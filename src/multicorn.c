/*
 * The Multicorn Foreign Data Wrapper allows you to fetch foreign data in
 * Python in your PostgreSQL server
 *
 * This software is released under the postgresql licence
 *
 */
#include "multicorn.h"
#include "optimizer/paths.h"
#include "optimizer/pathnode.h"
#include "optimizer/planmain.h"
#include "optimizer/restrictinfo.h"
#include "optimizer/clauses.h"
#include "optimizer/optimizer.h"
#include "optimizer/tlist.h"
#if PG_VERSION_NUM >= 140000
#include "optimizer/appendinfo.h"
#endif
#include "access/reloptions.h"
#include "access/relscan.h"
#include "access/sysattr.h"
#include "access/xact.h"
#include "nodes/makefuncs.h"
#include "catalog/pg_type.h"
#include "utils/memutils.h"
#include "miscadmin.h"
#include "utils/lsyscache.h"
#include "utils/rel.h"
#include "parser/parsetree.h"
#include "fmgr.h"
#include "port/atomics.h"

#if PG_VERSION_NUM >= 130000
#include "common/hashfn.h" /* oid_hash */
#endif


PG_MODULE_MAGIC;


extern Datum multicorn_handler(PG_FUNCTION_ARGS);
extern Datum multicorn_validator(PG_FUNCTION_ARGS);


PG_FUNCTION_INFO_V1(multicorn_handler);
PG_FUNCTION_INFO_V1(multicorn_validator);


void		_PG_init(void);
void		_PG_fini(void);

/*
 * FDW functions declarations
 */

static void multicornGetForeignRelSize(PlannerInfo *root,
                           RelOptInfo *baserel,
                           Oid foreigntableid);
static void multicornGetForeignPaths(PlannerInfo *root,
                         RelOptInfo *baserel,
                         Oid foreigntableid);
static ForeignScan *multicornGetForeignPlan(PlannerInfo *root,
                        RelOptInfo *baserel,
                        Oid foreigntableid,
                        ForeignPath *best_path,
                        List *tlist,
                        List *scan_clauses
                        , Plan *outer_plan
        );
static void multicornExplainForeignScan(ForeignScanState *node, ExplainState *es);
static void multicornBeginForeignScan(ForeignScanState *node, int eflags);
static TupleTableSlot *multicornIterateForeignScan(ForeignScanState *node);
static void multicornReScanForeignScan(ForeignScanState *node);
static void multicornEndForeignScan(ForeignScanState *node);

static void multicornAddForeignUpdateTargets(
#if PG_VERSION_NUM >= 140000
                                 PlannerInfo *root,
                                 Index rtindex,
#else
                                 Query *parsetree,
#endif
                                 RangeTblEntry *target_rte,
                                 Relation target_relation);

static List *multicornPlanForeignModify(PlannerInfo *root,
                           ModifyTable *plan,
                           Index resultRelation,
                           int subplan_index);
static void multicornBeginForeignModify(ModifyTableState *mtstate,
                            ResultRelInfo *resultRelInfo,
                            List *fdw_private,
                            int subplan_index,
                            int eflags);
static TupleTableSlot *multicornExecForeignInsert(EState *estate, ResultRelInfo *resultRelInfo,
                           TupleTableSlot *slot,
                           TupleTableSlot *planslot);
static TupleTableSlot *multicornExecForeignDelete(EState *estate, ResultRelInfo *resultRelInfo,
                           TupleTableSlot *slot, TupleTableSlot *planSlot);
static TupleTableSlot *multicornExecForeignUpdate(EState *estate, ResultRelInfo *resultRelInfo,
                           TupleTableSlot *slot, TupleTableSlot *planSlot);
static void multicornEndForeignModify(EState *estate, ResultRelInfo *resultRelInfo);

static void multicornGetForeignUpperPaths(PlannerInfo *root, UpperRelationKind stage,
						      RelOptInfo *input_rel, RelOptInfo *output_rel, void *extra
        );

#if PG_VERSION_NUM >= 140000
static TupleTableSlot **multicornExecForeignBatchInsert(EState *estate,
                            ResultRelInfo *rinfo,
                            TupleTableSlot **slots,
                            TupleTableSlot **planSlots,
                            int *numSlots);
static int multicornGetForeignModifyBatchSize(ResultRelInfo *rinfo);
#endif

static void multicorn_subxact_callback(SubXactEvent event, SubTransactionId mySubid,
                           SubTransactionId parentSubid, void *arg);

static List *multicornImportForeignSchema(ImportForeignSchemaStmt * stmt,
                             Oid serverOid);

static void multicorn_xact_callback(XactEvent event, void *arg);

/* Functions relating to aggregation/grouping pushdown */
static bool multicorn_foreign_grouping_ok(PlannerInfo *root, RelOptInfo *grouped_rel,
                                          Node *havingQual);
static void multicorn_add_foreign_grouping_paths(PlannerInfo *root,
											  RelOptInfo *input_rel,
											  RelOptInfo *grouped_rel,
											  GroupPathExtraData *extra
);

/*	Helpers functions */
void	   *serializePlanState(MulticornPlanState * planstate);
MulticornExecState *initializeExecState(void *internal_plan_state);

/* Hash table mapping oid to fdw instances */
HTAB	   *InstancesHash;

/* Global query counter */
static pg_atomic_uint64 global_query_counter;


void
_PG_init()
{
    HASHCTL		ctl;
    MemoryContext oldctx;
    bool need_import_plpy;

    /* Initialize the global query counter */
    pg_atomic_init_u64(&global_query_counter, 0);

    oldctx = MemoryContextSwitchTo(CacheMemoryContext);
    need_import_plpy = false;

    /* Try to load plpython3 with its own module */
    PG_TRY();
    {
    void * PyInit_plpy = load_external_function("plpython3", "PyInit_plpy", true, NULL);
    PyImport_AppendInittab("plpy", PyInit_plpy);
    need_import_plpy = true;
    }
    PG_CATCH();
    {
        need_import_plpy = false;
    }
    PG_END_TRY();
    Py_Initialize();
    if (need_import_plpy)
        PyImport_ImportModule("plpy");
    RegisterXactCallback(multicorn_xact_callback, NULL);
    RegisterSubXactCallback(multicorn_subxact_callback, NULL);
    /* Initialize the global oid -> python instances hash */
    MemSet(&ctl, 0, sizeof(ctl));
    ctl.keysize = sizeof(Oid);
    ctl.entrysize = sizeof(CacheEntry);
    ctl.hash = oid_hash;
    ctl.hcxt = CacheMemoryContext;
    InstancesHash = hash_create("multicorn instances", 32,
                                &ctl,
                                HASH_ELEM | HASH_FUNCTION);
    MemoryContextSwitchTo(oldctx);
}

void
_PG_fini()
{
    
    Py_Finalize();
}


Datum
multicorn_handler(PG_FUNCTION_ARGS)
{
    FdwRoutine *fdw_routine = makeNode(FdwRoutine);

    /* Plan phase */
    fdw_routine->GetForeignRelSize = multicornGetForeignRelSize;
    fdw_routine->GetForeignPaths = multicornGetForeignPaths;
    fdw_routine->GetForeignPlan = multicornGetForeignPlan;
    fdw_routine->ExplainForeignScan = multicornExplainForeignScan;

    /* Scan phase */
    fdw_routine->BeginForeignScan = multicornBeginForeignScan;
    fdw_routine->IterateForeignScan = multicornIterateForeignScan;
    fdw_routine->ReScanForeignScan = multicornReScanForeignScan;
    fdw_routine->EndForeignScan = multicornEndForeignScan;

    fdw_routine->AddForeignUpdateTargets = multicornAddForeignUpdateTargets;
    /* Writable API */
    fdw_routine->PlanForeignModify = multicornPlanForeignModify;
    fdw_routine->BeginForeignModify = multicornBeginForeignModify;
    fdw_routine->ExecForeignInsert = multicornExecForeignInsert;
    fdw_routine->ExecForeignDelete = multicornExecForeignDelete;
    fdw_routine->ExecForeignUpdate = multicornExecForeignUpdate;
    fdw_routine->EndForeignModify = multicornEndForeignModify;

#if PG_VERSION_NUM >= 140000
    fdw_routine->GetForeignModifyBatchSize = multicornGetForeignModifyBatchSize;
    fdw_routine->ExecForeignBatchInsert = multicornExecForeignBatchInsert;
#endif

    fdw_routine->ImportForeignSchema = multicornImportForeignSchema;

    /* Support functions for upper relation push-down */
	fdw_routine->GetForeignUpperPaths = multicornGetForeignUpperPaths;

    PG_RETURN_POINTER(fdw_routine);
}

Datum
multicorn_validator(PG_FUNCTION_ARGS)
{
    List	   *options_list = untransformRelOptions(PG_GETARG_DATUM(0));
    Oid			catalog = PG_GETARG_OID(1);
    char	   *className = NULL;
    ListCell   *cell;
    PyObject   *p_class;

    foreach(cell, options_list)
    {
        DefElem    *def = (DefElem *) lfirst(cell);

        if (strcmp(def->defname, "wrapper") == 0)
        {
            /* Only at server creation can we set the wrapper,	*/
            /* for security issues. */
            if (catalog == ForeignTableRelationId)
            {
                ereport(ERROR, (errmsg("%s", "Cannot set the wrapper class on the table"),
                                errhint("%s", "Set it on the server")));
            }
            else
            {
                className = (char *) defGetString(def);
            }
        }
    }
    if (catalog == ForeignServerRelationId)
    {
        if (className == NULL)
        {
            ereport(ERROR, (errmsg("%s", "The wrapper parameter is mandatory, specify a valid class name")));
        }
        /* Try to import the class. */
        p_class = getClassString(className);
        errorCheck();
        Py_DECREF(p_class);
    }
    PG_RETURN_VOID();
}


/*
 * multicornGetForeignRelSize
 *		Obtain relation size estimates for a foreign table.
 *		This is done by calling the
 */
static void
multicornGetForeignRelSize(PlannerInfo *root,
                           RelOptInfo *baserel,
                           Oid foreigntableid)
{
    MulticornPlanState *planstate = palloc0(sizeof(MulticornPlanState));
    ForeignTable *ftable = GetForeignTable(foreigntableid);
    ListCell   *lc;
    bool		needWholeRow = false;
    TupleDesc	desc;

    baserel->fdw_private = planstate;

    /* Base foreign tables need to be push down always */
	planstate->pushdown_safe = true;

    /* Initialize upperrel pushdown info */
    planstate->groupby_supported = false;
    planstate->agg_functions = NULL;

    planstate->fdw_instance = getInstance(foreigntableid);
    planstate->foreigntableid = foreigntableid;
    
    elog(WARNING, "1");

    /* Set the LIMIT clause if passed */
    if (root->limit_tuples > 0) {
        planstate->limit = root->limit_tuples;
    } else {
        planstate->limit = -1; // No LIMIT clause
    }

    elog(WARNING, "2");

    /* Set the unique plan identifier */
    planstate->plan_id = pg_atomic_fetch_add_u64(&global_query_counter, 1);
    /* Initialize the conversion info array */
    {
        Relation	rel = RelationIdGetRelation(ftable->relid);
        AttInMetadata *attinmeta;

        desc = RelationGetDescr(rel);
        attinmeta = TupleDescGetAttInMetadata(desc);
        planstate->numattrs = RelationGetNumberOfAttributes(rel);

        planstate->cinfos = palloc0(sizeof(ConversionInfo *) *
                                    planstate->numattrs);
        initConversioninfo(planstate->cinfos, attinmeta, NULL);
        needWholeRow = rel->trigdesc && rel->trigdesc->trig_insert_after_row;
        RelationClose(rel);
    }

    elog(WARNING, "3");

    if (needWholeRow)
    {
        int			i;

        for (i = 0; i < desc->natts; i++)
        {
            Form_pg_attribute att = TupleDescAttr(desc, i);

            if (!att->attisdropped)
            {
                planstate->target_list = lappend(planstate->target_list, makeString(NameStr(att->attname)));
            }
        }
    }
    else
    {
        /* Pull "var" clauses to build an appropriate target list */
        foreach(lc, extractColumns(baserel->reltarget->exprs, baserel->baserestrictinfo))
        {
            Var		   *var = (Var *) lfirst(lc);
#if PG_VERSION_NUM < 150000
            Value	   *colname;
#else
            String	   *colname;
#endif

            /*
             * Store only a Value node containing the string name of the
             * column.
             */
            colname = colnameFromVar(var, root, planstate);
            if (colname != NULL && strVal(colname) != NULL)
            {
                planstate->target_list = lappend(planstate->target_list, colname);
            }
        }
    }

    elog(WARNING, "4");

    /* Extract the restrictions from the plan. */
    foreach(lc, baserel->baserestrictinfo)
    {
        extractRestrictions(
#if PG_VERSION_NUM >= 140000
            root,
#endif
            baserel->relids,
            ((RestrictInfo *) lfirst(lc))->clause,
            &planstate->qual_list);

    }

    elog(WARNING, "5xx");

    /* Inject the "rows" and "width" attribute into the baserel */
    getRelSize(planstate, root, &baserel->rows, &baserel->reltarget->width);

    elog(WARNING, "6");

    planstate->width = baserel->reltarget->width;
}

/*
 * multicornGetForeignPaths
 *		Create possible access paths for a scan on the foreign table.
 *		This is done by calling the "get_path_keys method on the python side,
 *		and parsing its result to build parameterized paths according to the
 *		equivalence classes found in the plan.
 */
static void
multicornGetForeignPaths(PlannerInfo *root,
                         RelOptInfo *baserel,
                         Oid foreigntableid)
{
    List				*pathes; /* List of ForeignPath */
    MulticornPlanState	*planstate = baserel->fdw_private;
    ListCell		    *lc;

    elog(WARNING, "c1");

    /* These lists are used to handle sort pushdown */
    List				*apply_pathkeys = NULL;
    List				*deparsed_pathkeys = NULL;

    /* Extract a friendly version of the pathkeys. */
    List	   *possiblePaths = pathKeys(planstate);

    /* Try to find parameterized paths */
    pathes = findPaths(root, baserel, possiblePaths, planstate->startupCost,
            planstate, apply_pathkeys, deparsed_pathkeys);

    /* Add a simple default path */
    pathes = lappend(pathes, create_foreignscan_path(root, baserel,
             NULL,  /* default pathtarget */
            baserel->rows,
            planstate->startupCost,
            baserel->rows * baserel->reltarget->width,
            NIL,		/* no pathkeys */
            NULL,
            NULL,
#if PG_VERSION_NUM >= 170000
            NULL,
#endif
            NULL));

    /* Handle sort pushdown */
    if (root->query_pathkeys)
    {
        List		*deparsed = deparse_sortgroup(root, foreigntableid, baserel);

        if (deparsed)
        {
            /* Update the sort_*_pathkeys lists if needed */
            computeDeparsedSortGroup(deparsed, planstate, &apply_pathkeys,
                    &deparsed_pathkeys);
        }
    }

    elog(WARNING, "c2");

    /* Add each ForeignPath previously found */
    foreach(lc, pathes)
    {
        ForeignPath *path = (ForeignPath *) lfirst(lc);

        /* Add the path without modification */
        add_path(baserel, (Path *) path);

        /* Add the path with sort pusdown if possible */
        if (apply_pathkeys && deparsed_pathkeys)
        {
            ForeignPath *newpath;

            newpath = create_foreignscan_path(root, baserel,
                    NULL,  /* default pathtarget */
                    path->path.rows,
                    path->path.startup_cost, path->path.total_cost,
                    apply_pathkeys, NULL,
                    NULL,
#if PG_VERSION_NUM >= 170000
                    NULL,
#endif
                    (void *) deparsed_pathkeys);

            newpath->path.param_info = path->path.param_info;
            add_path(baserel, (Path *) newpath);
        }
    }
    errorCheck();
}

/*
 * multicornGetForeignPlan
 *		Create a ForeignScan plan node for scanning the foreign table
 */
static ForeignScan *
multicornGetForeignPlan(PlannerInfo *root,
                        RelOptInfo *foreignrel,
                        Oid foreigntableid,
                        ForeignPath *best_path,
                        List *tlist,
                        List *scan_clauses
                        , Plan *outer_plan
        )
{
    MulticornPlanState *ofpinfo, *planstate = (MulticornPlanState *) foreignrel->fdw_private;
    Index		scan_relid;
    ListCell   *lc;
    List	   *fdw_scan_tlist = NIL;

    elog(WARNING, "a1");

    if (IS_SIMPLE_REL(foreignrel))
	{
		/*
		 * For base relations, set scan_relid as the relid of the relation.
		 */
		scan_relid = foreignrel->relid;
	}
	else
	{
		/*
		 * Join relation or upper relation - set scan_relid to 0.
		 */
		scan_relid = 0;

		/*
		 * For a join rel, baserestrictinfo is NIL and we are not considering
		 * parameterization right now, so there should be no scan_clauses for
		 * a joinrel or an upper rel either.
		 */
		Assert(!scan_clauses);

		/* Build the list of columns to be fetched from the foreign server. */
		fdw_scan_tlist = multicorn_build_tlist_to_deparse(foreignrel);
	}

    best_path->path.pathtarget->width = planstate->width;
    planstate->pathkeys = (List *) best_path->fdw_private;

    scan_clauses = extract_actual_clauses(scan_clauses, false);
    /* Extract the quals coming from a parameterized path, if any */
    if (best_path->path.param_info)
    {

        foreach(lc, scan_clauses)
        {
            extractRestrictions(
#if PG_VERSION_NUM >= 140000
                root,
#endif
                foreignrel->relids,
                (Expr *) lfirst(lc),
                &planstate->qual_list);
        }
    }

    /* Extract data needed for aggregations on the Python side */
    if (IS_UPPER_REL(foreignrel))
    {
        /*
         * TODO: fdw_scan_tlist is present in the execute phase as well, via
         * node->ss.ps.plan.fdw_scan_tlist, and instead of root, one can employ
         * rte = exec_rt_fetch(rtindex, estate) to fetch the column name through
         * get_attname.
         *
         * Migrating the below function into multicornBeginForeignScan would thus
         * reduce the duplication of plan and execute fields that are now being
         * serialized.
         */
        multicorn_extract_upper_rel_info(root, fdw_scan_tlist, planstate);

        /*
         * Since scan_clauses are empty in case of upper relations for some
         * reason. We pass the clauses from the base relation obtained in MulticornGetForeignRelSize.
         */
        ofpinfo = (MulticornPlanState *) planstate->outerrel->fdw_private;
        planstate->baserestrictinfo = extract_actual_clauses(ofpinfo->baserestrictinfo, false);

        /*
         * In case of a join or aggregate use the lowest-numbered member RTE out
         * of all all the base relations participating in the underlying scan.
         *
         * NB: This may not work well in case of joins, keep an eye out for it.
         * We extract it here because fs_relids in execution phase can get distorted
         * in case of joins + agg combos.
         */
        planstate->rtindex = makeInteger(bms_next_member(root->all_baserels, -1));
    }

    elog(WARNING, "a2");

    return make_foreignscan(tlist,
                            scan_clauses,
                            scan_relid,
                            scan_clauses,		/* no expressions to evaluate */
                            serializePlanState(planstate)
                            , fdw_scan_tlist
                            , NULL /* All quals are meant to be rechecked */
                            , outer_plan
                            );
}

/*
 * multicornExplainForeignScan
 *		Placeholder for additional "EXPLAIN" information.
 *		This should (at least) output the python class name, as well
 *		as information that was taken into account for the choice of a path.
 */
static void
multicornExplainForeignScan(ForeignScanState *node, ExplainState *es)
{
    PyObject *p_iterable = execute(node, es),
             *p_item,
             *p_str;
    Py_INCREF(p_iterable);
    while((p_item = PyIter_Next(p_iterable))){
        p_str = PyObject_Str(p_item);
        ExplainPropertyText("Multicorn", PyString_AsString(p_str), es);
        Py_DECREF(p_str);
    }
    Py_DECREF(p_iterable);
    errorCheck();
}

/*
 *	multicornBeginForeignScan
 *		Initialize the foreign scan.
 *		This (primarily) involves :
 *			- retrieving cached info from the plan phase
 *			- initializing various buffers
 */
static void
multicornBeginForeignScan(ForeignScanState *node, int eflags)
{
    ForeignScan *fscan = (ForeignScan *) node->ss.ps.plan;
    MulticornExecState *execstate;
    ListCell   *lc;
    int rtindex;
    List *clauses;

    elog(DEBUG3, "starting BeginForeignScan()");

    execstate = initializeExecState(fscan->fdw_private);

    /*
	 * Get info we'll need for converting data fetched from the foreign server
	 * into local representation and error reporting during that process.
	 */
	if (fscan->scan.scanrelid > 0)
	{
        /*
         * Simple/base relation
         */

		execstate->rel = node->ss.ss_currentRelation;
		execstate->tupdesc = RelationGetDescr(execstate->rel);
        initConversioninfo(execstate->cinfos, TupleDescGetAttInMetadata(execstate->tupdesc), NULL);

        // Needed for parsing quals
        rtindex = fscan->scan.scanrelid;
        clauses = fscan->fdw_exprs;
	}
	else
	{
        /*
         * Upper (aggregation) relation
         */

		execstate->rel = NULL;
//#if (PG_VERSION_NUM >= 140000)
//		execstate->tupdesc = multicorn_get_tupdesc_for_join_scan_tuples(node);
//#else
		execstate->tupdesc = node->ss.ss_ScanTupleSlot->tts_tupleDescriptor;
//#endif
        initConversioninfo(execstate->cinfos, TupleDescGetAttInMetadata(execstate->tupdesc), execstate->upper_rel_targets);

        // Needed for parsing quals
        rtindex = intVal(execstate->rtindex);
        clauses = execstate->baserestrictinfo;
	}

    execstate->values = palloc(sizeof(Datum) * execstate->tupdesc->natts);
	execstate->nulls = palloc(sizeof(bool) * execstate->tupdesc->natts);
    execstate->qual_list = NULL;
    foreach(lc, clauses)
    {
        elog(DEBUG3, "looping in beginForeignScan()");
        extractRestrictions(
#if PG_VERSION_NUM >= 140000
NULL,
#endif
bms_make_singleton(rtindex),
                            ((Expr *) lfirst(lc)),
                            &execstate->qual_list);
    }
    node->fdw_state = execstate;
}


/*
 * multicornIterateForeignScan
 *		Retrieve next row from the result set, or clear tuple slot to indicate
 *		EOF.
 *
 *		This is done by iterating over the result from the "execute" python
 *		method.
 */
static TupleTableSlot *
multicornIterateForeignScan(ForeignScanState *node)
{
    TupleTableSlot *slot = node->ss.ss_ScanTupleSlot;
    MulticornExecState *execstate = node->fdw_state;
    PyObject   *p_value;

    if (execstate->p_iterator == NULL)
    {
        execute(node, NULL);
    }
    ExecClearTuple(slot);
    if (execstate->p_iterator == Py_None)
    {
        /* No iterator returned from get_iterator */
        Py_DECREF(execstate->p_iterator);
        return slot;
    }
    p_value = PyIter_Next(execstate->p_iterator);
    errorCheck();
    /* A none value results in an empty slot. */
    if (p_value == NULL || p_value == Py_None)
    {
        Py_XDECREF(p_value);
        return slot;
    }
    slot->tts_values = execstate->values;
    slot->tts_isnull = execstate->nulls;
    pythonResultToTuple(p_value, slot, execstate->cinfos, execstate->buffer);
    ExecStoreVirtualTuple(slot);
    Py_DECREF(p_value);

    return slot;
}

/*
 * multicornReScanForeignScan
 *		Restart the scan
 */
static void
multicornReScanForeignScan(ForeignScanState *node)
{
    MulticornExecState *state = node->fdw_state;

    if (state->p_iterator)
    {
        Py_DECREF(state->p_iterator);
        state->p_iterator = NULL;
    }
}

/*
 *	multicornEndForeignScan
 *		Finish scanning foreign table and dispose objects used for this scan.
 */
static void
multicornEndForeignScan(ForeignScanState *node)
{
    MulticornExecState *state = node->fdw_state;
    PyObject   *result = PyObject_CallMethod(state->fdw_instance, "end_scan", "()");

    errorCheck();
    Py_DECREF(result);
    Py_DECREF(state->fdw_instance);
    Py_XDECREF(state->p_iterator);
    state->p_iterator = NULL;
}



/*
 * multicornAddForeigUpdateTargets
 *		Add resjunk columns needed for update/delete.
 */
static void
multicornAddForeignUpdateTargets(
#if PG_VERSION_NUM >= 140000
                                 PlannerInfo *root,
                                 Index rtindex,
#else
                                 Query *parsetree,
#endif
                                 RangeTblEntry *target_rte,
                                 Relation target_relation)
{
    Var		   *var = NULL;
    TargetEntry *tle,
               *returningTle;
    PyObject   *instance = getInstance(target_relation->rd_id);
    const char *attrname = getRowIdColumn(instance);
    TupleDesc	desc = target_relation->rd_att;
    int			i;
    ListCell   *cell;
#if PG_VERSION_NUM >= 140000
    Query *parsetree = root->parse;
#endif

#if PG_VERSION_NUM >= 140000
    if (root->parse->commandType == CMD_UPDATE)
    {
        // In order to maintain backward compatibility with behavior prior to PG14, during an UPDATE we ensure that we
        // fetch all columns from the table to provide them to the `update()` method.  This could be made more efficient
        // in the future if multicornExecForeignUpdate() was modified to call `update()` with only the columns that have
        // been changed, but it might be a compatibility problem for existing FDWs.

        for (i = 0; i < desc->natts; i++)
        {
            Form_pg_attribute att = TupleDescAttr(desc, i);

            if (!att->attisdropped)
            {
                var = makeVar(rtindex,
                            att->attnum,
                            att->atttypid,
                            att->atttypmod,
                            att->attcollation,
                            0);
                add_row_identity_var(root, var, rtindex, strdup(NameStr(att->attname)));
            }
        }

        return;
    }
#endif

    foreach(cell, parsetree->returningList)
    {
        returningTle = lfirst(cell);
        tle = copyObject(returningTle);
        tle->resjunk = true;
#if PG_VERSION_NUM >= 140000
        add_row_identity_var(root, (Var *)tle->expr, rtindex, strdup(tle->resname));
#else
        parsetree->targetList = lappend(parsetree->targetList, tle);
#endif
    }


    for (i = 0; i < desc->natts; i++)
    {
        Form_pg_attribute att = TupleDescAttr(desc, i);

        if (!att->attisdropped)
        {
            if (strcmp(NameStr(att->attname), attrname) == 0)
            {
                var = makeVar(parsetree->resultRelation,
                              att->attnum,
                              att->atttypid,
                              att->atttypmod,
                              att->attcollation,
                              0);
                break;
            }
        }
    }
    if (var == NULL)
    {
        ereport(ERROR, (errmsg("%s", "The rowid attribute does not exist")));
    }

#if PG_VERSION_NUM >= 140000
    add_row_identity_var(root, var, parsetree->resultRelation, strdup(attrname));
#else
    tle = makeTargetEntry((Expr *) var,
                          list_length(parsetree->targetList) + 1,
                          strdup(attrname),
                          true);
    parsetree->targetList = lappend(parsetree->targetList, tle);
#endif

    Py_DECREF(instance);
}


/*
 * multicornPlanForeignModify
 *		Plan a foreign write operation.
 *		This is done by checking the "supported operations" attribute
 *		on the python class.
 */
static List *
multicornPlanForeignModify(PlannerInfo *root,
                           ModifyTable *plan,
                           Index resultRelation,
                           int subplan_index)
{
    return NULL;
}


/*
 * multicornBeginForeignModify
 *		Initialize a foreign write operation.
 */
static void
multicornBeginForeignModify(ModifyTableState *mtstate,
                            ResultRelInfo *resultRelInfo,
                            List *fdw_private,
                            int subplan_index,
                            int eflags)
{
    MulticornModifyState *modstate = palloc0(sizeof(MulticornModifyState));
    Relation	rel = resultRelInfo->ri_RelationDesc;
    TupleDesc	desc = RelationGetDescr(rel);
    PlanState  *ps =
#if PG_VERSION_NUM >= 140000
        outerPlanState(mtstate);
#else
        mtstate->mt_plans[subplan_index];
#endif
    Plan	   *subplan = ps->plan;
    MemoryContext oldcontext;
    int			i;

    modstate->cinfos = palloc0(sizeof(ConversionInfo *) *
                               desc->natts);
    modstate->buffer = makeStringInfo();
    modstate->fdw_instance = getInstance(rel->rd_id);
    modstate->rowidAttrName = getRowIdColumn(modstate->fdw_instance);
    initConversioninfo(modstate->cinfos, TupleDescGetAttInMetadata(desc), NULL);
    oldcontext = MemoryContextSwitchTo(TopMemoryContext);
    MemoryContextSwitchTo(oldcontext);
    if (ps->ps_ResultTupleSlot)
    {
        TupleDesc	resultTupleDesc = ps->ps_ResultTupleSlot->tts_tupleDescriptor;

        modstate->resultCinfos = palloc0(sizeof(ConversionInfo *) *
                                         resultTupleDesc->natts);
        initConversioninfo(modstate->resultCinfos, TupleDescGetAttInMetadata(resultTupleDesc), NULL);
    }
    for (i = 0; i < desc->natts; i++)
    {
        Form_pg_attribute att = TupleDescAttr(desc, i);

        if (!att->attisdropped)
        {
            if (strcmp(NameStr(att->attname), modstate->rowidAttrName) == 0)
            {
                modstate->rowidCinfo = modstate->cinfos[i];
                break;
            }
        }
    }
    modstate->rowidAttno = ExecFindJunkAttributeInTlist(subplan->targetlist, modstate->rowidAttrName);
    resultRelInfo->ri_FdwState = modstate;
}

/*
 * multicornExecForeignInsert
 *		Execute a foreign insert operation
 *		This is done by calling the python "insert" method.
 */
static TupleTableSlot *
multicornExecForeignInsert(EState *estate, ResultRelInfo *resultRelInfo,
                           TupleTableSlot *slot, TupleTableSlot *planSlot)
{
    MulticornModifyState *modstate = resultRelInfo->ri_FdwState;
    PyObject   *fdw_instance = modstate->fdw_instance;
    PyObject   *values = tupleTableSlotToPyObject(slot, modstate->cinfos);
    PyObject   *p_new_value = PyObject_CallMethod(fdw_instance, "insert", "(O)", values);

    errorCheck();
    if (p_new_value && p_new_value != Py_None)
    {
        ExecClearTuple(slot);
        pythonResultToTuple(p_new_value, slot, modstate->cinfos, modstate->buffer);
        ExecStoreVirtualTuple(slot);
    }
    Py_XDECREF(p_new_value);
    Py_DECREF(values);
    errorCheck();
    return slot;
}

/*
 * multicornExecForeignDelete
 *		Execute a foreign delete operation
 *		This is done by calling the python "delete" method, with the opaque
 *		rowid that was supplied.
 */
static TupleTableSlot *
multicornExecForeignDelete(EState *estate, ResultRelInfo *resultRelInfo,
                           TupleTableSlot *slot, TupleTableSlot *planSlot)
{
    MulticornModifyState *modstate = resultRelInfo->ri_FdwState;
    PyObject   *fdw_instance = modstate->fdw_instance,
               *p_row_id,
               *p_new_value;
    bool		is_null;
    ConversionInfo *cinfo = modstate->rowidCinfo;
    Datum		value = ExecGetJunkAttribute(planSlot, modstate->rowidAttno, &is_null);

    if (modstate->rowidAttno == InvalidAttrNumber)
    {
        ereport(ERROR, (errmsg("%s", "The rowid_column could not be identified")));
    }

    p_row_id = datumToPython(value, cinfo->atttypoid, cinfo);
    p_new_value = PyObject_CallMethod(fdw_instance, "delete", "(O)", p_row_id);
    errorCheck();
    if (p_new_value == NULL || p_new_value == Py_None)
    {
        Py_XDECREF(p_new_value);
        p_new_value = tupleTableSlotToPyObject(planSlot, modstate->resultCinfos);
    }
    ExecClearTuple(slot);
    pythonResultToTuple(p_new_value, slot, modstate->cinfos, modstate->buffer);
    ExecStoreVirtualTuple(slot);
    Py_DECREF(p_new_value);
    Py_DECREF(p_row_id);
    errorCheck();
    return slot;
}

#if PG_VERSION_NUM >= 140000

static TupleTableSlot **multicornExecForeignBatchInsert(EState *estate,
                                                        ResultRelInfo *rinfo,
                                                        TupleTableSlot **slots,
                                                        TupleTableSlot **planSlots,
                                                        int *numSlots)
{
    MulticornModifyState *modstate = rinfo->ri_FdwState;
    PyObject *fdw_instance = modstate->fdw_instance;
    PyObject *py_slots_list = PyList_New(0);  // Create a new list for all slot values
    PyObject *p_return_values;
    int i;

    // Convert all TupleTableSlots to Python objects and append to list
    for (i = 0; i < *numSlots; i++) {
        PyObject *values = tupleTableSlotToPyObject(slots[i], modstate->cinfos);
        errorCheck();
        if (values == NULL) {
            Py_DECREF(py_slots_list);
            return slots;  // Early exit on conversion failure
        }
        PyList_Append(py_slots_list, values);
        errorCheck();
        Py_DECREF(values);  // Decrement refcount after adding to list
    }

    p_return_values = PyObject_CallMethod(fdw_instance, "bulk_insert", "(O)", py_slots_list);
    errorCheck();

    // Process returned values if any
    if (p_return_values && p_return_values != Py_None) {
        if (PyList_Check(p_return_values) && PyList_Size(p_return_values) == *numSlots) {
            for (i = 0; i < *numSlots; i++) {
                PyObject *p_new_value = PyList_GetItem(p_return_values, i);  // Borrowed reference, no need to DECREF
                errorCheck();

                ExecClearTuple(slots[i]);
                pythonResultToTuple(p_new_value, slots[i], modstate->cinfos, modstate->buffer);
                errorCheck();

                ExecStoreVirtualTuple(slots[i]);
            }
        } else {
            // Error: return values do not match the number of slots provided
            ereport(ERROR, (errmsg("%s", "Returned list size does not match number of inserted values")));
        }
    }

    Py_XDECREF(p_return_values);
    Py_DECREF(py_slots_list);

    return slots;
}

static int multicornGetForeignModifyBatchSize(ResultRelInfo *rinfo)
{
    MulticornModifyState *modstate = rinfo->ri_FdwState;
    PyObject *fdw_instance = modstate->fdw_instance;
    int batch_size = getModifyBatchSize(fdw_instance);
    return batch_size;
}

#endif

/*
 * multicornExecForeignUpdate
 *		Execute a foreign update operation
 *		This is done by calling the python "update" method, with the opaque
 *		rowid that was supplied.
 */
static TupleTableSlot *
multicornExecForeignUpdate(EState *estate, ResultRelInfo *resultRelInfo,
                           TupleTableSlot *slot, TupleTableSlot *planSlot)
{
    MulticornModifyState *modstate = resultRelInfo->ri_FdwState;
    PyObject   *fdw_instance = modstate->fdw_instance,
               *p_row_id,
               *p_new_value,
               *p_value = tupleTableSlotToPyObject(slot, modstate->cinfos);
    bool		is_null;
    ConversionInfo *cinfo = modstate->rowidCinfo;
    Datum		value = ExecGetJunkAttribute(planSlot, modstate->rowidAttno, &is_null);

    if (modstate->rowidAttno == InvalidAttrNumber)
    {
        ereport(ERROR, (errmsg("%s", "The rowid_column could not be identified")));
    }

    p_row_id = datumToPython(value, cinfo->atttypoid, cinfo);
    p_new_value = PyObject_CallMethod(fdw_instance, "update", "(O,O)", p_row_id,
                                      p_value);
    errorCheck();
    if (p_new_value != NULL && p_new_value != Py_None)
    {
        ExecClearTuple(slot);
        pythonResultToTuple(p_new_value, slot, modstate->cinfos, modstate->buffer);
        ExecStoreVirtualTuple(slot);
    }
    Py_XDECREF(p_new_value);
    Py_DECREF(p_row_id);
    errorCheck();
    return slot;
}

/*
 * multicornEndForeignModify
 *		Clean internal state after a modify operation.
 */
static void
multicornEndForeignModify(EState *estate, ResultRelInfo *resultRelInfo)

{
    MulticornModifyState *modstate = resultRelInfo->ri_FdwState;
    PyObject   *result = PyObject_CallMethod(modstate->fdw_instance, "end_modify", "()");

    errorCheck();
    Py_DECREF(modstate->fdw_instance);
    Py_DECREF(result);
}

/*
 * Callback used to propagate a subtransaction end.
 */
static void
multicorn_subxact_callback(SubXactEvent event, SubTransactionId mySubid,
                           SubTransactionId parentSubid, void *arg)
{
    PyObject   *instance;
    int			curlevel;
    HASH_SEQ_STATUS status;
    CacheEntry *entry;

    /* Nothing to do after commit or subtransaction start. */
    if (event == SUBXACT_EVENT_COMMIT_SUB || event == SUBXACT_EVENT_START_SUB)
        return;

    curlevel = GetCurrentTransactionNestLevel();

    hash_seq_init(&status, InstancesHash);

    while ((entry = (CacheEntry *) hash_seq_search(&status)) != NULL)
    {
        if (entry->xact_depth < curlevel)
            continue;

        instance = entry->value;
        if (event == SUBXACT_EVENT_PRE_COMMIT_SUB)
        {
            PyObject_CallMethod(instance, "sub_commit", "(i)", curlevel);
        }
        else
        {
            PyObject_CallMethod(instance, "sub_rollback", "(i)", curlevel);
        }
        errorCheck();
        entry->xact_depth--;
    }
}

/*
 * Callback used to propagate pre-commit / commit / rollback.
 */
static void
multicorn_xact_callback(XactEvent event, void *arg)
{
    PyObject   *instance;
    HASH_SEQ_STATUS status;
    CacheEntry *entry;

    hash_seq_init(&status, InstancesHash);
    while ((entry = (CacheEntry *) hash_seq_search(&status)) != NULL)
    {
        instance = entry->value;
        if (entry->xact_depth == 0)
            continue;

        switch (event)
        {
            case XACT_EVENT_PRE_COMMIT:
                PyObject_CallMethod(instance, "pre_commit", "()");
                break;
            case XACT_EVENT_COMMIT:
                PyObject_CallMethod(instance, "commit", "()");
                entry->xact_depth = 0;
                break;
            case XACT_EVENT_ABORT:
                PyObject_CallMethod(instance, "rollback", "()");
                entry->xact_depth = 0;
                break;
            default:
                break;
        }
        errorCheck();
    }
}

static List *
multicornImportForeignSchema(ImportForeignSchemaStmt * stmt,
                             Oid serverOid)
{
    List	   *cmds = NULL;
    List	   *options = NULL;
    UserMapping *mapping;
    ForeignServer *f_server;
    char	   *restrict_type = NULL;
    PyObject   *p_class = NULL;
    PyObject   *p_tables,
               *p_srv_options,
               *p_options,
               *p_restrict_list,
               *p_iter,
               *p_item;
    ListCell   *lc;

    f_server = GetForeignServer(serverOid);
    foreach(lc, f_server->options)
    {
        DefElem    *option = (DefElem *) lfirst(lc);

        if (strcmp(option->defname, "wrapper") == 0)
        {
            p_class = getClassString(defGetString(option));
            errorCheck();
        }
        else
        {
            options = lappend(options, option);
        }
    }
    mapping = multicorn_GetUserMapping(GetUserId(), serverOid);
    if (mapping)
        options = list_concat(options, mapping->options);

    if (p_class == NULL)
    {
        /*
         * This should never happen, since we validate the wrapper parameter
         * at
         */
        /* object creation time. */
        ereport(ERROR, (errmsg("%s", "The wrapper parameter is mandatory, specify a valid class name")));
    }
    switch (stmt->list_type)
    {
        case FDW_IMPORT_SCHEMA_LIMIT_TO:
            restrict_type = "limit";
            break;
        case FDW_IMPORT_SCHEMA_EXCEPT:
            restrict_type = "except";
            break;
        case FDW_IMPORT_SCHEMA_ALL:
            break;
    }
    p_srv_options = optionsListToPyDict(options);
    p_options = optionsListToPyDict(stmt->options);
    p_restrict_list = PyList_New(0);
    foreach(lc, stmt->table_list)
    {
        RangeVar   *rv = (RangeVar *) lfirst(lc);
        PyObject   *p_tablename = PyUnicode_Decode(
                                            rv->relname, strlen(rv->relname),
                                                   getPythonEncodingName(),
                                                   NULL);

        errorCheck();
        PyList_Append(p_restrict_list, p_tablename);
        Py_DECREF(p_tablename);
    }
    errorCheck();
    p_tables = PyObject_CallMethod(p_class, "import_schema", "(s, O, O, s, O)",
                               stmt->remote_schema, p_srv_options, p_options,
                                   restrict_type, p_restrict_list);
    errorCheck();
    Py_DECREF(p_class);
    Py_DECREF(p_options);
    Py_DECREF(p_srv_options);
    Py_DECREF(p_restrict_list);
    errorCheck();
    p_iter = PyObject_GetIter(p_tables);
    while ((p_item = PyIter_Next(p_iter)))
    {
        PyObject   *p_string;
        char	   *value;

        p_string = PyObject_CallMethod(p_item, "to_statement", "(s,s)",
                                   stmt->local_schema, f_server->servername);
        errorCheck();
        value = PyString_AsString(p_string);
        errorCheck();
        cmds = lappend(cmds, pstrdup(value));
        Py_DECREF(p_string);
        Py_DECREF(p_item);
    }
    errorCheck();
    Py_DECREF(p_iter);
    Py_DECREF(p_tables);
    return cmds;
}


/*
 * Merge FDW options from input relations into a new set of options for a join
 * or an upper rel.
 *
 * For a join relation, FDW-specific information about the inner and outer
 * relations is provided using fpinfo_i and fpinfo_o.  For an upper relation,
 * fpinfo_o provides the information for the input relation; fpinfo_i is
 * expected to NULL.
 */
static void
multicorn_merge_fdw_options(MulticornPlanState *fpinfo,
				  const MulticornPlanState *fpinfo_o,
				  const MulticornPlanState *fpinfo_i)
{
	/* We must always have fpinfo_o. */
	Assert(fpinfo_o);

	/* fpinfo_i may be NULL, but if present the servers must both match. */
	Assert(!fpinfo_i ||
		   fpinfo_i->server->serverid == fpinfo_o->server->serverid);

	/*
	 * Copy the server specific FDW options.  (For a join, both relations come
	 * from the same server, so the server options should have the same value
	 * for both relations.)
	 */
	fpinfo->fdw_startup_cost = fpinfo_o->fdw_startup_cost;
	fpinfo->fdw_tuple_cost = fpinfo_o->fdw_tuple_cost;
	fpinfo->shippable_extensions = fpinfo_o->shippable_extensions;
	fpinfo->use_remote_estimate = fpinfo_o->use_remote_estimate;
	fpinfo->fetch_size = fpinfo_o->fetch_size;

    /* Multicorn specific options, differing from othe FDW implementations */
    fpinfo->fdw_instance = fpinfo_o->fdw_instance;
    fpinfo->foreigntableid = fpinfo_o->foreigntableid;
	fpinfo->numattrs = fpinfo_o->numattrs;
    fpinfo->cinfos = fpinfo_o->cinfos;
    fpinfo->pathkeys = fpinfo_o->pathkeys;
    fpinfo->target_list = fpinfo_o->target_list;
    fpinfo->qual_list = fpinfo_o->qual_list;
    fpinfo->pathkeys = fpinfo_o->pathkeys;

	/* Merge the table level options from either side of the join. */
	if (fpinfo_i)
	{
		/*
		 * We'll prefer to use remote estimates for this join if any table
		 * from either side of the join is using remote estimates.  This is
		 * most likely going to be preferred since they're already willing to
		 * pay the price of a round trip to get the remote EXPLAIN.  In any
		 * case it's not entirely clear how we might otherwise handle this
		 * best.
		 */
		fpinfo->use_remote_estimate = fpinfo_o->use_remote_estimate ||
			fpinfo_i->use_remote_estimate;

		/*
		 * Set fetch size to maximum of the joining sides, since we are
		 * expecting the rows returned by the join to be proportional to the
		 * relation sizes.
		 */
		fpinfo->fetch_size = Max(fpinfo_o->fetch_size, fpinfo_i->fetch_size);
	}
}

/*
 * Assess whether the aggregation, grouping and having operations can be pushed
 * down to the foreign server.  As a side effect, save information we obtain in
 * this function to MulticornPlanState of the input relation.
 */
static bool
multicorn_foreign_grouping_ok(PlannerInfo *root, RelOptInfo *grouped_rel,
                              Node *havingQual)
{
	Query	   *query = root->parse;
	MulticornPlanState *fpinfo = (MulticornPlanState *) grouped_rel->fdw_private;
    PathTarget *grouping_target = grouped_rel->reltarget;
    // Q: Or perhaps like in SQLite FDW `PathTarget *grouping_target = root->upper_targets[UPPERREL_GROUP_AGG];`?
    // A: It appears they are the same thing; see also GridDBs sortgrouprefs explanation
	MulticornPlanState *ofpinfo;
	ListCell   *lc;
	int			i;
	List	   *tlist = NIL;

	/* We currently don't support pushing Grouping Sets. */
	if (query->groupingSets) {
        elog(WARNING, "xxx0");
		return false;
    }

	/* Get the fpinfo of the underlying scan relation. */
	ofpinfo = (MulticornPlanState *) fpinfo->outerrel->fdw_private;

    /*
	 * If underlying scan relation has more quals than we are attempting to push
     * down, this means that some are missing in qual_list, hence the aggregation
     * wouldn't be correct. Examples includes using a float value in a WHERE clause
     * against a column of integer type.
     * NB: If we ever decide to add support for join-agg pushdown this won't work.
	 */
    if (list_length(ofpinfo->qual_list) < list_length(fpinfo->outerrel->baserestrictinfo))
    {
        elog(WARNING, "xxx1");
        return false;
    }

	/*
	 * If underlying scan relation has any quals with unsupported operators
     * we cannot pushdown the aggregation.
	 */
    foreach(lc, ofpinfo->qual_list)
    {
        MulticornBaseQual *qual = (MulticornBaseQual *) lfirst(lc);

        if (!list_member(ofpinfo->operators_supported, makeString(qual->opname))) {
            elog(WARNING, "xxx2");
            return false;
        }
    }

    /*
	 * Examine grouping expressions, as well as other expressions we'd need to
	 * compute, and check whether they are safe to push down to the foreign
	 * server.  All GROUP BY expressions will be part of the grouping target
	 * and thus there is no need to search for them separately.  Add grouping
	 * expressions into target list which will be passed to foreign server.
     *
     * A tricky fine point is that we must not put any expression into the
	 * target list that is just a foreign param (that is, something that
	 * deparse.c would conclude has to be sent to the foreign server).  If we
	 * do, the expression will also appear in the fdw_exprs list of the plan
	 * node, and setrefs.c will get confused and decide that the fdw_exprs
	 * entry is actually a reference to the fdw_scan_tlist entry, resulting in
	 * a broken plan.  Somewhat oddly, it's OK if the expression contains such
	 * a node, as long as it's not at top level; then no match is possible.
	 */
	i = 0;
	foreach(lc, grouping_target->exprs)
	{
		Expr	   *expr = (Expr *) lfirst(lc);
		Index		sgref = get_pathtarget_sortgroupref(grouping_target, i);
		ListCell   *l;

		/* Check whether this expression is part of GROUP BY clause */
		if (sgref && get_sortgroupref_clause_noerr(sgref, query->groupClause))
		{
			TargetEntry *tle;

            /*
			 * Ensure GROUP BY clauses are shippable at all by the corresponding
             * Python FDW instance.
			 */
            if (!fpinfo->groupby_supported) {
                elog(WARNING, "xxx3");
                return false;
            }

			/*
			 * If any GROUP BY expression is not shippable, then we cannot
			 * push down aggregation to the foreign server.
			 */
			if (!multicorn_is_foreign_expr(root, grouped_rel, expr)) {
                elog(WARNING, "xxx4");
				return false;
            }

			/*
			 * If it would be a foreign param, we can't put it into the tlist,
			 * so we have to fail.
			 */
			if (multicorn_is_foreign_param(root, grouped_rel, expr)) {
                elog(WARNING, "xxx5");
				return false;
            }

			/*
			 * Pushable, so add to tlist.  We need to create a TLE for this
			 * expression and apply the sortgroupref to it.  We cannot use
			 * add_to_flat_tlist() here because that avoids making duplicate
			 * entries in the tlist.  If there are duplicate entries with
			 * distinct sortgrouprefs, we have to duplicate that situation in
			 * the output tlist.
			 */
			tle = makeTargetEntry(expr, list_length(tlist) + 1, NULL, false);
			tle->ressortgroupref = sgref;
			tlist = lappend(tlist, tle);
		}
		else
		{
            /*
			 * Ensure aggregation functions are shippable at all by the corresponding
             * Python FDW instance.
			 */
            if (!fpinfo->agg_functions) {
                elog(WARNING, "xxx6");
                return false;
            }

			/*
			 * Non-grouping expression we need to compute.  Can we ship it
			 * as-is to the foreign server?
			 */
			if (multicorn_is_foreign_expr(root, grouped_rel, expr) &&
				!multicorn_is_foreign_param(root, grouped_rel, expr))
			{
				/* Yes, so add to tlist as-is; OK to suppress duplicates */
				tlist = add_to_flat_tlist(tlist, list_make1(expr));
			}
			else
			{
				/* Not pushable as a whole; extract its Vars and aggregates */
                List	   *aggvars;

				aggvars = pull_var_clause((Node *) expr,
										  PVC_INCLUDE_AGGREGATES);

                /*
				 * If any aggregate expression is not shippable, then we
				 * cannot push down aggregation to the foreign server.  (We
				 * don't have to check is_foreign_param, since that certainly
				 * won't return true for any such expression.)
				 */
				if (!multicorn_is_foreign_expr(root, grouped_rel, (Expr *) aggvars)) {
                    elog(WARNING, "xxx7");
					return false;
                }

				/*
				 * Add aggregates, if any, into the targetlist.  Plain Vars
				 * outside an aggregate can be ignored, because they should be
				 * either same as some GROUP BY column or part of some GROUP
				 * BY expression.  In either case, they are already part of
				 * the targetlist and thus no need to add them again.  In fact
				 * including plain Vars in the tlist when they do not match a
				 * GROUP BY column would cause the foreign server to complain
				 * that the shipped query is invalid.
				 */
				foreach(l, aggvars)
				{
					Expr	   *expr = (Expr *) lfirst(l);

					if (IsA(expr, Aggref))
						tlist = add_to_flat_tlist(tlist, list_make1(expr));
				}
			}
		}

		i++;
	}

	/*
     * TODO: Enable HAVING clause pushdowns.
     * Note that certain simple HAVING clauses get transformed to WHERE clauses
     * internally for performance reasons, i.e. smaller scan size. Example is a
     * HAVING clause on a column that is also a part of the GROUP BY clause, in
     * which case WHERE clause effectively achieves the same thing. In those
     * cases the havingQual is NULL, even though root->hasHavingQual is true.
	 */
	if (havingQual)
	{
        elog(WARNING, "xxx8");
		return false;
	}

	/* Store generated targetlist */
	fpinfo->grouped_tlist = tlist;

	/* Safe to pushdown */
	fpinfo->pushdown_safe = true;

	/*
	 * If user is willing to estimate cost for a scan using EXPLAIN, he
	 * intends to estimate scans on that relation more accurately. Then, it
	 * makes sense to estimate the cost of the grouping on that relation more
	 * accurately using EXPLAIN.
	 */
	fpinfo->use_remote_estimate = ofpinfo->use_remote_estimate;

	/* Copy startup and tuple cost as is from underneath input rel's fpinfo */
	fpinfo->fdw_startup_cost = ofpinfo->fdw_startup_cost;
	fpinfo->fdw_tuple_cost = ofpinfo->fdw_tuple_cost;

	/*
	 * Set # of retrieved rows and cached relation costs to some negative
	 * value, so that we can detect when they are set to some sensible values,
	 * during one (usually the first) of the calls to multicorn_estimate_path_cost_size.
	 */
	fpinfo->retrieved_rows = -1;
	fpinfo->rel_startup_cost = -1;
	fpinfo->rel_total_cost = -1;

	return true;
}

/*
 * multicornGetForeignUpperPaths
 *		Add paths for post-join operations like aggregation, grouping etc. if
 *		corresponding operations are safe to push down.
 *
 * Right now, we only support aggregate, grouping and having clause pushdown.
 */
static void
multicornGetForeignUpperPaths(PlannerInfo *root, UpperRelationKind stage,
						      RelOptInfo *input_rel, RelOptInfo *output_rel, void *extra
)
{
	MulticornPlanState *fpinfo;
    elog(WARNING, "here0");
	/*
	 * If input rel is not safe to pushdown, then simply return as we cannot
	 * perform any post-join operations on the foreign server.
	 */
	if (!input_rel->fdw_private ||
		!((MulticornPlanState *) input_rel->fdw_private)->pushdown_safe)
		return;

	/* Ignore stages we don't support; and skip any duplicate calls. */
	if (stage != UPPERREL_GROUP_AGG || output_rel->fdw_private)
		return;

    elog(WARNING, "here1");

    /*
     * Check with the Python FDW instance whether it supports pushdown at all
     * NB: Here we deviate from other FDWs, in that we don't know whether the
     * something can be pushed down without consulting the corresponding Python
     * FDW instance.
     */

    if (!canPushdownUpperrel((MulticornPlanState *) input_rel->fdw_private))
    {
        elog(WARNING, "here2");
        return;
    }
    elog(WARNING, "here3");

	fpinfo = (MulticornPlanState *) palloc0(sizeof(MulticornPlanState));
	fpinfo->pushdown_safe = false;
	fpinfo->stage = stage;
	output_rel->fdw_private = fpinfo;

	switch (stage)
	{
		case UPPERREL_GROUP_AGG:
			multicorn_add_foreign_grouping_paths(root, input_rel, output_rel, (GroupPathExtraData *) extra);
			break;
		default:
			elog(ERROR, "unexpected upper relation: %d", (int) stage);
			break;
	}
}

/*
 * multicorn_add_foreign_grouping_paths
 *		Add foreign path for grouping and/or aggregation.
 *
 * Given input_rel represents the underlying scan.  The paths are added to the
 * given grouped_rel.
 */
static void
multicorn_add_foreign_grouping_paths(PlannerInfo *root, RelOptInfo *input_rel,
								     RelOptInfo *grouped_rel,
                                     GroupPathExtraData *extra
)
{
	Query	   *parse = root->parse;
	MulticornPlanState *ifpinfo = input_rel->fdw_private;
	MulticornPlanState *fpinfo = grouped_rel->fdw_private;
	ForeignPath *grouppath;
	double		rows;
	int			width;
	Cost		startup_cost;
	Cost		total_cost;

	/* Nothing to be done, if there is no grouping or aggregation required. */
	if (!parse->groupClause && !parse->groupingSets && !parse->hasAggs &&
		!root->hasHavingQual)
		return;

	Assert(extra->patype == PARTITIONWISE_AGGREGATE_NONE ||
		   extra->patype == PARTITIONWISE_AGGREGATE_FULL);

	/* save the input_rel as outerrel in fpinfo */
	fpinfo->outerrel = input_rel;

	/*
	 * Copy foreign table, foreign server, user mapping, shippable extensions
	 * etc. details from the input relation's fpinfo.
	 */
    fpinfo->table = ifpinfo->table;
	fpinfo->server = ifpinfo->server;
	fpinfo->user = ifpinfo->user;

    /* copy the upperrel pushdown info as well */
    fpinfo->groupby_supported = ifpinfo->groupby_supported;
	fpinfo->agg_functions = ifpinfo->agg_functions;

    multicorn_merge_fdw_options(fpinfo, ifpinfo, NULL);

    elog(WARNING, "cabum0");

    /*
	 * Assess if it is safe to push down aggregation and grouping.
	 *
	 * Use HAVING qual from extra. In case of child partition, it will have
	 * translated Vars.
	 */
	if (!multicorn_foreign_grouping_ok(root, grouped_rel, extra->havingQual)) {
        elog(WARNING, "cabum1");
    	return;
    }

    elog(WARNING, "cabum2");

	/* Use small cost to push down aggregate always */
	rows = width = startup_cost = total_cost = 1;
	/* Now update this information in the fpinfo */
	fpinfo->rows = rows;
	fpinfo->width = width;
	fpinfo->startup_cost = startup_cost;
	fpinfo->total_cost = total_cost;

	/* Create and add foreign path to the grouping relation. */
	grouppath = create_foreign_upper_path(root,
										  grouped_rel,
										  grouped_rel->reltarget,
										  rows,
										  startup_cost,
										  total_cost,
										  NIL,	/* no pathkeys */
										  NULL,
										  NIL); /* no fdw_private */

	/* Add generated path into grouped_rel by add_path(). */
	add_path(grouped_rel, (Path *) grouppath);
}

/*
 *	"Serialize" a MulticornPlanState, so that it is safe to be carried
 *	between the plan and the execution safe.
 */
void *
serializePlanState(MulticornPlanState * state)
{
    List	   *result = NULL;

    result = lappend(result, makeConst(INT4OID,
                          -1, InvalidOid, 4, Int32GetDatum(state->numattrs), false, true));
    result = lappend(result, makeConst(INT4OID,
                    -1, InvalidOid, 4, Int32GetDatum(state->foreigntableid), false, true));
    result = lappend(result, state->target_list);

    result = lappend(result, serializeDeparsedSortGroup(state->pathkeys));

    result = lappend(result, state->upper_rel_targets);

    result = lappend(result, state->aggs);

    result = lappend(result, state->group_clauses);

    result = lappend(result, state->baserestrictinfo);

    result = lappend(result, state->rtindex);

    /* Serialize the new 'limit' attribute as a DOUBLE */
    result = lappend(result, makeConst(FLOAT8OID,
                    -1, InvalidOid, 8, Float8GetDatum(state->limit), false, true));

    /* Serialize the 'plan_id' attribute as INT8 */
    result = lappend(result, makeConst(INT8OID,
                    -1, InvalidOid, 8, Int64GetDatum(state->plan_id), false, true));

    return result;
}

/*
 *	"Deserialize" an internal state and inject it in an
 *	MulticornExecState
 */
MulticornExecState *
initializeExecState(void *internalstate)
{
    MulticornExecState *execstate = palloc0(sizeof(MulticornExecState));
    List	   *values = (List *) internalstate;
    AttrNumber	attnum = ((Const *) linitial(values))->constvalue;
    Oid			foreigntableid = ((Const *) lsecond(values))->constvalue;
    List		*pathkeys;

    ForeignTable *ftable = GetForeignTable(foreigntableid);
    Relation	rel = RelationIdGetRelation(ftable->relid);
    AttInMetadata *attinmeta;

    attinmeta = TupleDescGetAttInMetadata(rel->rd_att);
    execstate->qual_cinfos = palloc0(sizeof(ConversionInfo *) *
                                     attinmeta->tupdesc->natts);
    initConversioninfo(execstate->qual_cinfos, attinmeta, NULL);
    RelationClose(rel);

    /* Those list must be copied, because their memory context can become */
    /* invalid during the execution (in particular with the cursor interface) */
    execstate->target_list = copyObject(lthird(values));
    pathkeys = lfourth(values);
    execstate->pathkeys = deserializeDeparsedSortGroup(pathkeys);
    execstate->fdw_instance = getInstance(foreigntableid);
    execstate->buffer = makeStringInfo();
    execstate->cinfos = palloc0(sizeof(ConversionInfo *) * attnum);
    execstate->values = palloc(attnum * sizeof(Datum));
    execstate->nulls = palloc(attnum * sizeof(bool));

    execstate->upper_rel_targets = list_nth(values, 4);
    execstate->aggs = list_nth(values, 5);
    execstate->group_clauses = list_nth(values, 6);
    execstate->baserestrictinfo = list_nth(values, 7);
    execstate->rtindex = list_nth(values, 8);

    /* Deserialize the 'limit' value */
    execstate->limit = DatumGetFloat8(((Const *) list_nth(values, 9))->constvalue);

    /* Deserialize the 'plan_id' value */
    Datum plan_id_datum = ((Const *) list_nth(values, 10))->constvalue;
    execstate->plan_id = DatumGetInt64(plan_id_datum);

    return execstate;
}