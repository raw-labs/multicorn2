/*-------------------------------------------------------------------------
 *
 * Multicorn Foreign Data Wrapper for PostgreSQL
 *
 * IDENTIFICATION
 *        deparse.c
 *
 *-------------------------------------------------------------------------
 */

#include "postgres.h"

#include "pgtime.h"
#include "access/heapam.h"
#include "access/htup_details.h"
#include "access/sysattr.h"
#include "catalog/pg_aggregate.h"
#include "catalog/pg_collation.h"
#include "catalog/pg_namespace.h"
#include "catalog/pg_operator.h"
#include "catalog/pg_proc.h"
#include "catalog/pg_type.h"
#include "commands/defrem.h"
#include "nodes/nodeFuncs.h"
#include "nodes/plannodes.h"
#include "nodes/nodes.h"
#include "optimizer/clauses.h"
#include "optimizer/optimizer.h"
#include "optimizer/tlist.h"
#include "parser/parsetree.h"
#include "utils/builtins.h"
#include "utils/lsyscache.h"
#include "utils/syscache.h"
#include "utils/timestamp.h"
#include "utils/typcache.h"
#include "commands/tablecmds.h"
#include "nodes/print.h" 

#include "multicorn.h"


/*
 * Local (per-tree-level) context for multicorn_foreign_expr_walker's search.
 * This is concerned with identifying collations used in the expression.
 */
typedef enum
{
	FDW_COLLATE_NONE,			/* expression is of a noncollatable type */
	FDW_COLLATE_SAFE,			/* collation derives from a foreign Var */
	FDW_COLLATE_UNSAFE			/* collation derives from something else */
} FDWCollateState;


/*
 * Global context for multicorn_foreign_expr_walker's search of an expression tree.
 */
typedef struct foreign_glob_cxt
{
	PlannerInfo *root;			/* global planner state */
	RelOptInfo *foreignrel;		/* the foreign relation we are planning for */

	/*
	 * For join pushdown, only a limited set of operators are allowed to be
	 * pushed.  This flag helps us identify if we are walking through the list
	 * of join conditions. Also true for aggregate relations to restrict
	 * aggregates for specified list.
	 */
	bool		is_remote_cond;	/* true for join or aggregate relations */
	Relids		relids;			/* relids of base relations in the underlying
								 * scan */
} foreign_glob_cxt;

typedef struct foreign_loc_cxt
{
	Oid			collation;		/* OID of current collation, if any */
	FDWCollateState state;		/* state of current collation choice */
} foreign_loc_cxt;

static String *multicorn_deparse_function_name(Oid funcid);


/*
 * Return true if given object is one of PostgreSQL's built-in objects.
 *
 * We use PG_CATALOG_NAMESPACE as the cutoff, so that we only consider
 * objects with hand-assigned OIDs to be "built in", not for instance any
 * function or type defined in the information_schema.
 *
 * Our constraints for dealing with types are tighter than they are for
 * functions or operators: we want to accept only types that are in pg_catalog,
 * else format_type might incorrectly fail to schema-qualify their names.
 * (This could be fixed with some changes to format_type, but for now there's
 * no need.)  Thus we must exclude information_schema types.
 *
 * XXX there is a problem with this, which is that the set of built-in
 * objects expands over time.  Something that is built-in to us might not
 * be known to the remote server, if it's of an older version.  But keeping
 * track of that would be a huge exercise.
 */
static bool
multicorn_is_builtin(Oid oid)
{
	return (oid < FirstNormalObjectId);
}

static const char *
nodeTagToString(NodeTag tag)
{
    switch (tag)
    {
        case T_Invalid: return "T_Invalid";
        case T_IndexInfo: return "T_IndexInfo";
        case T_ExprContext: return "T_ExprContext";
        case T_ProjectionInfo: return "T_ProjectionInfo";
        case T_JunkFilter: return "T_JunkFilter";
        case T_ResultRelInfo: return "T_ResultRelInfo";
        case T_EState: return "T_EState";
        case T_TupleTableSlot: return "T_TupleTableSlot";
        /* Add cases for all NodeTag values you expect */
        case T_Var: return "T_Var";
        case T_Const: return "T_Const";
        case T_Param: return "T_Param";
        case T_Aggref: return "T_Aggref";
        case T_GroupingFunc: return "T_GroupingFunc";
        case T_WindowFunc: return "T_WindowFunc";
        case T_ParamRef: return "T_ParamRef";
        case T_FuncExpr: return "T_FuncExpr";
        case T_OpExpr: return "T_OpExpr";
        case T_DistinctExpr: return "T_DistinctExpr";
        case T_NullIfExpr: return "T_NullIfExpr";
        case T_ScalarArrayOpExpr: return "T_ScalarArrayOpExpr";
        case T_BoolExpr: return "T_BoolExpr";
        case T_SubLink: return "T_SubLink";
        case T_SubPlan: return "T_SubPlan";
        case T_AlternativeSubPlan: return "T_AlternativeSubPlan";
        case T_FieldSelect: return "T_FieldSelect";
        case T_FieldStore: return "T_FieldStore";
        case T_RelabelType: return "T_RelabelType";
        case T_CoerceViaIO: return "T_CoerceViaIO";
        case T_ArrayCoerceExpr: return "T_ArrayCoerceExpr";
        case T_ConvertRowtypeExpr: return "T_ConvertRowtypeExpr";
        case T_CollateExpr: return "T_CollateExpr";
        case T_CaseExpr: return "T_CaseExpr";
        case T_CaseWhen: return "T_CaseWhen";
        case T_CaseTestExpr: return "T_CaseTestExpr";
        case T_ArrayExpr: return "T_ArrayExpr";
        case T_RowExpr: return "T_RowExpr";
        case T_RowCompareExpr: return "T_RowCompareExpr";
        case T_CoalesceExpr: return "T_CoalesceExpr";
        case T_MinMaxExpr: return "T_MinMaxExpr";
        case T_SQLValueFunction: return "T_SQLValueFunction";
        case T_XmlExpr: return "T_XmlExpr";
        case T_NullTest: return "T_NullTest";
        case T_BooleanTest: return "T_BooleanTest";
        case T_CoerceToDomain: return "T_CoerceToDomain";
        case T_CoerceToDomainValue: return "T_CoerceToDomainValue";
        case T_SetToDefault: return "T_SetToDefault";
        case T_CurrentOfExpr: return "T_CurrentOfExpr";
        case T_NextValueExpr: return "T_NextValueExpr";
        case T_InferenceElem: return "T_InferenceElem";
        case T_TargetEntry: return "T_TargetEntry";
        case T_RangeTblRef: return "T_RangeTblRef";
        case T_JoinExpr: return "T_JoinExpr";
        case T_FromExpr: return "T_FromExpr";
        /* Add more cases as needed */
        default:
            {
                static char buffer[64];
                snprintf(buffer, sizeof(buffer), "Unknown NodeTag (%d)", (int) tag);
                return buffer;
            }
    }
}

static bool foreign_expr_recursive_walker(Node *node,
                                          foreign_glob_cxt *glob_cxt,
                                          foreign_loc_cxt *inner_cxt);

/*
 * Check if expression is safe to execute remotely, and return true if so.
 *
 * In addition, *outer_cxt is updated with collation information.
 *
 * We must check that the expression contains only node types we can deparse,
 * that all types/functions/operators are safe to send (which we approximate
 * as being built-in), and that all collations used in the expression derive
 * from Vars of the foreign table.  Because of the latter, the logic is
 * pretty close to assign_collations_walker() in parse_collate.c, though we
 * can assume here that the given expression is valid.
 */
static bool
multicorn_foreign_expr_walker(Node *node,
						      foreign_glob_cxt *glob_cxt,
						      foreign_loc_cxt *outer_cxt)
{
	bool		check_type = true;
    MulticornPlanState *fpinfo;
	foreign_loc_cxt inner_cxt;
	Oid			collation = InvalidOid;
	FDWCollateState state = FDW_COLLATE_NONE;
	HeapTuple	tuple;

	/* Need do nothing for empty subexpressions */
	if (node == NULL) {
		elog(WARNING, "kkk0");
		return true;
	}

    /* Needed to asses per-instance FDW shipability properties */
	fpinfo = (MulticornPlanState *) (glob_cxt->foreignrel->fdw_private);

	/* Set up inner_cxt for possible recursion to child nodes */
	inner_cxt.collation = InvalidOid;
	inner_cxt.state = FDW_COLLATE_NONE;
	switch (nodeTag(node))
	{
		case T_Var:
			{
				Var *var = (Var *) node;

				/*
				 * If the Var is from the foreign table, we consider its
				 * collation (if any) safe to use.  If it is from another
				 * table, we treat its collation the same way as we would a
				 * Param's collation, ie it's not safe for it to have a
				 * non-default collation.
				 */
				if (bms_is_member(var->varno, glob_cxt->relids) &&
					var->varlevelsup == 0)
				{
					/* Var belongs to foreign table */

					/*
					 * System columns (e.g. oid, ctid) should not be sent to
					 * the remote, since we don't make any effort to ensure
					 * that local and remote values match (tableoid, in
					 * particular, almost certainly doesn't match).
					 */
					if (var->varattno < 0) {
						elog(WARNING, "kkk1");
						return false;
					}

					/* Else check the collation */
					collation = var->varcollid;
					state = OidIsValid(collation) ? FDW_COLLATE_SAFE : FDW_COLLATE_NONE;
				}
				else
				{
					/* Var belongs to some other table */
					collation = var->varcollid;
					if (collation == InvalidOid ||
						collation == DEFAULT_COLLATION_OID)
					{
						/*
						 * It's noncollatable, or it's safe to combine with a
						 * collatable foreign Var, so set state to NONE.
						 */
						state = FDW_COLLATE_NONE;
					}
					else
					{
						/*
						 * Do not fail right away, since the Var might appear
						 * in a collation-insensitive context.
						 */
						state = FDW_COLLATE_UNSAFE;
					}
				}
			}
			break;
		case T_Aggref:
			{
				Aggref	   *agg = (Aggref *) node;
				ListCell   *lc;
				char	   *opername = NULL;
                StringInfo opername_composite = makeStringInfo();
				Oid			schema;

				/* get function name and schema */
				tuple = SearchSysCache1(PROCOID, ObjectIdGetDatum(agg->aggfnoid));
				if (!HeapTupleIsValid(tuple))
				{
					elog(ERROR, "cache lookup failed for function %u", agg->aggfnoid);
				}
				opername = pstrdup(((Form_pg_proc) GETSTRUCT(tuple))->proname.data);
				schema = ((Form_pg_proc) GETSTRUCT(tuple))->pronamespace;
				ReleaseSysCache(tuple);

				/* ignore functions in other than the pg_catalog schema */
				if (schema != PG_CATALOG_NAMESPACE) {
					elog(WARNING, "kkk2");
					return false;
				}

                /* Make sure the specific function at hand is shippable
                 * NB: here we deviate from standard FDW code, since the allowed
                 * function list is fetched from the Python FDW instance
                 */
                if (agg->aggstar)
                {
                    initStringInfo(opername_composite);
                    appendStringInfoString(opername_composite, opername);
                    appendStringInfoString(opername_composite, ".*");

                    if (!list_member(fpinfo->agg_functions, makeString(opername_composite->data))) {
						elog(WARNING, "kkk3");
					    return false;
					}
                }
				else if (!list_member(fpinfo->agg_functions, makeString(opername))) {
					elog(WARNING, "kkk4");
					return false;
				}

				/* Not safe to pushdown when not in grouping context */
				if (!IS_UPPER_REL(glob_cxt->foreignrel)) {
					elog(WARNING, "kkk5");
					return false;
				}

				/* Only non-split aggregates are pushable. */
				if (agg->aggsplit != AGGSPLIT_SIMPLE) {
					elog(WARNING, "kkk6");
					return false;
				}

                /*
                 * For now we don't push down DISTINCT aggregations.
                 * TODO: Enable this
                 */
                if (agg->aggdistinct) {
					elog(WARNING, "kkk7");
                    return false;
				}

				/*
				 * Recurse to input args. aggdirectargs, aggorder and
				 * aggdistinct are all present in args, so no need to check
				 * their shippability explicitly.
				 */
				foreach(lc, agg->args)
				{
					Node	   *n = (Node *) lfirst(lc);

					/* If TargetEntry, extract the expression from it */
					if (IsA(n, TargetEntry))
					{
						TargetEntry *tle = (TargetEntry *) n;

						n = (Node *) tle->expr;
					}

					if (!multicorn_foreign_expr_walker(n, glob_cxt, &inner_cxt)) {
						elog(WARNING, "kkk8");
						return false;
					}
				}

				if (agg->aggorder || agg->aggfilter)
				{
					elog(WARNING, "kkk9");
					return false;
				}

				/*
				 * If aggregate's input collation is not derived from a
				 * foreign Var, it can't be sent to remote.
				 */
				if (agg->inputcollid == InvalidOid)
					 /* OK, inputs are all noncollatable */ ;
				else if (inner_cxt.state != FDW_COLLATE_SAFE ||
						 agg->inputcollid != inner_cxt.collation) {
					elog(WARNING, "kkk10");
					return false;
				}

				/*
				 * Detect whether node is introducing a collation not derived
				 * from a foreign Var.  (If so, we just mark it unsafe for now
				 * rather than immediately returning false, since the parent
				 * node might not care.)
				 */
				collation = agg->aggcollid;
				if (collation == InvalidOid)
					state = FDW_COLLATE_NONE;
				else if (inner_cxt.state == FDW_COLLATE_SAFE &&
						 collation == inner_cxt.collation)
					state = FDW_COLLATE_SAFE;
				else if (collation == DEFAULT_COLLATION_OID)
					state = FDW_COLLATE_NONE;
				else
					state = FDW_COLLATE_UNSAFE;
			}
			break;

    	case T_List:
        {
            ListCell *lc;

            foreach(lc, (List *) node)
            {
                if (!multicorn_foreign_expr_walker((Node *) lfirst(lc), glob_cxt, outer_cxt))
                {
                    return false;
                }
            }
            return true;
        }
        break;

 		// case T_Const:
        //     {
        //         Const *c = (Const *) node;

        //         collation = c->constcollid;
        //         state = OidIsValid(collation) ? FDW_COLLATE_SAFE : FDW_COLLATE_NONE;

        //         /* Check if the constant's type is built-in */
        //         if (check_type && !multicorn_is_builtin(c->consttype))
        //             return false;
        //     }
        //     break;

        // case T_Param:
        //     {
        //         Param *p = (Param *) node;

        //         collation = p->paramcollid;
        //         state = OidIsValid(collation) ? FDW_COLLATE_SAFE : FDW_COLLATE_NONE;

        //         /* Check if the parameter's type is built-in */
        //         if (check_type && !multicorn_is_builtin(p->paramtype))
        //             return false;
        //     }
        //     break;

        // case T_FuncExpr:
        //     {
        //         FuncExpr   *fe = (FuncExpr *) node;

        //         /* Check if the function is shippable */
        //         if (!multicorn_is_builtin(fe->funcid))
        //             return false;

        //         /* Recurse into arguments */
        //         if (!foreign_expr_recursive_walker((Node *) fe->args, glob_cxt, &inner_cxt))
        //             return false;

        //         /* Handle collation */
        //         collation = fe->funccollid;
        //         state = FDW_COLLATE_NONE;
        //         if (fe->inputcollid == InvalidOid)
        //             ; /* OK */
        //         else if (inner_cxt.state != FDW_COLLATE_SAFE || fe->inputcollid != inner_cxt.collation)
        //             return false;
        //     }
        //     break;

        // case T_OpExpr:
        //     {
        //         OpExpr     *oe = (OpExpr *) node;

        //         /* Check if the operator is shippable */
        //         if (!multicorn_is_builtin(oe->opno))
        //             return false;

        //         /* Recurse into arguments */
        //         if (!foreign_expr_recursive_walker((Node *) oe->args, glob_cxt, &inner_cxt))
        //             return false;

        //         /* Handle collation */
        //         collation = oe->opcollid;
        //         state = FDW_COLLATE_NONE;
        //         if (oe->inputcollid == InvalidOid)
        //             ; /* OK */
        //         else if (inner_cxt.state != FDW_COLLATE_SAFE || oe->inputcollid != inner_cxt.collation)
        //             return false;
        //     }
        //     break;

        // case T_RelabelType:
        //     {
        //         RelabelType *rt = (RelabelType *) node;

        //         /* Recurse into the argument */
        //         if (!multicorn_foreign_expr_walker((Node *) rt->arg, glob_cxt, &inner_cxt))
        //             return false;

        //         /* Handle collation */
        //         collation = rt->resultcollid;
        //         state = inner_cxt.state;
        //     }
        //     break;

        // case T_BoolExpr:
        //     {
        //         BoolExpr   *be = (BoolExpr *) node;
        //         ListCell   *lc;

        //         /* Recurse into arguments */
        //         foreach(lc, be->args)
        //         {
        //             if (!multicorn_foreign_expr_walker((Node *) lfirst(lc), glob_cxt, &inner_cxt))
        //                 return false;
        //         }

        //         /* BoolExpr doesn't affect collation */
        //         collation = InvalidOid;
        //         state = FDW_COLLATE_NONE;
        //     }
        //     break;

        // case T_NullTest:
        //     {
        //         NullTest   *nt = (NullTest *) node;

        //         /* Recurse into the argument */
        //         if (!multicorn_foreign_expr_walker((Node *) nt->arg, glob_cxt, &inner_cxt))
        //             return false;

        //         /* NullTest doesn't affect collation */
        //         collation = InvalidOid;
        //         state = FDW_COLLATE_NONE;
        //     }
        //     break;


		default:

			/*
			 * If it's anything else, assume it's unsafe.  This list can be
			 * expanded later, but don't forget to add deparse support below.
			 */

			{
				char *node_str = nodeToString(node);
				elog(WARNING, "kkk11: Unhandled node type: %s, nodeTag(node): %d, T_Aggref: %d", node_str, (int) nodeTag(node), (int) T_Aggref);
				pfree(node_str); // Free the memory allocated by nodeToString				
        		// const char *nodeTypeName = nodeTagToString(nodeTag(node));
        		// elog(WARNING, "kkk11: Unhandled node type: %s", nodeTypeName);
        		return false;
			}
	}

	/*
	 * If result type of given expression is not built-in, it can't be sent to
	 * remote because it might have incompatible semantics on remote side.
	 */
	if (check_type && !multicorn_is_builtin(exprType(node))) {
		elog(WARNING, "kkk12");
		return false;
	}

	/*
	 * Now, merge my collation information into my parent's state.
	 */
	if (state > outer_cxt->state)
	{
		/* Override previous parent state */
		outer_cxt->collation = collation;
		outer_cxt->state = state;
	}
	else if (state == outer_cxt->state)
	{
		/* Merge, or detect error if there's a collation conflict */
		switch (state)
		{
			case FDW_COLLATE_NONE:
				/* Nothing + nothing is still nothing */
				break;
			case FDW_COLLATE_SAFE:
				if (collation != outer_cxt->collation)
				{
					/*
					 * Non-default collation always beats default.
					 */
					if (outer_cxt->collation == DEFAULT_COLLATION_OID)
					{
						/* Override previous parent state */
						outer_cxt->collation = collation;
					}
					else if (collation != DEFAULT_COLLATION_OID)
					{
						/*
						 * Conflict; show state as indeterminate.  We don't
						 * want to "return false" right away, since parent
						 * node might not care about collation.
						 */
						outer_cxt->state = FDW_COLLATE_UNSAFE;
					}
				}
				break;
			case FDW_COLLATE_UNSAFE:
				/* We're still conflicted ... */
				break;
		}
	}
	/* It looks OK */
	return true;
}

/* Helper function to recurse into expression trees */
static bool
foreign_expr_recursive_walker(Node *node, foreign_glob_cxt *glob_cxt, foreign_loc_cxt *inner_cxt)
{
    if (node == NULL)
        return true;

    if (IsA(node, List))
    {
        ListCell *lc;
        foreach(lc, (List *) node)
        {
            if (!multicorn_foreign_expr_walker((Node *) lfirst(lc), glob_cxt, inner_cxt))
                return false;
        }
        return true;
    }
    else
    {
        return multicorn_foreign_expr_walker(node, glob_cxt, inner_cxt);
    }
}

/*
 * Returns true if given expr is safe to evaluate on the foreign server.
 */
bool
multicorn_is_foreign_expr(PlannerInfo *root,
					      RelOptInfo *baserel,
					      Expr *expr)
{
	foreign_glob_cxt glob_cxt;
	foreign_loc_cxt loc_cxt;
	MulticornPlanState *fpinfo = (MulticornPlanState *) (baserel->fdw_private);

	/*
	 * Check that the expression consists of nodes that are safe to execute
	 * remotely.
	 */
	glob_cxt.root = root;
	glob_cxt.foreignrel = baserel;

	/*
	 * For an upper relation, use relids from its underneath scan relation,
	 * because the upperrel's own relids currently aren't set to anything
	 * meaningful by the core code.  For other relation, use their own relids.
	 */
	if (IS_UPPER_REL(baserel))
		glob_cxt.relids = fpinfo->outerrel->relids;
	else
		glob_cxt.relids = baserel->relids;
	loc_cxt.collation = InvalidOid;
	loc_cxt.state = FDW_COLLATE_NONE;
	if (!multicorn_foreign_expr_walker((Node *) expr, &glob_cxt, &loc_cxt)) {
		elog(WARNING, "zzz0");
		return false;
	}

	/*
	 * If the expression has a valid collation that does not arise from a
	 * foreign var, the expression can not be sent over.
	 */
	if (loc_cxt.state == FDW_COLLATE_UNSAFE) {
		elog(WARNING, "zzz1");
		return false;
	}

	/*
	 * An expression which includes any mutable functions can't be sent over
	 * because its result is not stable.  For example, sending now() remote
	 * side could cause confusion from clock offsets.  Future versions might
	 * be able to make this choice with more granularity. (We check this last
	 * because it requires a lot of expensive catalog lookups.)
	 */
	if (contain_mutable_functions((Node *) expr)) {
		elog(WARNING, "zzz2");
		return false;
	}

	/* OK to evaluate on the remote server */
	return true;
}


/*
 * Returns true if given expr is something we'd have to send the value of
 * to the foreign server.
 *
 * This should return true when the expression is a shippable node that
 * deparseExpr would add to context->params_list.  Note that we don't care
 * if the expression *contains* such a node, only whether one appears at top
 * level.  We need this to detect cases where setrefs.c would recognize a
 * false match between an fdw_exprs item (which came from the params_list)
 * and an entry in fdw_scan_tlist (which we're considering putting the given
 * expression into).
 */
bool
multicorn_is_foreign_param(PlannerInfo *root,
						   RelOptInfo *baserel,
						   Expr *expr)
{
	if (expr == NULL)
		return false;

	switch (nodeTag(expr))
	{
		case T_Var:
			{
				/* It would have to be sent unless it's a foreign Var */
				Var		   *var = (Var *) expr;
				MulticornPlanState *fpinfo = (MulticornPlanState *) (baserel->fdw_private);
				Relids		relids;

				if (IS_UPPER_REL(baserel))
					relids = fpinfo->outerrel->relids;
				else
					relids = baserel->relids;

				if (bms_is_member(var->varno, relids) && var->varlevelsup == 0)
					return false;	/* foreign Var, so not a param */
				else
					return true;	/* it'd have to be a param */
				break;
			}
		case T_Param:
			/* Params always have to be sent to the foreign server */
			return true;
		default:
			break;
	}
	return false;
}

/*
 * Build the targetlist for given relation to be deparsed as SELECT clause.
 *
 * The output targetlist contains the columns that need to be fetched from the
 * foreign server for the given relation.  If foreignrel is an upper relation,
 * then the output targetlist can also contains expressions to be evaluated on
 * foreign server.
 */
List *
multicorn_build_tlist_to_deparse(RelOptInfo *foreignrel)
{
	List	   *tlist = NIL;
	MulticornPlanState *fpinfo = (MulticornPlanState *) foreignrel->fdw_private;
	ListCell   *lc;

	/*
	 * For an upper relation, we have already built the target list while
	 * checking shippability, so just return that.
	 */
	if (IS_UPPER_REL(foreignrel))
		return fpinfo->grouped_tlist;

	return tlist;
}

/*
 * Iterate through the targets and extract relveant information needed to execute
 * the aggregation and/or grouping on the remote data source through Python.
 *
 * NB: Logic here is strongly coupled to multicorn_foreign_grouping_ok(), i.e.
 * if there is no ressortgroupref set, we automatically assume the only other
 * option is a Aggref node type.
 * Moreover, for the Aggref node type we assume only a single element in args
 * (e.g. sum(column2)). In particular, this is because in
 * multicorn_foreign_expr_walker() we don't have T_OpExpr case yet.
 */
void
multicorn_extract_upper_rel_info(PlannerInfo *root, List *tlist, MulticornPlanState *fpinfo)
{
    ListCell *lc;
    TargetEntry *tle;
    Var *var;
    String *colname, *function;
    Aggref *aggref;
    StringInfo agg_key = makeStringInfo();

    foreach(lc, tlist)
    {
        tle = lfirst_node(TargetEntry, lc);

        if (tle->ressortgroupref)
        {
            /* GROUP BY target */
            var = (Var *) tle->expr;
            colname = colnameFromVar(var, root, fpinfo);

            fpinfo->group_clauses = lappend(fpinfo->group_clauses, colname);
            fpinfo->upper_rel_targets = lappend(fpinfo->upper_rel_targets, colname);
        }
        else
        {
            /* Aggregation target */
            aggref = (Aggref *) tle->expr;
            function = multicorn_deparse_function_name(aggref->aggfnoid);

            if (aggref->aggstar)
            {
                colname = makeString("*");
            }
            else
            {
                var = linitial(pull_var_clause((Node *) aggref,
                                            PVC_RECURSE_AGGREGATES |
                                            PVC_RECURSE_PLACEHOLDERS));
                colname = colnameFromVar(var, root, fpinfo);
            }

            initStringInfo(agg_key);
            appendStringInfoString(agg_key, strVal(function));
            appendStringInfoString(agg_key, ".");
            appendStringInfoString(agg_key, strVal(colname));

            fpinfo->aggs = lappend(fpinfo->aggs, list_make3(makeString(agg_key->data), function, colname));
            fpinfo->upper_rel_targets = lappend(fpinfo->upper_rel_targets, makeString(agg_key->data));
        }
    }
}

/*
 * multicorn_deparse_function_name
 *		Deparses function name from given function oid.
 */
static String *
multicorn_deparse_function_name(Oid funcid)
{
	HeapTuple	proctup;
	Form_pg_proc procform;
	char *proname;

	proctup = SearchSysCache1(PROCOID, ObjectIdGetDatum(funcid));
	if (!HeapTupleIsValid(proctup))
		elog(ERROR, "cache lookup failed for function %u", funcid);
	procform = (Form_pg_proc) GETSTRUCT(proctup);

	proname = NameStr(procform->proname);

	ReleaseSysCache(proctup);
    return makeString(proname);
}
