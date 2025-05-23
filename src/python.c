#include <Python.h>
#include "datetime.h"
#include "postgres.h"
#include "multicorn.h"
#include "catalog/pg_user_mapping.h"
#include "access/reloptions.h"
#include "miscadmin.h"
#include "utils/numeric.h"
#include "utils/date.h"
#include "utils/timestamp.h"
#include "utils/array.h"
#include "utils/catcache.h"
#include "utils/memutils.h"
#include "utils/resowner.h"
#include "utils/rel.h"
#include "utils/rel.h"
#include "executor/nodeSubplan.h"
#include "bytesobject.h"
#include "mb/pg_wchar.h"
#include "access/xact.h"
#include "utils/lsyscache.h"
#include "executor/spi.h"
#include "utils/jsonb.h"



List	   *getOptions(Oid foreigntableid);
bool		compareOptions(List *options1, List *options2);

void		getColumnsFromTable(TupleDesc desc, PyObject **p_columns, List **columns);
bool		compareColumns(List *columns1, List *columns2);

PyObject   *getClass(PyObject *className);
PyObject   *valuesToPySet(List *targetlist);
PyObject   *qualDefsToPyList(List *quallist, ConversionInfo ** cinfo);
PyObject *pythonQual(char *operatorname, PyObject *value,
           ConversionInfo * cinfo,
           bool is_array,
           bool use_or,
           Oid typeoid);

PyObject  *getSortKey(MulticornDeparsedSortGroup *key);
MulticornDeparsedSortGroup *getDeparsedSortGroup(PyObject *key);


Datum pyobjectToDatum(PyObject *object, StringInfo buffer,
                ConversionInfo * cinfo);
PyObject   *qualdefToPython(MulticornConstQual * qualdef, ConversionInfo ** cinfo);
PyObject *paramDefToPython(List *paramdef, ConversionInfo ** cinfos,
                 Oid typeoid,
                 Datum value);

Datum
foreign_function_execute(List *options_list, int nArgs, char **argNames,  Oid *argTypes, Datum *argDatums, bool *argNulls, Oid retType);

PyObject   *datumToPython(Datum node, Oid typeoid, ConversionInfo * cinfo);
static PyObject   *datumStringToPython(Datum node, ConversionInfo * cinfo);
static PyObject   *datumBlankPaddedStringToPython(Datum datum, ConversionInfo * cinfo);
static PyObject   *datumFloat4ToPython(Datum datum, ConversionInfo * cinfo);
static PyObject   *datumFloat8ToPython(Datum datum, ConversionInfo * cinfo);
static PyObject   *datumDateToPython(Datum datum, ConversionInfo * cinfo);
static PyObject   *datumTimestampToPython(Datum datum, ConversionInfo * cinfo);
static PyObject   *datumTimestampTzToPython(Datum datum, ConversionInfo * cinfo);
static PyObject   *datumIntToPython(Datum datum, ConversionInfo * cinfo);
static PyObject   *datumArrayToPython(Datum datum, Oid type, ConversionInfo * cinfo);
static PyObject   *datumByteaToPython(Datum datum, ConversionInfo * cinfo);
static PyObject   *datumUnknownToPython(Datum datum, ConversionInfo * cinfo, Oid type);


void pythonDictToTuple(PyObject *p_value,
                  TupleTableSlot *slot,
                  ConversionInfo ** cinfos,
                  StringInfo buffer);

void pythonSequenceToTuple(PyObject *p_value,
                      TupleTableSlot *slot,
                      ConversionInfo ** cinfos,
                      StringInfo buffer);

/* Python to cstring functions */
void pyobjectToCString(PyObject *pyobject, StringInfo buffer,
                  ConversionInfo * cinfo);

void pynumberToCString(PyObject *pyobject, StringInfo buffer,
                  ConversionInfo * cinfo);
void pyunicodeToCString(PyObject *pyobject, StringInfo buffer,
                   ConversionInfo * cinfo);
void pystringToCString(PyObject *pyobject, StringInfo buffer,
                  ConversionInfo * cinfo);
void pysequenceToCString(PyObject *pyobject, StringInfo buffer,
                    ConversionInfo * cinfo);
void pymappingToCString(PyObject *pyobject, StringInfo buffer,
                   ConversionInfo * cinfo);
void hstoreArrayToCString(PyObject *pyobject, Py_ssize_t size, StringInfo buffer);
void pydateToCString(PyObject *pyobject, StringInfo buffer,
                ConversionInfo * cinfo);
void pytimeToCString(PyObject *pyobject, StringInfo buffer,
                ConversionInfo * cinfo);

void pyunknownToCstring(PyObject *pyobject, StringInfo buffer,
                   ConversionInfo * cinfo);

void appendBinaryStringInfoQuote(StringInfo buffer,
                            char *tempbuffer,
                            Py_ssize_t strlength,
                            bool need_quote);

void hstoreEscapedString(PyObject *s, StringInfo buffer);

static void begin_remote_xact(CacheEntry * entry);

static char* ascii_encoding_name = "ascii";

static Oid hstore_oid = InvalidOid;
static Oid hstore_array_oid = InvalidOid;
static Oid hstore_to_jsonb_oid = InvalidOid;

/* Setters for HSTORE related OIDs: hstore, hstore[] and hstore_to_jsonb, used when
 * translating hstore values to python */

void setHstoreOid(Oid oid) {
    if (oid == InvalidOid) {
        /* The HSTORE extension should have been loaded upfront. */
        elog(ERROR, "Invalid HSTORE OID (is the 'hstore' extension loaded?)");
    }
    elog(DEBUG3, "Setting HSTORE OID to %d", oid);
    hstore_oid = oid;
}

void setHstoreArrayOid(Oid oid) {
    if (oid == InvalidOid) {
        /* The HSTORE extension should have been loaded upfront. */
        elog(ERROR, "Invalid HSTORE array OID (is the 'hstore' extension loaded?)");
    }
    elog(DEBUG3, "Setting HSTORE array OID to %d", oid);
    hstore_array_oid = oid;
}

void setHstoreToJsonbOid(Oid oid) {
    if (oid == InvalidOid) {
        /* The HSTORE extension should have been loaded upfront. */
        elog(ERROR, "Invalid hstore_to_jsonb OID (is the 'hstore' extension loaded?)");
    }
    elog(DEBUG3, "Setting hstore_to_jsonb OID to %d", oid);
    hstore_to_jsonb_oid = oid;
}

/*
 * Get a (python) encoding name for an attribute.
 */
const char *
getPythonEncodingName()
{
    const char *encoding_name = GetDatabaseEncodingName();

    if (strcmp(encoding_name, "SQL_ASCII") == 0)
    {
        encoding_name = ascii_encoding_name;
    }
    return encoding_name;
}

PGDLLEXPORT char *
PyUnicode_AsPgString(PyObject *p_unicode)
{
    char	   *message = NULL;
    PyObject   *pTempStr;

    if (p_unicode == NULL)
    {
        elog(ERROR, "Received a null pointer in pyunicode_aspgstring");
    }
    pTempStr = PyUnicode_AsEncodedString(p_unicode, getPythonEncodingName(), NULL);
    errorCheck();
    message = strdup(PyBytes_AsString(pTempStr));
    errorCheck();
    Py_DECREF(pTempStr);
    return message;
}

/*
 * Convert a C string in the PostgreSQL server encoding to a Python
 * unicode object.	Reference ownership is passed to the caller.
 */
PyObject *
PyString_FromStringAndSize(const char *s, Py_ssize_t size)
{
    char	   *utf8string;
    PyObject   *o;

    utf8string = (char *) pg_do_encoding_conversion((unsigned char *) s,
                                                    strlen(s),
                                                    GetDatabaseEncoding(),
                                                    PG_UTF8);
    if (size < 0)
    {
        o = PyUnicode_FromString(utf8string);
    }
    else
    {
        o = PyUnicode_FromStringAndSize(utf8string, size);
    }
    if (utf8string != s)
        pfree(utf8string);

    return o;
}

PyObject *
PyString_FromString(const char *s)
{
    return PyString_FromStringAndSize(s, -1);
}

PGDLLEXPORT char *
PyString_AsString(PyObject *unicode)
{
    char	   *rv;
    PyObject   *o = PyUnicode_AsEncodedString(unicode, getPythonEncodingName(), NULL);
    errorCheck();
    rv = pstrdup(PyBytes_AsString(o));
    Py_XDECREF(o);
    return rv;
}

int
PyString_AsStringAndSize(PyObject *obj, char **buffer, Py_ssize_t *length)
{
    PyObject   *o;
    int			rv;
    char *tempbuffer;

    if (PyUnicode_Check(obj))
    {
        o = PyUnicode_AsEncodedString(obj, getPythonEncodingName(), NULL);
        errorCheck();
        rv = PyBytes_AsStringAndSize(o, &tempbuffer, length);
        *buffer = pstrdup(tempbuffer);
        Py_XDECREF(o);
        return rv;
    }
    return PyBytes_AsStringAndSize(obj, buffer, length);
}

/*
 * Utility function responsible for importing, and returning, a class by name
 *
 * Returns a new reference to the class.
 */
PyObject *
getClass(PyObject *className)
{
    PyObject   *p_multicorn = PyImport_ImportModule("multicorn"),
               *p_class = PyObject_CallMethod(p_multicorn, "get_class", "(O)",
                                              className);

    errorCheck();
    Py_DECREF(p_multicorn);
    return p_class;
}

void
appendBinaryStringInfoQuote(StringInfo buffer,
                            char *tempbuffer,
                            Py_ssize_t strlength,
                            bool need_quote)
{
    if (need_quote)
    {
        char	   *c;
        int			i;

        appendStringInfoChar(buffer, '"');
        for (c = tempbuffer, i = 0; i < strlength; ++i, ++c)
        {
            if (*c == '"')
            {
                appendBinaryStringInfo(buffer, "\\\"", 2);
            }
            else if (*c == '\\')
            {
                appendBinaryStringInfo(buffer, "\\\\", 2);
            }
            else
            {
                appendStringInfoChar(buffer, *c);
            }
        }
        appendStringInfoChar(buffer, '"');
    }
    else
    {
        appendBinaryStringInfo(buffer, tempbuffer, strlength);
    }
}

/* The function dumps a python string into a StringInfo buffer, but assuming
 * it's already within double quotes. Doubles quotes and backslashes are escaped.
 * This is to render keys and values within an HSTORE encoded as a string:
 * - key or value "b" becomes \"b\"
 * -              "b c" becomes \"b c\"
 * -              "b\"c" becomes \"b\\\"c\"
 * -              "b\\c" becomes \"b\\\\c\"
 */
void
hstoreEscapedString(PyObject *str, StringInfo buffer)
{
    char *tempbuffer;
    char *c;
    int i;
    Py_ssize_t strlength = 0;
    if (PyString_AsStringAndSize(str, &tempbuffer, &strlength) < 0)
    {
        ereport(WARNING,
                (errmsg("An error occured while decoding the column"),
                 errhint("You should maybe return unicode instead?")));
    } else {
        appendBinaryStringInfo(buffer, "\\\"", 2);
        for (c = tempbuffer, i = 0; i < strlength; ++i, ++c) {
            if (*c == '"') {
                appendBinaryStringInfo(buffer, "\\\\\\\"", 4);
            } else if (*c == '\\') {
                appendBinaryStringInfo(buffer, "\\\\\\\\", 4);
            } else {
                appendStringInfoChar(buffer, *c);
            }
        }
        appendBinaryStringInfo(buffer, "\\\"", 2);
    }
}

/*
 * Convert a list of Value nodes containing the column name as a string to a
 * pyset of python unicode strings.
 */
PyObject *
valuesToPySet(List *targetlist)
{
    PyObject   *result = PySet_New(0);
    ListCell   *lc;

    foreach(lc, targetlist)
    {
#if PG_VERSION_NUM < 150000
        Value	   *value = (Value *) lfirst(lc);
#else
        String	   *value = lfirst_node(String, lc);
#endif
        PyObject   *pyString = PyString_FromString(strVal(value));

        PySet_Add(result, pyString);
        Py_DECREF(pyString);
    }
    return result;
}

PyObject *
qualDefsToPyList(List *qual_list, ConversionInfo ** cinfos)
{
    ListCell   *lc;
    PyObject   *p_quals = PyList_New(0);

    foreach(lc, qual_list)
    {
        MulticornBaseQual *qual_def = (MulticornBaseQual *) lfirst(lc);

        if (qual_def->right_type == T_Const)
        {
            PyObject   *python_qual = qualdefToPython((MulticornConstQual *) qual_def, cinfos);

            if (python_qual != NULL)
            {
                PyList_Append(p_quals, python_qual);
                Py_DECREF(python_qual);
            }
        }
    }
    return p_quals;
}


/*
 * Same as getClass, but accepts a C-String argument instead of a python
 * string.
 *
 * Returns a new reference to the class.
 */
PyObject *
getClassString(const char *className)
{
    PyObject   *p_classname = PyString_FromString(className),
               *p_class = getClass(p_classname);

    Py_DECREF(p_classname);
    return p_class;
}


List *
getOptions(Oid foreigntableid)
{
    ForeignTable *f_table;
    ForeignServer *f_server;
    UserMapping *mapping;
    List	   *options;

    f_table = GetForeignTable(foreigntableid);
    f_server = GetForeignServer(f_table->serverid);

    options = NIL;
    options = list_concat(options, f_table->options);
    options = list_concat(options, f_server->options);
    /* An error might occur if no user mapping is defined. */
    /* In that case, just ignore it */
    mapping = multicorn_GetUserMapping(GetUserId(), f_table->serverid);
    if (mapping)
        options = list_concat(options, mapping->options);
    return options;
}

/*
 * Reimplementation of GetUserMapping, which returns NULL instead of throwing an
 * error when the mapping is not found.
 */
UserMapping *
multicorn_GetUserMapping(Oid userid, Oid serverid)
{
    Datum		datum;
    HeapTuple	tp;
    bool		isnull;
    UserMapping *um;

    tp = SearchSysCache2(USERMAPPINGUSERSERVER,
                         ObjectIdGetDatum(userid),
                         ObjectIdGetDatum(serverid));

    if (!HeapTupleIsValid(tp))
    {
        /* Not found for the specific user -- try PUBLIC */
        tp = SearchSysCache2(USERMAPPINGUSERSERVER,
                             ObjectIdGetDatum(InvalidOid),
                             ObjectIdGetDatum(serverid));
    }

    if (!HeapTupleIsValid(tp))
        return NULL;

    um = (UserMapping *) palloc(sizeof(UserMapping));
    um->userid = userid;
    um->serverid = serverid;

    /* Extract the umoptions */
    datum = SysCacheGetAttr(USERMAPPINGUSERSERVER,
                            tp,
                            Anum_pg_user_mapping_umoptions,
                            &isnull);
    if (isnull)
        um->options = NIL;
    else
        um->options = untransformRelOptions(datum);

    ReleaseSysCache(tp);

    return um;
}


/*
 * Collect and validate options.
 * Only one option is required "wrapper".
 *
 * Returns a new reference to a dictionary.
 *
 * */
PyObject *
optionsListToPyDict(List *options)
{
    ListCell   *lc;
    PyObject   *p_options_dict = PyDict_New();

    foreach(lc, options)
    {
        DefElem    *def = (DefElem *) lfirst(lc);
        PyObject   *pStr = PyString_FromString((char *) defGetString(def));

        PyDict_SetItemString(p_options_dict, def->defname, pStr);
        Py_DECREF(pStr);
    }
    return p_options_dict;
}


bool
compareOptions(List *options1, List *options2)
{
    ListCell   *lc1,
               *lc2;


    if (list_length(options1) != list_length(options2))
    {
        return false;
    }
    forboth(lc1, options1, lc2, options2)
    {
        DefElem    *def1 = (DefElem *) lfirst(lc1);
        DefElem    *def2 = (DefElem *) lfirst(lc2);

        if (def1 == NULL || def2 == NULL || strcmp(def1->defname, def2->defname) != 0)
        {
            return false;
        }
        if (strcmp(defGetString(def1), defGetString(def2)) != 0)
        {
            return false;
        }
    }
    return true;
}

void
getColumnsFromTable(TupleDesc desc, PyObject **p_columns, List **columns)
{
    PyObject   *columns_dict = *p_columns;
    List	   *columns_list = *columns;

    elog(DEBUG1, "Calling 'getColumnsFromTable'");
    if ((columns_dict != NULL) && (columns_list != NULL))
    {
        elog(WARNING, "columns_dict = %p, columns_list = %p", columns_dict, columns_list);
        return;
    }
    else
    {
        int			i;
        PyObject   *p_columnclass = getClassString("multicorn."
                                                   "ColumnDefinition"),
                   *p_collections = PyImport_ImportModule("collections"),
                   *p_dictclass = PyObject_GetAttrString(p_collections, "OrderedDict");

        columns_dict = PyObject_CallFunction(p_dictclass, "()");

        for (i = 0; i < desc->natts; i++)
        {
            Form_pg_attribute att = TupleDescAttr(desc, i);

            if (!att->attisdropped)
            {
                Oid			typOid = att->atttypid;

                char	   *key = NameStr(att->attname);
                int32		typmod = att->atttypmod;
                char	   *base_type = format_type_be(typOid);
                char	   *modded_type = format_type_with_typemod(typOid, typmod);
                List	   *options = GetForeignColumnOptions(att->attrelid,
                                                              att->attnum);
                PyObject   *p_options = optionsListToPyDict(options);
                PyObject   *column = PyObject_CallFunction(p_columnclass,
                                                           "(s,i,i,s,s,O)",
                                                           key,
                                                           typOid,
                                                           typmod,
                                                           modded_type,
                                                           base_type,
                                                           p_options);
                List	   *columnDef = NULL;

                errorCheck();
                elog(DEBUG1, "Adding column %s (%d, %s, %s)", key, typOid, base_type, modded_type);
                columnDef = lappend(columnDef, makeString(pstrdup(key)));
                columnDef = lappend(columnDef, makeConst(TYPEOID,
                                   -1, InvalidOid, 4, ObjectIdGetDatum(typOid), false, true));
                columnDef = lappend(columnDef, makeConst(INT4OID,
                                   -1, InvalidOid, 4, Int32GetDatum(typmod), false, true));
                columnDef = lappend(columnDef, options);
                columns_list = lappend(columns_list, columnDef);
                PyMapping_SetItemString(columns_dict, key, column);
                Py_DECREF(p_options);
                Py_DECREF(column);
            }
        }
        elog(DEBUG1, "Added all columns");
        Py_DECREF(p_columnclass);
        Py_DECREF(p_collections);
        Py_DECREF(p_dictclass);
        errorCheck();
        *p_columns = columns_dict;
        *columns = columns_list;
    }

}

bool
compareColumns(List *columns1, List *columns2)
{
    ListCell   *lc1,
               *lc2;

    if (columns1->length != columns2->length)
    {
        return false;
    }

    forboth(lc1, columns1, lc2, columns2)
    {
        List	   *coldef1 = lfirst(lc1);
        List	   *coldef2 = lfirst(lc2);
        ListCell   *cell1 = list_head(coldef1),
                   *cell2 = list_head(coldef2);

        /* Compare column name */
        if (strcmp(strVal(lfirst(cell1)), strVal(lfirst(cell2))) != 0)
        {
            return false;
        }
#if PG_VERSION_NUM >= 130000
        cell1 = lnext(coldef1, cell1);
        cell2 = lnext(coldef2, cell2);
#else
        cell1 = lnext(cell1);
        cell2 = lnext(cell2);
#endif
        /* Compare typoid */
        if (((Const *) (lfirst(cell1)))->constvalue != ((Const *) lfirst(cell2))->constvalue)
        {
            return false;
        }
#if PG_VERSION_NUM >= 130000
        cell1 = lnext(coldef1, cell1);
        cell2 = lnext(coldef2, cell2);
#else
        cell1 = lnext(cell1);
        cell2 = lnext(cell2);
#endif
        /* Compare typmod */
        if (((Const *) (lfirst(cell1)))->constvalue != ((Const *) lfirst(cell2))->constvalue)
        {
            return false;
        }
#if PG_VERSION_NUM >= 130000
        cell1 = lnext(coldef1, cell1);
        cell2 = lnext(coldef2, cell2);
#else
        cell1 = lnext(cell1);
        cell2 = lnext(cell2);
#endif
        /* Compare column options */
        if (!compareOptions(lfirst(cell1), lfirst(cell2)))
        {
            return false;
        }
    }
    return true;
}


CacheEntry *
getCacheEntry(Oid foreigntableid)
{
    /*
     * create a temporary context. If we have to (re)create the python
     * instance, it will be promoted to a cachememorycontext. Otherwise, it
     * will be freed before returning the instance
     */
    MemoryContext tempContext = AllocSetContextCreate(CurrentMemoryContext,
                                                  "multicorn temporary data",
                                                      ALLOCSET_SMALL_MINSIZE,
                                                      ALLOCSET_SMALL_INITSIZE,
                                                      ALLOCSET_SMALL_MAXSIZE),
                oldContext = MemoryContextSwitchTo(tempContext);
    CacheEntry *entry = NULL;
    bool		found = false;
    List	   *options = getOptions(foreigntableid);
    List	   *columns = NULL;
    PyObject   *p_columns = NULL;
    ForeignTable *ftable = GetForeignTable(foreigntableid);
    Relation	rel = RelationIdGetRelation(ftable->relid);
    TupleDesc	desc = rel->rd_att;
    bool		needInitialization = false;

    entry = hash_search(InstancesHash, &foreigntableid, HASH_ENTER,
                        &found);

    if (!found || entry->value == NULL)
    {
        entry->options = NULL;
        entry->columns = NULL;
        entry->cacheContext = NULL;
        entry->xact_depth = 0;
        needInitialization = true;
    }
    else
    {
        elog(DEBUG1, "Found table %d in cache", foreigntableid);
        /* Even if found, we have to check several things */
        if (!compareOptions(entry->options, options))
        {
            /* Options have changed, we must purge the cache. */
            elog(DEBUG1, "compareOptions => false");
            Py_XDECREF(entry->value);
            needInitialization = true;
        }
        else
        {
            /* Options have not changed, we should look at columns. */
            getColumnsFromTable(desc, &p_columns, &columns);
            if (!compareColumns(columns, entry->columns))
            {
                elog(DEBUG1, "compareColumns => false");
                Py_XDECREF(entry->value);
                needInitialization = true;
            }
            else
            {
                Py_XDECREF(p_columns);
            }
        }
    }
    if (needInitialization)
    {
        PyObject   *p_options = optionsListToPyDict(options),
                   *p_class = getClass(PyDict_GetItemString(p_options,
                                                            "wrapper")),
                   *p_instance;

        entry->value = NULL;
        getColumnsFromTable(desc, &p_columns, &columns);
        PyDict_DelItemString(p_options, "wrapper");
        p_instance = PyObject_CallFunction(p_class, "(O,O)", p_options,
                                           p_columns);
        errorCheck();
        /* Cleanup the old context, containing the old columns and options */
        /* values */
        if (entry->cacheContext != NULL)
        {
            MemoryContextDelete(entry->cacheContext);
        }
        /* Promote this tempcontext. */
        MemoryContextSetParent(tempContext, CacheMemoryContext);
        entry->cacheContext = tempContext;
        entry->options = options;
        entry->columns = columns;
        entry->xact_depth = 0;
        Py_DECREF(p_class);
        Py_DECREF(p_options);
        Py_DECREF(p_columns);
        errorCheck();
        entry->value = p_instance;
        MemoryContextSwitchTo(oldContext);
    }
    else
    {
        MemoryContextSwitchTo(oldContext);
        MemoryContextDelete(tempContext);
    }
    RelationClose(rel);

    /*
     * Start a new transaction or subtransaction if needed.
     */
    begin_remote_xact(entry);
    return entry;
}


/*
 * Returns the fdw_instance associated with the foreigntableid.
 *
 * For performance reasons, it is cached in hash table.
 */
PyObject *
getInstance(Oid foreigntableid)
{
    PyObject* retval = getCacheEntry(foreigntableid)->value;
    Py_INCREF(retval);
    return retval;
}


static void
begin_remote_xact(CacheEntry * entry)
{
    int			curlevel = GetCurrentTransactionNestLevel();
    PyObject   *rv;

    /* Start main transaction if we haven't yet */
    if (entry->xact_depth <= 0)
    {
        rv = PyObject_CallMethod(entry->value, "begin", "(i)", IsolationIsSerializable());
        Py_XDECREF(rv);
        errorCheck();
        entry->xact_depth = 1;
    }

    while (entry->xact_depth < curlevel)
    {
        entry->xact_depth++;
        rv = PyObject_CallMethod(entry->value, "sub_begin", "(i)", entry->xact_depth);
        Py_XDECREF(rv);
        errorCheck();
    }
}



/*
 * Returns the relation estimated size, in term of number of rows and width.
 * This is done by calling the getRelSize python method.
 *
 */
void
getRelSize(MulticornPlanState * state,
           PlannerInfo *root,
           double *rows,
           int *width)
{
    PyObject   *p_targets_set,
               *p_quals,
               *p_rows_and_width,
               *p_rows,
               *p_width,
               *p_startup_cost;

    p_targets_set = valuesToPySet(state->target_list);
    p_quals = qualDefsToPyList(state->qual_list, state->cinfos);
    elog(DEBUG1, "Calling 'get_rel_size'");
    p_rows_and_width = PyObject_CallMethod(state->fdw_instance, "get_rel_size",
                                           "(O,O)", p_quals, p_targets_set);
    errorCheck();
    Py_DECREF(p_targets_set);
    Py_DECREF(p_quals);
    if ((p_rows_and_width == Py_None) || PyTuple_Size(p_rows_and_width) != 2)
    {
        Py_DECREF(p_rows_and_width);
        elog(ERROR, "The get_rel_size python method should return a tuple of length 2");
    }
    p_rows = PyNumber_Long(PyTuple_GetItem(p_rows_and_width, 0));
    p_width = PyNumber_Long(PyTuple_GetItem(p_rows_and_width, 1));
    p_startup_cost = PyNumber_Long(
               PyObject_GetAttrString(state->fdw_instance, "_startup_cost"));
    *rows = PyLong_AsDouble(p_rows);
    elog(DEBUG1, "Got rows = %lf", *rows);
    *width = (int) PyLong_AsLong(p_width);
    elog(DEBUG1, "Got width = %d", *width);
    state->startupCost = (int) PyLong_AsLong(p_startup_cost);
    elog(DEBUG1, "Got startupCost = %d", state->startupCost);
    Py_DECREF(p_rows);
    Py_DECREF(p_width);
    Py_DECREF(p_rows_and_width);
}

PyObject *
qualdefToPython(MulticornConstQual * qualdef, ConversionInfo ** cinfos)
{
    int			arrayindex = qualdef->base.varattno - 1;
    char	   *operatorname = qualdef->base.opname;
    ConversionInfo *cinfo = cinfos[arrayindex];
    bool		is_array = qualdef->base.isArray,
                use_or = qualdef->base.useOr;
    Oid			typeoid = qualdef->base.typeoid;
    Datum		value = qualdef->value;
    PyObject   *p_value;

    if (qualdef->isnull)
    {
        p_value = Py_None;
        Py_INCREF(Py_None);
    }
    else
    {
        if (typeoid == InvalidOid)
        {
            typeoid = cinfo->atttypoid;
        }
        p_value = datumToPython(value, typeoid, cinfo);
        if (p_value == NULL)
        {
            return NULL;
        }
    }

    if (typeoid <= 0)
    {
        typeoid = cinfo->atttypoid;
    }

    return pythonQual(operatorname, p_value,
                      cinfo, is_array, use_or, typeoid);
}


PyObject *
pythonQual(char *operatorname,
           PyObject *value,
           ConversionInfo * cinfo,
           bool is_array,
           bool use_or,
           Oid typeoid)
{
    PyObject   *qualClass = getClassString("multicorn.Qual"),
               *qualInstance,
               *p_operatorname,
               *operator,
               *columnName;

    p_operatorname = PyUnicode_Decode(operatorname, strlen(operatorname), getPythonEncodingName(), NULL);
    errorCheck();
    if (is_array)
    {
        PyObject   *arrayOpType;


        if (use_or)
        {
            arrayOpType = Py_True;
        }
        else
        {
            arrayOpType = Py_False;
        }
        operator = Py_BuildValue("(O, O)", p_operatorname, arrayOpType);
        Py_DECREF(p_operatorname);
        errorCheck();
    }
    else
    {
        operator = p_operatorname;
    }

    columnName = PyUnicode_Decode(cinfo->attrname, strlen(cinfo->attrname), getPythonEncodingName(), NULL);
    qualInstance = PyObject_CallFunction(qualClass, "(O,O,O)",
                                         columnName,
                                         operator,
                                         value);
    errorCheck();
    Py_DECREF(value);
    Py_DECREF(operator);
    Py_DECREF(qualClass);
    Py_DECREF(columnName);
    return qualInstance;
}

PyObject  *
getSortKey(MulticornDeparsedSortGroup *key)
{
    PyObject *SortKeyClass = getClassString("multicorn.SortKey"),
             *SortKeyInstance,
             *p_attname,
             *p_reversed,
             *p_nulls_first,
             *p_collate;

    p_attname = PyUnicode_Decode(NameStr(*(key->attname)), strlen(NameStr(*(key->attname))), getPythonEncodingName(), NULL);
    if (key->reversed)
        p_reversed = Py_True;
    else
        p_reversed = Py_False;
    if (key->nulls_first)
        p_nulls_first = Py_True;
    else
        p_nulls_first = Py_False;
    if(key->collate == NULL){
        p_collate = Py_None;
        Py_INCREF(p_collate);
    }
    else
        p_collate = PyUnicode_Decode(NameStr(*(key->collate)), strlen(NameStr(*(key->collate))), getPythonEncodingName(), NULL);
    SortKeyInstance = PyObject_CallFunction(SortKeyClass, "(O,i,O,O,O)",
            p_attname,
            key->attnum,
            p_reversed,
            p_nulls_first,
            p_collate);
    errorCheck();
    Py_DECREF(p_attname);
    Py_DECREF(p_collate);
    Py_DECREF(SortKeyClass);
    return SortKeyInstance;
}

MulticornDeparsedSortGroup *
getDeparsedSortGroup(PyObject *sortKey)
{
    MulticornDeparsedSortGroup *md = palloc0(sizeof(MulticornDeparsedSortGroup));
    PyObject * p_temp;
    p_temp = PyObject_GetAttrString(sortKey, "attname");
    md->attname = (Name) strndup((const char *)PyUnicode_1BYTE_DATA(p_temp), PyUnicode_GET_LENGTH(p_temp));
    Py_DECREF(p_temp);
    p_temp = PyObject_GetAttrString(sortKey, "attnum");
    md->attnum = (int) PyLong_AsLong(p_temp);
    Py_DECREF(p_temp);
    p_temp = PyObject_GetAttrString(sortKey, "is_reversed");
    md->reversed = PyObject_IsTrue(p_temp);
    Py_DECREF(p_temp);
    p_temp = PyObject_GetAttrString(sortKey, "nulls_first");
    md->nulls_first = PyObject_IsTrue(PyObject_GetAttrString(sortKey, "nulls_first"));
    Py_DECREF(p_temp);
    p_temp = PyObject_GetAttrString(sortKey, "collate");
    if(p_temp == Py_None)
        md->collate = 0;
    else
        md->collate = (Name) strndup((const char *)PyUnicode_1BYTE_DATA(p_temp), PyUnicode_GET_LENGTH(p_temp));
    Py_DECREF(p_temp);
    return md;
}

/* Helper to copy a non-null-terminated string */
static char *
pstrndup(const char *src, size_t len)
{
    char *result = palloc(len + 1);
    memcpy(result, src, len);
    result[len] = '\0';
    return result;
}

/*
 * get_http_headers
 *
 * Reads the session variable "my.raw_http_headers", which is expected to contain a JSON string
 * representing an array of objects. Each object must have string fields "header" and "value".
 * The function converts that JSON string to a JSONB Datum (using jsonb_in), verifies that the
 * root is an array, then iterates over each object, converting the "header" and "value" strings
 * to Python Unicode objects and inserting them into a Python dictionary (mapping header to value).
 * In any error condition (e.g., missing field, wrong type), a warning is logged and the function
 * returns NULL.
 */
static PyObject *
get_http_headers(void)
{
    /* Retrieve the GUC value */
    const char *headers_value = GetConfigOptionByName("my.raw_http_headers", false, false);
    if (headers_value == NULL || headers_value[0] == '\0')
    {
        elog(WARNING, "my.raw_http_headers is not set");
        return NULL;
    }

    /*
     * Convert the JSON string into a JSONB Datum.
     * Note: Uses the built‑in jsonb_in function.
     */
    Datum jsonb_datum = DirectFunctionCall1(jsonb_in, CStringGetDatum(headers_value));
    Jsonb *jb = DatumGetJsonbP(jsonb_datum);
    if (JB_ROOT_IS_SCALAR(jb))
    {
        elog(WARNING, "Expected JSONB container for my.raw_http_headers, got a scalar");
        return NULL;
    }

    if (!JB_ROOT_IS_ARRAY(jb))
    {
        elog(WARNING, "Expected JSONB array for my.raw_http_headers, but got something else");
        return NULL;
    }

    /* For debugging, you could log internal header values if needed. */
    JsonbContainer *container = (JsonbContainer *) VARDATA_ANY(jb);
    /* Initialize a JsonbIterator */
    JsonbIterator *it = JsonbIteratorInit(container);
    JsonbValue v;
    int r;

    /* Expect the JSON to be an array. The first token should be WJB_BEGIN_ARRAY. */
    r = JsonbIteratorNext(&it, &v, false);
    if (r != WJB_BEGIN_ARRAY)
    {
        elog(WARNING, "Expected JSON array in my.raw_http_headers");
        return NULL;
    }

    /* Create a new Python dictionary */
    PyObject *py_dict = PyDict_New();
    if (!py_dict)
    {
        elog(WARNING, "Failed to create Python dict");
        return NULL;
    }

    /* Iterate through each element of the JSON array */
    while ((r = JsonbIteratorNext(&it, &v, false)) != 0)
    {
        if (r == WJB_END_ARRAY)
            break;

        if (r == WJB_BEGIN_OBJECT)
        {
            char *header = NULL;
            char *value  = NULL;

            /* Iterate through the keys/values in the object */
            while ((r = JsonbIteratorNext(&it, &v, false)) != 0)
            {
                if (r == WJB_END_OBJECT)
                    break;

                if (r == WJB_KEY)
                {
                    /* Get the key name */
                    char *key = v.val.string.val;
                    int key_length = v.val.string.len;

                    /* The next token should be the value */
                    r = JsonbIteratorNext(&it, &v, false);
                    if (r != WJB_VALUE)
                    {
                        elog(WARNING, "Expected a value for key '%.*s'", key_length, key);
                        Py_DECREF(py_dict);
                        return NULL;
                    }

                    if (v.type != jbvString)
                    {
                        elog(WARNING, "Expected string value for key '%.*s'", key_length, key);
                        Py_DECREF(py_dict);
                        return NULL;
                    }

                    /* Save the value based on the key.
                     * Since the token string is not null-terminated, we compare both length and content.
                     */
                    if (key_length == strlen("header") && strncmp(key, "header", key_length) == 0)
                        header = pstrndup(v.val.string.val, v.val.string.len);
                    else if (key_length == strlen("value") && strncmp(key, "value", key_length) == 0)
                        value = pstrndup(v.val.string.val, v.val.string.len);
                }
            } /* End of inner while for object */

            /* Ensure both "header" and "value" were provided */
            if (!header || !value)
            {
                elog(WARNING, "Missing field 'header' or 'value' in one of the JSON objects");
                Py_DECREF(py_dict);
                if (header)
                    pfree(header);
                if (value)
                    pfree(value);
                return NULL;
            }

            /* Convert C strings to Python Unicode objects */
            PyObject *py_key = PyUnicode_FromString(header);
            PyObject *py_value = PyUnicode_FromString(value);
            if (!py_key || !py_value)
            {
                elog(WARNING, "Failed to create Python string objects");
                Py_XDECREF(py_key);
                Py_XDECREF(py_value);
                Py_DECREF(py_dict);
                pfree(header);
                pfree(value);
                return NULL;
            }
            if (PyDict_SetItem(py_dict, py_key, py_value) != 0)
            {
                elog(WARNING, "Failed to insert item into Python dict");
                Py_DECREF(py_key);
                Py_DECREF(py_value);
                Py_DECREF(py_dict);
                pfree(header);
                pfree(value);
                return NULL;
            }
            Py_DECREF(py_key);
            Py_DECREF(py_value);
            pfree(header);
            pfree(value);
        }
        else
        {
            /* Skip any tokens that are not the start of an object */
            continue;
        }
    } /* End while over array */

    return py_dict;
}


/*
 * get_scopes
 *
 * Reads the session variable "my.raw_scopes", which is expected to contain a JSON string
 * representing an array of strings, and converts it into a Python list of Unicode strings.
 *
 * The function converts the JSON string to a JSONB Datum (using jsonb_in), verifies that the
 * root of the JSONB value is an array, then iterates over its elements. Each element must
 * be a string, and is converted using PyUnicode_FromStringAndSize. In any error condition,
 * a warning is issued using elog and the function returns NULL.
 */
static PyObject *
get_scopes(void)
{
    /* Retrieve the GUC value */
    const char *scopes_value = GetConfigOptionByName("my.raw_scopes", false, false);
    if (scopes_value == NULL || scopes_value[0] == '\0')
    {
        elog(WARNING, "my.raw_scopes is not set");
        return NULL;
    }

    /*
     * Convert the JSON string into a JSONB Datum using jsonb_in.
     */
    Datum jsonb_datum = DirectFunctionCall1(jsonb_in, CStringGetDatum(scopes_value));
    Jsonb *jb = DatumGetJsonbP(jsonb_datum);
    if (JB_ROOT_IS_SCALAR(jb))
    {
        elog(WARNING, "Expected JSONB container for my.raw_scopes, got a scalar");
        return NULL;
    }

    if (!JB_ROOT_IS_ARRAY(jb))
    {
        elog(WARNING, "Expected JSONB array for my.raw_scopes, but got something else");
        return NULL;
    }

    /* Get the container pointer */
    JsonbContainer *container = (JsonbContainer *) VARDATA_ANY(jb);
    /* Initialize a JsonbIterator from the container */
    JsonbIterator *it = JsonbIteratorInit(container);
    JsonbValue v;
    int r;

    /* Expect the first token to be WJB_BEGIN_ARRAY */
    r = JsonbIteratorNext(&it, &v, false);
    if (r != WJB_BEGIN_ARRAY)
    {
        elog(WARNING, "Expected JSON array in my.raw_scopes");
        return NULL;
    }

    /* Create an empty Python list */
    PyObject *py_list = PyList_New(0);
    if (!py_list)
    {
        elog(WARNING, "Failed to create Python list");
        return NULL;
    }

    /* Iterate through each element in the JSON array */
    while ((r = JsonbIteratorNext(&it, &v, false)) != 0)
    {
        if (r == WJB_END_ARRAY)
            break;

        /* Accept both WJB_VALUE and WJB_ELEM tokens for array elements */
        if (r != WJB_VALUE && r != WJB_ELEM)
        {
            elog(WARNING, "Expected a value in my.raw_scopes array");
            Py_DECREF(py_list);
            return NULL;
        }

        if (v.type != jbvString)
        {
            elog(WARNING, "Expected string element in my.raw_scopes array");
            Py_DECREF(py_list);
            return NULL;
        }

        /* Create a Python Unicode string from the token.
         * Since the token string is not null-terminated, use PyUnicode_FromStringAndSize.
         */
        PyObject *py_str = PyUnicode_FromStringAndSize(v.val.string.val, v.val.string.len);
        if (!py_str)
        {
            elog(WARNING, "Failed to create Python string from my.raw_scopes element");
            Py_DECREF(py_list);
            return NULL;
        }

        if (PyList_Append(py_list, py_str) != 0)
        {
            elog(WARNING, "Failed to append Python string to list");
            Py_DECREF(py_str);
            Py_DECREF(py_list);
            return NULL;
        }
        Py_DECREF(py_str);
    }

    return py_list;
}

/*
 * Execute the query in the python fdw, and returns an iterator.
 */
PyObject *
execute(ForeignScanState *node, ExplainState *es)
{
    MulticornExecState *state = node->fdw_state;
    PyObject   *p_targets_set,
               *p_quals = PyList_New(0),
               *p_pathkeys = PyList_New(0),
               *p_iterable,
               *p_method;
    ListCell   *lc;

    ExprContext *econtext = node->ss.ps.ps_ExprContext;

    foreach(lc, state->qual_list)
    {
        MulticornBaseQual *qual = lfirst(lc);
        MulticornConstQual *newqual = NULL;
        bool		isNull = true;
        ExprState  *expr_state = NULL;

        switch (qual->right_type)
        {
            case T_Param:
                expr_state = ExecInitExpr(((MulticornParamQual *) qual)->expr,
                                          (PlanState *) node);
                newqual = palloc0(sizeof(MulticornConstQual));
                newqual->base.right_type = T_Const;
                newqual->base.varattno = qual->varattno;
                newqual->base.opname = qual->opname;
                newqual->base.isArray = qual->isArray;
                newqual->base.useOr = qual->useOr;

                // Don't attempt to evaluate the expression if we're running an EXPLAIN
                if (es == NULL)
                {
                    expr_state = ExecInitExpr(((MulticornParamQual *) qual)->expr,
                                            (PlanState *) node);
                    #if PG_VERSION_NUM >= 100000
                    newqual->value = ExecEvalExpr(expr_state, econtext, &isNull);
                    #else
                    newqual->value = ExecEvalExpr(expr_state, econtext, &isNull, NULL);
                    #endif
                }
                newqual->base.typeoid = ((MulticornBaseQual *) qual)->typeoid;
                newqual->isnull = isNull;
                break;
            case T_Const:
                newqual = (MulticornConstQual *) qual;
                break;
            default:
                break;
        }
        if (newqual != NULL)
        {
            PyObject   *python_qual = qualdefToPython((MulticornConstQual *) newqual, state->cinfos);

            if (python_qual != NULL)
            {
                PyList_Append(p_quals, python_qual);
                Py_DECREF(python_qual);
            }
        }
    }
    /* Transform every object to a suitable python representation */
    p_targets_set = valuesToPySet(state->target_list);

    foreach(lc, state->pathkeys)
    {
        MulticornDeparsedSortGroup *pathkey = (MulticornDeparsedSortGroup *) lfirst(lc);
        PyObject *python_sortkey = getSortKey(pathkey);
        PyList_Append(p_pathkeys, python_sortkey);
        Py_DECREF(python_sortkey);
    }
    {
        PyObject * args,
                 * kwargs = PyDict_New();
        if(PyList_Size(p_pathkeys) > 0){
            PyDict_SetItemString(kwargs, "sortkeys", p_pathkeys);
        }
        /* Set the limit optional argument if there is a LIMIT clause. */
        if(state->limit != -1) {
            PyDict_SetItemString(kwargs, "limit", PyLong_FromLongLong(state->limit));
        }

        PyObject* scopes = get_scopes();
        if (scopes) {
            PyDict_SetItemString(kwargs, "scopes", scopes);
        }

        PyObject* http_headers = get_http_headers();
        if (http_headers) {
            PyDict_SetItemString(kwargs, "http_headers", http_headers);
        }

        if(es != NULL){
            PyObject * verbose;
            if(es->verbose){
                verbose = Py_True;
            } else {
                verbose = Py_False;
            }
            p_method = PyObject_GetAttrString(state->fdw_instance, "explain");
            args = PyTuple_Pack(2, p_quals, p_targets_set);
            PyDict_SetItemString(kwargs, "verbose", verbose);
            errorCheck();
        } else {
            /* For execution, pass back the plan identifier. This allows the plugin to distinguish between different executions of the same plan node. */
            PyDict_SetItemString(kwargs, "planid", PyString_FromString(state->plan_id));

            p_method = PyObject_GetAttrString(state->fdw_instance, "execute");
            errorCheck();
            args = PyTuple_Pack(2, p_quals, p_targets_set);
            errorCheck();
        }
        p_iterable = PyObject_Call(p_method, args, kwargs);
        errorCheck();
        if (http_headers) {
            Py_DECREF(http_headers);
        }
        if (scopes) {
            Py_DECREF(scopes);
        }
        Py_DECREF(p_method);
        Py_DECREF(args);
        Py_DECREF(kwargs);
    }

    errorCheck();
    if (p_iterable == Py_None){
        state->p_iterator = p_iterable;
    }
    else
    {
        state->p_iterator = PyObject_GetIter(p_iterable);
    }
    Py_DECREF(p_quals);
    Py_DECREF(p_targets_set);
    Py_DECREF(p_pathkeys);
    Py_DECREF(p_iterable);
    errorCheck();
    return state->p_iterator;
}

void
pynumberToCString(PyObject *pyobject, StringInfo buffer,
                  ConversionInfo * cinfo)
{
    PyObject   *pTempStr;
    char	   *tempbuffer;
    Py_ssize_t	strlength = 0;

    pTempStr = PyObject_Str(pyobject);
    PyString_AsStringAndSize(pTempStr, &tempbuffer, &strlength);
    appendBinaryStringInfo(buffer, tempbuffer, strlength);
    Py_DECREF(pTempStr);
}

void
pyunicodeToCString(PyObject *pyobject, StringInfo buffer,
                   ConversionInfo * cinfo)
{
    char	   *tempbuffer;
    Py_ssize_t	strlength = 0;
    PyObject   *pTempStr;
    pTempStr = PyUnicode_AsEncodedString(pyobject, getPythonEncodingName(), NULL);
    errorCheck();
    PyBytes_AsStringAndSize(pTempStr, &tempbuffer, &strlength);
    appendBinaryStringInfoQuote(buffer, tempbuffer, strlength, cinfo->need_quote);
    Py_DECREF(pTempStr);
}

void
pystringToCString(PyObject *pyobject, StringInfo buffer,
                  ConversionInfo * cinfo)
{
    char	   *tempbuffer;
    Py_ssize_t	strlength = 0;

    if (PyString_AsStringAndSize(pyobject, &tempbuffer, &strlength) < 0)
    {
        ereport(WARNING,
                (errmsg("An error occured while decoding the %s column",
                        cinfo->attrname),
                 errhint("You should maybe return unicode instead?")));
    }
    appendBinaryStringInfoQuote(buffer, tempbuffer, strlength, cinfo->need_quote);
}

void
pysequenceToCString(PyObject *pyobject, StringInfo buffer,
                    ConversionInfo * cinfo)
{
    /* Its an array */
    Py_ssize_t	i,
                size = PySequence_Size(pyobject);
    PyObject   *p_item;
    int			previous_dims = cinfo->attndims,
                previous_needquote = cinfo->need_quote;

    if (cinfo->attndims == 0)
    {
        /* We are not supposed to be converted to an array. */
        pyunknownToCstring(pyobject, buffer, cinfo);
        return;
    }
    if (cinfo->atttypoid == hstore_array_oid) {
        /* Arrays of HSTORE aren't formatted like regular arrays */
        hstoreArrayToCString(pyobject, size, buffer);
    } else {
        /* Arrays are formatted as comma-separated list of items */
        appendStringInfoChar(buffer, '{');
        /* We are an array, so we need to quote stuff */
        cinfo->need_quote = true;
        cinfo->attndims = cinfo->attndims - 1;
        for (i = 0; i < size; i++)
        {
            ConversionInfo innerInfo = *cinfo;
            p_item = PySequence_GetItem(pyobject, i);
            if (cinfo->atttypoid == JSONARRAYOID) innerInfo.atttypoid = JSONOID;
            else if (cinfo->atttypoid == JSONBARRAYOID) innerInfo.atttypoid = JSONBOID;
            // else fingers crossed
            pyobjectToCString(p_item, buffer, &innerInfo);
            Py_DECREF(p_item);
            if (i != size - 1)
            {
                appendBinaryStringInfo(buffer, ", ", 2);
            }
        }
        appendStringInfoChar(buffer, '}');
    }
    cinfo->attndims = previous_dims;
    cinfo->need_quote = previous_needquote;
}

void
pymappingToCString(PyObject *pyobject, StringInfo buffer,
                   ConversionInfo * cinfo)
{
    PyObject   *items = PyMapping_Items(pyobject);
    PyObject   *current_tuple;
    PyObject   *value;
    Py_ssize_t	i;
    Py_ssize_t	size = PyList_Size(items);
    bool		need_quote = cinfo->need_quote;

    cinfo->need_quote = true;
    for (i = 0; i < size; i++)
    {
        current_tuple = PySequence_GetItem(items, i);
        pyobjectToCString(PyTuple_GetItem(current_tuple, 0),
                          buffer, cinfo);
        appendBinaryStringInfo(buffer, "=>", 2);
        value = PyTuple_GetItem(current_tuple, 1);
        if (value == Py_None)
        {
            appendBinaryStringInfo(buffer, "NULL", 4);
        }
        else
        {
            pyobjectToCString(value, buffer, cinfo);
        }
        if (i != size - 1)
        {
            appendBinaryStringInfo(buffer, ", ", 2);
        }
        Py_DECREF(current_tuple);
    }
    Py_DECREF(items);
    cinfo->need_quote = need_quote;
}

/* Function to render an HSTORE ARRAY as a string (used to
 * load HSTORE arrays into Postgres. Each inner HSTORE is
 * wrapped into double quotes. Key and value strings
 * have to be escaped */
void
hstoreArrayToCString(PyObject *array, Py_ssize_t n_items, StringInfo buffer)
{
    Py_ssize_t	i;
    appendStringInfoChar(buffer, '{');
    for (i = 0; i < n_items; i++) {
        PyObject   *hstore = PySequence_GetItem(array, i);
        PyObject   *hstore_items = PyMapping_Items(hstore);
        Py_ssize_t	size = PyList_Size(hstore_items);
        Py_ssize_t  j;
        appendStringInfoChar(buffer, '"');
        for (j = 0; j < size; j++)
        {
            PyObject* current_tuple = PySequence_GetItem(hstore_items, j);
            PyObject* key = PyTuple_GetItem(current_tuple, 0);
            PyObject* value = PyTuple_GetItem(current_tuple, 1);
            hstoreEscapedString(key, buffer);
            appendBinaryStringInfo(buffer, "=>", 2);
            if (value == Py_None)
            {
                appendBinaryStringInfo(buffer, "NULL", 4);
            }
            else
            {
                hstoreEscapedString(value, buffer);
            }
            if (j != size - 1)
            {
                appendBinaryStringInfo(buffer, ", ", 2);
            }
            Py_DECREF(key);
            Py_DECREF(value);
            Py_DECREF(current_tuple);
        }
        Py_DECREF(hstore_items);
        appendStringInfoChar(buffer, '"');

        if (i != n_items - 1)
        {
            appendBinaryStringInfo(buffer, ", ", 2);
        }
    }
    appendStringInfoChar(buffer, '}');
}

void
pydateToCString(PyObject *pyobject, StringInfo buffer,
                ConversionInfo * cinfo)
{
    char	   *tempbuffer;
    Py_ssize_t	strlength = 0;
    PyObject   *formatted_date;

    formatted_date = PyObject_CallMethod(pyobject, "isoformat", "()");
    PyString_AsStringAndSize(formatted_date, &tempbuffer, &strlength);
    appendBinaryStringInfo(buffer, tempbuffer, strlength);
    Py_DECREF(formatted_date);
}

void
pytimeToCString(PyObject *pyobject, StringInfo buffer,
                ConversionInfo * cinfo)
{
    char	   *tempbuffer;
    Py_ssize_t	strlength = 0;
    PyObject   *formatted_time;

    formatted_time = PyObject_CallMethod(pyobject, "isoformat", "()");
    PyString_AsStringAndSize(formatted_time, &tempbuffer, &strlength);
    appendBinaryStringInfo(buffer, tempbuffer, strlength);
    Py_DECREF(formatted_time);
}


void
pyobjectToCString(PyObject *pyobject, StringInfo buffer,
                  ConversionInfo * cinfo)
{
    if (pyobject == NULL || pyobject == Py_None)
    {
        elog(DEBUG1, "Importing NULL (OID=%d)", cinfo->atttypoid);
        appendBinaryStringInfo(buffer, "NULL", 4);
        return;
    }
    if (cinfo->atttypoid == JSONOID || cinfo->atttypoid == JSONBOID) {
        elog(DEBUG1, "Importing Python object as JSON (OID=%d)", cinfo->atttypoid);
        PyObject *multicorn_das = PyImport_ImportModule("multicorn_das");
        PyObject *p_to_json = PyObject_GetAttrString(multicorn_das, "multicorn_serialize_as_json");
        errorCheck();
        PyObject *s = PyObject_CallFunction(p_to_json, "O", pyobject);
        Py_DECREF(multicorn_das);
        Py_DECREF(p_to_json);
        if (PyErr_Occurred()) {
            PyErr_Print();  // Print the exception traceback to stderr (log)
            elog(ERROR, "Couldn't serialize Python object to JSON");
        }
        pyunicodeToCString(s, buffer, cinfo);
        Py_DECREF(s);
        return;
    }
    if (cinfo->atttypoid == INTERVALOID) {
        elog(DEBUG1, "Importing Python interval (OID=%d)", cinfo->atttypoid);
        pyunicodeToCString(pyobject, buffer, cinfo);
        return;
    }
    if (PyNumber_Check(pyobject))
    {
        elog(DEBUG1, "Importing Python number (OID=%d)", cinfo->atttypoid);
        pynumberToCString(pyobject, buffer, cinfo);
        return;
    }
    if (PyUnicode_Check(pyobject))
    {
        elog(DEBUG1, "Importing Python unicode string (OID=%d)", cinfo->atttypoid);
        pyunicodeToCString(pyobject, buffer, cinfo);
        return;
    }
    if (PyBytes_Check(pyobject))
    {
        elog(DEBUG1, "Importing Python bytes (OID=%d)", cinfo->atttypoid);
        pystringToCString(pyobject, buffer, cinfo);
        return;
    }
    if (PySequence_Check(pyobject))
    {
        elog(DEBUG1, "Importing Python sequence (OID=%d)", cinfo->atttypoid);
        pysequenceToCString(pyobject, buffer, cinfo);
        return;
    }
    if (PyMapping_Check(pyobject))
    {
        elog(DEBUG1, "Importing Python map (OID=%d)", cinfo->atttypoid);
        pymappingToCString(pyobject, buffer, cinfo);
        return;
    }
    PyDateTime_IMPORT;
    if (PyDate_Check(pyobject))
    {
        elog(DEBUG1, "Importing Python date (OID=%d)", cinfo->atttypoid);
        pydateToCString(pyobject, buffer, cinfo);
        return;
    }
    if (PyTime_Check(pyobject))
    {
        elog(DEBUG1, "Importing Python time (OID=%d)", cinfo->atttypoid);
        pytimeToCString(pyobject, buffer, cinfo);
        return;
    }
    elog(WARNING, "Unexpected type OID=%d, trying generic data import", cinfo->atttypoid);
    pyunknownToCstring(pyobject, buffer, cinfo);
}

void
pyunknownToCstring(PyObject *pyobject, StringInfo buffer,
                   ConversionInfo * cinfo)
{
    PyObject   *pTempStr = PyObject_Str(pyobject);
    char	   *tempbuffer;
    Py_ssize_t	strlength;

    PyString_AsStringAndSize(pTempStr, &tempbuffer, &strlength);
    errorCheck();
    appendBinaryStringInfoQuote(buffer, tempbuffer, strlength, cinfo->need_quote);
    Py_DECREF(pTempStr);
    return;
}

void
pythonDictToTuple(PyObject *p_value,
                  TupleTableSlot *slot,
                  ConversionInfo ** cinfos,
                  StringInfo buffer)
{
    int			i;
    PyObject   *p_object;
    Datum	   *values = slot->tts_values;
    bool	   *nulls = slot->tts_isnull;

    for (i = 0; i < slot->tts_tupleDescriptor->natts; i++)
    {
        char	   *key;
        Form_pg_attribute attr = TupleDescAttr(slot->tts_tupleDescriptor,i);
        AttrNumber	cinfo_idx = attr->attnum - 1;

        if (cinfos[cinfo_idx] == NULL)
        {
            continue;
        }
        key = cinfos[cinfo_idx]->attrname;
        p_object = PyMapping_GetItemString(p_value, key);
        if (p_object != NULL && p_object != Py_None)
        {
            resetStringInfo(buffer);
            values[i] = pyobjectToDatum(p_object,
                                        buffer,
                                        cinfos[cinfo_idx]);
            if (buffer->data == NULL)
            {
                nulls[i] = true;
            }
            else
            {
                nulls[i] = false;
            }
        }
        else
        {
            /* "KeyError", doesnt matter. */
            PyErr_Clear();
            values[i] = (Datum) NULL;
            nulls[i] = true;
        }
        Py_XDECREF(p_object);
    }
}

void
pythonSequenceToTuple(PyObject *p_value,
                      TupleTableSlot *slot,
                      ConversionInfo ** cinfos,
                      StringInfo buffer)
{
    int			i,
                j;
    Datum	   *values = slot->tts_values;
    bool	   *nulls = slot->tts_isnull;

    for (i = 0, j = 0; i < slot->tts_tupleDescriptor->natts; i++)
    {
        PyObject   *p_object;
        Form_pg_attribute attr = TupleDescAttr(slot->tts_tupleDescriptor,i);
        AttrNumber	cinfo_idx = attr->attnum - 1;

        if (cinfos[cinfo_idx] == NULL)
        {
            continue;
        }
        p_object = PySequence_GetItem(p_value, j);
        if(p_object == NULL || p_object == Py_None){
            nulls[i] = true;
            values[i] = 0;
        }
        else
        {
            resetStringInfo(buffer);
            values[i] = pyobjectToDatum(p_object, buffer,
                                        cinfos[cinfo_idx]);
            if (buffer->data == NULL)
            {
                nulls[i] = true;
            }
            else
            {
                nulls[i] = false;
            }
        }
        errorCheck();
        Py_DECREF(p_object);
        j++;
    }
}

/*
 * Convert a python result (a sequence or a dictionary) to a tupletableslot.
 */
void
pythonResultToTuple(PyObject *p_value,
                    TupleTableSlot *slot,
                    ConversionInfo ** cinfos,
                    StringInfo buffer)
{
    if (PySequence_Check(p_value))
    {
        pythonSequenceToTuple(p_value, slot, cinfos, buffer);
    }
    else
    {

        if (PyMapping_Check(p_value))
        {
            pythonDictToTuple(p_value, slot, cinfos, buffer);
        }
        else
        {
            elog(ERROR, "Cannot transform anything else than mappings and"
                 "sequences to rows");
        }
    }
}

Datum
pyobjectToDatum(PyObject *object, StringInfo buffer,
                ConversionInfo * cinfo)
{
    Datum		value = 0;

    pyobjectToCString(object, buffer,
                      cinfo);

    if (buffer->len >= 0)
    {

        if (cinfo->atttypoid == BYTEAOID || cinfo->atttypoid == TEXTOID ||
            cinfo->atttypoid == VARCHAROID)
        {
            /*
             * Special case, since the value is already a byte string.
             */
            value = PointerGetDatum(cstring_to_text_with_len(buffer->data,
                                                             buffer->len));
        }
        else
        {
            value = InputFunctionCall(cinfo->attinfunc,
                                      buffer->data,
                                      cinfo->attioparam,
                                      cinfo->atttypmod);
        }
    }
    return value;
}

PyObject *
datumStringToPython(Datum datum, ConversionInfo * cinfo)
{
    char	   *temp;
    ssize_t		size;
    PyObject   *result;

    temp = datum == 0 ? "?" : TextDatumGetCString(datum);
    size = strlen(temp);
    result = PyUnicode_Decode(temp, size, getPythonEncodingName(), NULL);
    return result;
}

static PyObject *
datumBlankPaddedStringToPython(Datum datum, ConversionInfo * cinfo)
{
    char	   *temp;
    ssize_t		size;
    PyObject   *result;

    temp = datum == 0 ? "?" : TextDatumGetCString(datum);
    size = strlen(temp);
    size = bpchartruelen(temp, size);
    result = PyUnicode_Decode(temp, size, getPythonEncodingName(), NULL);
    return result;
}

static PyObject *
datumUnknownToPython(Datum datum, ConversionInfo * cinfo, Oid type)
{
    char	   *temp;
    ssize_t		size;
    PyObject   *result;
    Oid			outfuncoid;
    bool		isvarlena;
    FmgrInfo   *fmout = palloc0(sizeof(FmgrInfo));

    getTypeOutputInfo(type, &outfuncoid, &isvarlena);
    fmgr_info(outfuncoid, fmout);
    temp = OutputFunctionCall(fmout, datum);
    size = strlen(temp);
    result = PyUnicode_Decode(temp, size, getPythonEncodingName(), NULL);
    pfree(fmout);
    return result;
}

static PyObject *
datumFloat4ToPython(Datum datum, ConversionInfo * cinfo)
{
    float4 float4Value = DatumGetFloat4(datum);
    return PyFloat_FromDouble(float4Value);
}

static PyObject *
datumFloat8ToPython(Datum datum, ConversionInfo * cinfo)
{
    float8 float8Value = DatumGetFloat8(datum);
    return PyFloat_FromDouble(float8Value);
}

static PyObject *
datumDateToPython(Datum datum, ConversionInfo * cinfo)
{
    struct pg_tm *pg_tm_value = palloc(sizeof(struct pg_tm));
    PyObject   *result;
    fsec_t		fsec;

    PyDateTime_IMPORT;
    datum = DirectFunctionCall1(date_timestamp, datum);
    timestamp2tm(DatumGetTimestamp(datum), NULL, pg_tm_value, &fsec,
                 NULL, NULL);
    result = PyDate_FromDate(pg_tm_value->tm_year,
                             pg_tm_value->tm_mon, pg_tm_value->tm_mday);
    pfree(pg_tm_value);
    return result;
}

static PyObject *
datumTimeToPython(Datum datum, ConversionInfo *cinfo)
{
    struct pg_tm *pg_tm_value = palloc(sizeof(struct pg_tm));
    fsec_t fsec;
    PyObject *result;

    PyDateTime_IMPORT;

    time2tm(DatumGetTimeADT(datum), pg_tm_value, &fsec);

    result = PyTime_FromTime(pg_tm_value->tm_hour,
                             pg_tm_value->tm_min,
                             pg_tm_value->tm_sec,
                             fsec / 1000);  /* Convert microseconds */

    pfree(pg_tm_value);
    return result;
}

PyObject *
datumTimestampToPython(Datum datum, ConversionInfo * cinfo)
{
    struct pg_tm *pg_tm_value = palloc(sizeof(struct pg_tm));
    PyObject   *result;
    fsec_t		fsec;

    PyDateTime_IMPORT;
    timestamp2tm(DatumGetTimestamp(datum), NULL, pg_tm_value, &fsec,
                 NULL, NULL);
    result = PyDateTime_FromDateAndTime(pg_tm_value->tm_year,
                                        pg_tm_value->tm_mon,
                                        pg_tm_value->tm_mday,
                                        pg_tm_value->tm_hour,
                                        pg_tm_value->tm_min,
                                        pg_tm_value->tm_sec,
                                        fsec);
    pfree(pg_tm_value);
    return result;
}

/*
 * Converts a PostgreSQL Timestamp with Time Zone Datum into a Python datetime object.
 *
 * Note: This conversion produces a naive Python datetime. The timestamp's timezone
 *       information is used only to compute local time, and is not preserved in the
 *       resulting Python object. If a timezone-aware datetime is required, additional
 *       handling is necessary.
 *
 * Examples: With a session_timezone Europe/Zurich (+01:00)
 * timestamp with time zone '2001-01-10 10:00:00+02:00' => '2001-01-10 09:00:00
 * timestamp with time zone '2001-01-10 10:00:00+01:00' => '2001-01-10 10:00:00 // same time
 * timestamp with time zone '2001-01-10 10:00:00+00:00' => '2001-01-10 11:00:00
 * timestamp with time zone '2001-01-10 10:00:00-01:00' => '2001-01-10 12:00:00
 *
 */
PyObject *
datumTimestampTzToPython(Datum datum, ConversionInfo * cinfo)
{
    struct pg_tm *pg_tm_value = palloc(sizeof(struct pg_tm));
    PyObject   *result;
    fsec_t		fsec;
    int tzp;
    const char* tzn;

    PyDateTime_IMPORT;
    /*
     * Convert the timestamp Datum into a local broken-down time.
     * This function interprets the Datum using the session timezone,
     * extracting components into pg_tm_value and computing fractional seconds.
     * The timezone offset (tzp) and name (tzn) are also set, but not used below.
     */
    timestamp2tm(DatumGetTimestampTz(datum), &tzp, pg_tm_value, &fsec,
                 &tzn, session_timezone);
    /*
     * Create a Python datetime object using the extracted components.
     * The resulting datetime is naive (i.e., without tzinfo).
     */
    result = PyDateTime_FromDateAndTime(pg_tm_value->tm_year,
                                        pg_tm_value->tm_mon,
                                        pg_tm_value->tm_mday,
                                        pg_tm_value->tm_hour,
                                        pg_tm_value->tm_min,
                                        pg_tm_value->tm_sec,
                                        fsec);
    pfree(pg_tm_value);
    return result;
}

static PyObject *
datumIntToPython(Datum datum, ConversionInfo * cinfo)
{
    return PyLong_FromLong(DatumGetInt32(datum));
}

static PyObject *
datumBoolToPython(Datum datum, ConversionInfo * cinfo)
{
    return PyBool_FromLong(DatumGetBool(datum));
}

static PyObject *
datumDecimalToPython(Datum datum, ConversionInfo *cinfo)
{
    char *decimalStr = DatumGetCString(DirectFunctionCall1(numeric_out, datum));
    PyObject *p_decimal = PyImport_ImportModule("decimal");
    PyObject *p_Decimal = PyObject_GetAttrString(p_decimal, "Decimal");

    PyObject *result = PyObject_CallFunction(p_Decimal, "s", decimalStr);

    Py_DECREF(p_decimal);
    Py_DECREF(p_Decimal);
    pfree(decimalStr);

    return result;
}

static PyObject *
datumArrayToPython(Datum datum, Oid type, ConversionInfo * cinfo)
{
    ArrayIterator iterator = array_create_iterator(DatumGetArrayTypeP(datum), 0, NULL);

    Datum		elem = (Datum) NULL;
    bool		isnull;
    PyObject   *result = PyList_New(0),
               *pyitem;

    while (array_iterate(iterator, &elem, &isnull))
    {
        if (isnull)
        {
            PyList_Append(result, Py_None);
        }
        else
        {
            HeapTuple	tuple;
            Form_pg_type typeStruct;

            tuple = SearchSysCache1(TYPEOID, ObjectIdGetDatum(type));
            if (!HeapTupleIsValid(tuple))
            {
                elog(ERROR, "lookup failed for type %u",
                     type);
            }
            typeStruct = (Form_pg_type) GETSTRUCT(tuple);
            pyitem = datumToPython(elem, typeStruct->typelem, cinfo);
            ReleaseSysCache(tuple);

            PyList_Append(result, pyitem);
            Py_DECREF(pyitem);
        }
    }
    return result;
}


static PyObject *
datumByteaToPython(Datum datum, ConversionInfo * cinfo)
{
    text	   *txt = DatumGetByteaP(datum);
    char	   *str = txt == NULL ? "?" : VARDATA(txt);
    size_t		size = VARSIZE(txt) - VARHDRSZ;

    return PyBytes_FromStringAndSize(str, size);
}

/* Helper that turns a plain string into a Python dictionary */
static PyObject *
jsonStrToPython(char *json_str)
{
    PyObject *json_module, *json_loads, *py_json_str, *result;

    /* Import the Python json module */
    json_module = PyImport_ImportModule("json");
    if (!json_module) {
        elog(ERROR, "import python/json failed");
    }
    /* Get the 'loads' function from the json module */
    json_loads = PyObject_GetAttrString(json_module, "loads");
    if(!json_loads) {
        Py_DECREF(json_module);
        elog(ERROR, "import python/json.loads failed");
    }
    /* Create a Python string object from the C string */
    py_json_str = PyUnicode_FromString(json_str);
    if (!py_json_str)
    {
        Py_DECREF(json_loads);
        Py_DECREF(json_module);
        elog(ERROR, "conversion to python string failed");
    }

    /* Call json.loads() to convert the JSON string into a Python object */
    result = PyObject_CallFunctionObjArgs(json_loads, py_json_str, NULL);

    /* Clean up references */
    Py_DECREF(py_json_str);
    Py_DECREF(json_loads);
    Py_DECREF(json_module);

    return result;
}

static PyObject *
datumHstoreToPython(Datum datum, ConversionInfo *cinfo)
{
    /* Use the internal hstore_to_json and then turn json to Python dictionary */
    Datum jsonbDatum;
    char *json_str;

    /* Call hstore_to_jsonb using the OidFunctionCall1 interface */
    jsonbDatum = OidFunctionCall1(hstore_to_jsonb_oid, datum);

    /* Convert the JSON datum to a C string using the json output function */
    json_str = DatumGetCString(DirectFunctionCall1(jsonb_out, jsonbDatum));

    return jsonStrToPython(json_str);
}


static PyObject *
datumJsonbToPython(Datum datum, ConversionInfo *cinfo)
{
    char *json_str;

    /* Convert the JSONB datum to a C string using the jsonb output function */
    json_str = DatumGetCString(DirectFunctionCall1(jsonb_out, datum));

    return jsonStrToPython(json_str);
}


PyObject *
datumToPython(Datum datum, Oid type, ConversionInfo * cinfo)
{
    HeapTuple	tuple;
    Form_pg_type typeStruct;

    switch (type)
    {
        case BYTEAOID:
            return datumByteaToPython(datum, cinfo);
        case TEXTOID:
        case VARCHAROID:
            return datumStringToPython(datum, cinfo);
        case BPCHAROID:
            return datumBlankPaddedStringToPython(datum, cinfo);
        case NUMERICOID:
            return datumDecimalToPython(datum, cinfo);
        case DATEOID:
            return datumDateToPython(datum, cinfo);
        case TIMESTAMPTZOID:
            return datumTimestampTzToPython(datum, cinfo);
        case TIMESTAMPOID:
            return datumTimestampToPython(datum, cinfo);
        case FLOAT4OID:
            return datumFloat4ToPython(datum, cinfo);
        case FLOAT8OID:
            return datumFloat8ToPython(datum, cinfo);
        case INT2OID:
        case INT4OID:
        case INT8OID:
            return datumIntToPython(datum, cinfo);
        case BOOLOID:
            return datumBoolToPython(datum, cinfo);
        case TIMEOID:
            return datumTimeToPython(datum, cinfo);
        case JSONBOID:
            return datumJsonbToPython(datum, cinfo);
        default:
            /* Maybe HSTORE? We check here because its OID is known at runtime
             * and cannot be added to the switch/case. */
            if (type == hstore_oid) {
                return datumHstoreToPython(datum, cinfo);
            }
            /* Case for the array ? */
            tuple = SearchSysCache1(TYPEOID, ObjectIdGetDatum(type));
            if (!HeapTupleIsValid(tuple))
            {
                elog(ERROR, "lookup failed for type %u",
                     type);
            }
            typeStruct = (Form_pg_type) GETSTRUCT(tuple);
            ReleaseSysCache(tuple);
            if ((typeStruct->typelem != 0) && (typeStruct->typlen == -1))
            {
                /* Its an array. */
                return datumArrayToPython(datum, type, cinfo);
            }
            return datumUnknownToPython(datum, cinfo, type);
    }
}

/*
 * Call the path_keys method from the python implementation, and convert the
 * result to a list of "tuples" (list) of the form:
 *
 * - Bitmapset of attnums - Cost (integer)
 */
List *
pathKeys(MulticornPlanState * state)
{
    List	   *result = NULL;
    Py_ssize_t	i;
    PyObject   *fdw_instance = state->fdw_instance,
               *p_pathkeys;

    p_pathkeys = PyObject_CallMethod(fdw_instance, "get_path_keys", "()");
    errorCheck();
    for (i = 0; i < PySequence_Length(p_pathkeys); i++)
    {
        PyObject   *p_item = PySequence_GetItem(p_pathkeys, i),
                   *p_keys = PySequence_GetItem(p_item, 0),
                   *p_cost = PySequence_GetItem(p_item, 1),
                   *p_cost_long = PyNumber_Long(p_cost);
        double		rows = PyLong_AsDouble(p_cost_long);
        ssize_t		j;
        List	   *attnums = NULL;
        List	   *item = NULL;

        for (j = 0; j < PySequence_Length(p_keys); j++)
        {
            PyObject   *p_key = PySequence_GetItem(p_keys, j);
            ssize_t		k;

            /* Lookup the attribute number by its key. */
            for (k = 0; k < state->numattrs; k++)
            {
                ConversionInfo *cinfo = state->cinfos[k];

                if (cinfo == NULL)
                {
                    continue;
                }
                if (p_key != Py_None &&
                    strcmp(cinfo->attrname, PyString_AsString(p_key)) == 0)
                {
                    attnums = list_append_unique_int(attnums, cinfo->attnum);
                    break;
                }
            }
            Py_DECREF(p_key);
        }
        item = lappend(item, attnums);
        item = lappend(item, makeConst(INT4OID,
                                     -1, InvalidOid, 4, rows, false, true));
        result = lappend(result, item);
        Py_DECREF(p_keys);
        Py_DECREF(p_cost);
        Py_DECREF(p_cost_long);
        Py_DECREF(p_item);
    }
    Py_DECREF(p_pathkeys);
    return result;
}

/*
 * Call the can_sort method from the python implementation. We provide a deparsed
 * version of the requested fields to sort with all detail as needed (nulls,
 * collate...), and convert the result to a list of "tuples" (list) of the form:
 *
 * - Bitmapset of attnums
 *
 * representing the fields that the foreign data wrapper can be sort as
 * we requested.
 */
List *
canSort(MulticornPlanState * state, List *deparsed)
{
    List	   *result = NULL;
    ListCell   *lc;
    Py_ssize_t	i;
    PyObject   *fdw_instance = state->fdw_instance,
               *p_pathkeys = PyList_New(0),
               *p_sortable;

    foreach(lc, deparsed)
    {
        MulticornDeparsedSortGroup *pathkey = (MulticornDeparsedSortGroup *) lfirst(lc);
        PyObject *python_sortkey = getSortKey(pathkey);
        PyList_Append(p_pathkeys, python_sortkey);
        Py_DECREF(python_sortkey);
    }

    p_sortable = PyObject_CallMethod(fdw_instance, "can_sort", "(O)", p_pathkeys);
    errorCheck();
    for (i = 0; i < PySequence_Length(p_sortable); i++)
    {
        PyObject   *p_key = PySequence_GetItem(p_sortable, i);
        MulticornDeparsedSortGroup *md = getDeparsedSortGroup(p_key);
        result = lappend(result, md);
        Py_DECREF(p_key);
    }
    Py_DECREF(p_pathkeys);
    Py_DECREF(p_sortable);
    return result;
}

PyObject *
tupleTableSlotToPyObject(TupleTableSlot *slot, ConversionInfo ** cinfos)
{
    PyObject   *result = PyDict_New();
    TupleDesc	tupdesc = slot->tts_tupleDescriptor;
    int			i;

    for (i = 0; i < tupdesc->natts; i++)
    {
        Form_pg_attribute attr = TupleDescAttr(tupdesc,i);
        bool		isnull;
        Datum		value;
        PyObject   *item;
        AttrNumber	cinfo_idx = attr->attnum - 1;

        if (attr->attisdropped || cinfos[cinfo_idx] == NULL)
        {
            continue;
        }
        value = slot_getattr(slot, i + 1, &isnull);
        if (isnull)
        {
            item = Py_None;
            Py_INCREF(item);
        }
        else
        {
            item = datumToPython(value, cinfos[cinfo_idx]->atttypoid,
                                 cinfos[cinfo_idx]);
            errorCheck();
        }
        PyDict_SetItemString(result, cinfos[cinfo_idx]->attrname, item);
        Py_DECREF(item);
    }
    return result;
}

/*
 * Get the rowid column name
 */
char *
getRowIdColumn(PyObject *fdw_instance)
{
    PyObject   *value = PyObject_GetAttrString(fdw_instance, "rowid_column");
    char	   *result;

    errorCheck();
    if (value == Py_None)
    {
        Py_DECREF(value);
        elog(ERROR, "This FDW does not support the writable API");
    }
    result = PyString_AsString(value);
    Py_DECREF(value);
    return result;
}

/*
 * Get modify batch size
 */
int getModifyBatchSize(PyObject *fdw_instance)
{
    PyObject   *value = PyObject_GetAttrString(fdw_instance, "modify_batch_size");
    int			result;

    errorCheck();
    if (value == Py_None)
    {
        Py_DECREF(value);
        return 1; // Default to disabling batch modifications for backwards compatibility
    }

    result = PyLong_AsLong(value);
    errorCheck();
    Py_DECREF(value);

    return result;
}

/*
 * This function constructs a dummy AttInMetadata structure for a given return type.
 * It creates a tuple descriptor with a single attribute and initializes it with the
 * specified return type. If the return type is an array, it adjusts the dimension 
 * count accordingly.
 */
static AttInMetadata *
build_dummy_attinmeta(Oid retType)
{
    TupleDesc tupDesc;
    AttInMetadata *attinmeta;
    int attndims = 0;
    Oid elemType = get_element_type(retType);

    /* If retType is an array type, set attndims to 1 */
    if (OidIsValid(elemType)) {
        attndims = 1;
    }

    /* Create a tuple descriptor with 1 column */
    tupDesc = CreateTemplateTupleDesc(1);

    /*
     * Initialize the single attribute.
     * Name: "dummy"
     * Type: retType
     * typmod: -1 (unknown)
     * attndims: set as above (0 for scalar, 1 for array)
     */
    TupleDescInitEntry(tupDesc,
                       (AttrNumber) 1,
                       "dummy",
                       retType,
                       -1,
                       attndims);

    /* Get the conversion info from the tuple descriptor */
    attinmeta = TupleDescGetAttInMetadata(tupDesc);

    return attinmeta;
}


/*
 * This function executes the Python function defined in multicorn to execute functions and returns
 * the result as a Datum. It prepares the options and arguments as Python dictionaries,
 * calls the Python function, and converts the result back to a PostgreSQL Datum.
 */
Datum
foreign_function_execute(List *options_list, int nArgs, char **argNames,  Oid *argTypes, Datum *argDatums, bool *argNulls, Oid retType)
{
    /* 1) Build a Python dictionary from the FDW-like options list. */
    PyObject *option_dict = optionsListToPyDict(options_list);
    errorCheck();  /* check for Python errors */

    /* 2) Build a Python dictionary for the function arguments, keyed by name. */
    PyObject *py_argdict = PyDict_New();
    if (!py_argdict)
    {
        Py_DECREF(option_dict);
        elog(ERROR, "Failed to create Python dictionary for function arguments");
    }
    for (int i = 0; i < nArgs; i++)
    {
        PyObject *pyVal = NULL;
        if (argNulls[i])
        {
            Py_INCREF(Py_None);
            pyVal = Py_None;
        }
        else
        {
            ConversionInfo localCinfo;
            memset(&localCinfo, 0, sizeof(localCinfo));
            localCinfo.atttypoid = argTypes[i];
            pyVal = datumToPython(argDatums[i], argTypes[i], &localCinfo);
        }
        if (!pyVal)
        {
            Py_DECREF(py_argdict);
            Py_DECREF(option_dict);
            elog(ERROR, "Failed to convert argument %d to Python object", i);
        }
        if (PyDict_SetItemString(py_argdict, argNames[i], pyVal) != 0)
        {
            Py_DECREF(pyVal);
            Py_DECREF(py_argdict);
            Py_DECREF(option_dict);
            elog(ERROR, "Failed to set argument '%s' in Python dictionary", argNames[i]);
        }
        Py_DECREF(pyVal); /* PyDict_SetItemString increases reference count */
    }
    errorCheck();

    /* Check if the "wrapper" key exists in the options dictionary */
    PyObject *p_wrapper = PyDict_GetItemString(option_dict, "wrapper");
    if (p_wrapper == NULL)
    {
        Py_DECREF(py_argdict);
        Py_DECREF(option_dict);
        elog(ERROR, "Missing 'wrapper' key in options");
    }

    /* Get the class from the wrapper value (which is a borrowed reference) */
    PyObject *p_class = getClass(p_wrapper);
    if (p_class == NULL || !PyCallable_Check(p_class))
    {
        Py_XDECREF(p_class);
        Py_DECREF(py_argdict);
        Py_DECREF(option_dict);
        elog(ERROR, "Could not get callable wrapper class from 'wrapper' option");
    }

    /* Remove the "wrapper" key from the dictionary; check for errors */
    if (PyDict_DelItemString(option_dict, "wrapper") < 0)
    {
        Py_DECREF(p_class);
        Py_DECREF(py_argdict);
        Py_DECREF(option_dict);
        elog(ERROR, "Failed to remove 'wrapper' key from options");
    }

    /* 5) Then get the class method "execute_static". */
    PyObject *p_func = PyObject_GetAttrString(p_class, "execute_static");
    Py_DECREF(p_class);
    if (!p_func || !PyCallable_Check(p_func))
    {
        Py_XDECREF(p_func);
        Py_DECREF(py_argdict);
        Py_DECREF(option_dict);
        elog(ERROR, "No callable 'execute_static' found in DASFunction");
    }

    PyObject* kwargs = PyDict_New();
    PyObject* scopes = get_scopes();
    if (scopes) {
        PyDict_SetItemString(kwargs, "scopes", scopes);
    }
    PyObject* http_headers = get_http_headers();
    if (http_headers) {
        PyDict_SetItemString(kwargs, "http_headers", http_headers);
    }

    /* 6) Build final arguments for p_func.
     * Assume execute_static expects two parameters:
     *   - a dict of options,
     *   - a dict of arguments keyed by name.
     */
    PyObject *call_args = PyTuple_New(2);
    PyTuple_SetItem(call_args, 0, option_dict);  /* tuple takes ownership */
    PyTuple_SetItem(call_args, 1, py_argdict);   /* tuple takes ownership */

    /* 7) Call the Python method. */
    PyObject *p_result = PyObject_Call(p_func, call_args, kwargs);
    Py_DECREF(call_args);
    if (http_headers) {
        Py_DECREF(http_headers);
    }
    if (scopes) {
        Py_DECREF(scopes);
    }
    Py_DECREF(kwargs);
    Py_DECREF(p_func);
    errorCheck();

    if (!p_result || p_result == Py_None)
    {
        Py_XDECREF(p_result);
        elog(ERROR, "execute_static returned non-string or None");
    }

    /* 8) Convert the Python result to a Postgres Datum using pyobjectToDatum. */
    StringInfo buffer = makeStringInfo();
    ConversionInfo* retCinfo;

    /* Retrieve the type’s output function and related info */
    AttInMetadata* meta = build_dummy_attinmeta(retType);
    initConversioninfo(&retCinfo, meta);

    /* Optionally set other retCinfo fields if needed */
    Datum resultDatum = pyobjectToDatum(p_result, buffer, retCinfo);
    Py_DECREF(p_result);
    pfree(buffer->data);
    pfree(buffer);
    /* Return the converted Datum. */
    return resultDatum;

}
