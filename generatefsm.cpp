/* Copyright (c) 2021 The Connectal Project
 *
 * Permission is hereby granted, free of charge, to any person obtaining a
 * copy of this software and associated documentation files (the "Software"),
 * to deal in the Software without restriction, including without limitation
 * the rights to use, copy, modify, merge, publish, distribute, sublicense,
 * and/or sell copies of the Software, and to permit persons to whom the
 * Software is furnished to do so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included
 * in all copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS
 * OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
 * FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL
 * THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
 * LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
 * FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER
 * DEALINGS IN THE SOFTWARE.
 */

#include <stdio.h>
#include <fcntl.h>
#include <unistd.h>
#include <string>
#include <map>

#include "cJSON.c"

#define BUFFER_LENGTH 20000000
#define getObject cJSON_GetObjectItemCaseSensitive

static char buffer[BUFFER_LENGTH];
static FILE *outfile;
static std::map<std::string, std::string> dataMap;

static void dumpJson(const cJSON *arg, std::string &master, int depth);
static void dumpSingle(const cJSON *p, std::string &master, int depth);
static std::string getExprSingle(const cJSON *item);

typedef struct {
    const char *name;
    const char *value;
} NameMap;

NameMap dirMap[] = {
    {"In", "input"},
    {"Out", "output"},
    {"InOut", "inout"},
    {nullptr, nullptr}};
NameMap edgeMap[] = {
    {"PosEdge", "posedge"},
    {"NegEdge", "negedge"},
    {nullptr, nullptr}};
NameMap procKindMap[] = {
    {"Always", "always"},
    {"AlwaysComb", "always comb"},
    {nullptr, nullptr}};
NameMap unaryMap[] = {
    {"LogicalNot", "!"},
    {"BitwiseNot", "~"},
    {"Minus", "-"},
    {nullptr, nullptr}};
NameMap binaryMap[] = {
    {"LogicalAnd", "&&"},
    {"BinaryAnd", "&"},
    {"LogicalOr", "||"},
    {"BinaryOr", "|"},
    {"Add", "+"},
    {"Subtract", "-"},
    {"Divide", "/"},
    {"Equality", "=="},
    {"CaseEquality", "=="},
    {"Inequality", "!="},
    {"LessThan", "<"},
    {"LessThanEqual", "<="},
    {"GreaterThan", ">"},
    {"GreaterThanEqual", ">="},
    {"LogicalShiftLeft", "<<"},
    {nullptr, nullptr}};
NameMap repMap[] = {
    {"Nonconsecutive", "="},
    {"Consecutive", "*"},
    {"GoTo", "->"},
    {nullptr, nullptr}};
NameMap binaryPropMap[] = {
    {"Implication", "|->"},
    {"Throughout", "throughout"},
    {"Intersect", "intersect"},
    {"Until", "until"},
    {"Within", "within"},
    {"FollowedBy", "#-#"},
    {"Implies", "->"},
    {"Iff", "iff"},
    {"Until", "until"},
    {"And", "&&"},
    {"Or", "||"},
    {nullptr, nullptr}};
NameMap unaryPropMap[] = {
    {"Not", "!"},
    {"NextTime", "nextime("},
    {nullptr, nullptr}};

extern "C" void jca(){}

static inline std::string autostr(uint64_t X, bool isNeg = false)
{
    char Buffer[21];
    char *BufPtr = std::end(Buffer);

    if (X == 0) *--BufPtr = '0';  // Handle special case...

    while (X) {
        *--BufPtr = '0' + char(X % 10);
        X /= 10;
    }

    if (isNeg) *--BufPtr = '-';   // Add negative sign...
    return std::string(BufPtr, std::end(Buffer));
}
static bool inline startswith(std::string str, std::string suffix)
{
    return str.substr(0, suffix.length()) == suffix;
}
static bool inline endswith(std::string str, std::string suffix)
{
    int skipl = str.length() - suffix.length();
    return skipl >= 0 && str.substr(skipl) == suffix;
}

static std::string getString(const cJSON *arg, const char *name, NameMap *map = nullptr)
{
    cJSON *item = getObject(arg, name);
    std::string val;
    if (item && item->valuestring) {
        val = item->valuestring;
        if (map) {
            while (map->name) {
                if (val == map->name)
                    return map->value;
                map++;
            }
printf("[%s:%d] NAMEMAP %s fail %s\n", __FUNCTION__, __LINE__, (map-1)->name, val.c_str());
        }
    }
    return val;
}

static std::string getStringSpace(const cJSON *arg, const char *name)
{
    std::string val = getString(arg, name);
    int ind = val.find(" ");
    if (ind > 0)
        val = val.substr(ind+1);
    return val;
}

static bool getBool(const cJSON *parent, const char *name)
{
    return cJSON_IsTrue(getObject(parent, name));
}

static int getInteger(const cJSON *parent, const char *name)
{
    const cJSON *p = getObject(parent, name);
    return p->valueint;
}

static std::string setDataMap(std::string temp, std::string base)
{
    auto item = dataMap.find(temp);
    if (item != dataMap.end())
        return item->second;
    dataMap[temp] = base;
    fprintf(outfile, "**** %s ****\n%s\n", base.c_str(), temp.c_str());
    return base;
}

static std::string getExpr(const cJSON *parent, const char *name)
{
    return getExprSingle(getObject(parent, name));
}
static std::string getExprArray(const cJSON *parent, const char *name)
{
    std::string master, sep;
    const cJSON *expr = NULL;
    cJSON_ArrayForEach(expr, getObject(parent, name)) {
        master += sep + getExprSingle(expr);
        sep = ", ";
    }
    return master;
}
static std::string getExprSingle(const cJSON *item)
{
    if (!item)
        return "";
    std::string kind = getString(item, "kind");
    std::string type = getString(item, "type");
    std::string left = getExpr(item, "left");
    std::string right = getExpr(item, "right");
    std::string val;
    if (kind == "Assignment") {
        val = "=";
        if (const cJSON *nonBlock = getObject(item, "isNonBlocking"))
        if (nonBlock->type & cJSON_True)
            val = "<=";
    }
    else if (kind == "IntegerLiteral")
        val = getString(item, "constant");
    else if (kind == "UnaryOp")
        val = getString(item, "op", unaryMap) + getExpr(item, "operand");
    else if (kind == "BinaryOp")
        val = getString(item, "op", binaryMap);
    //else if (kind == "Binary")   ///////////////// TODO: typo????????????????????????
        //val = getString(item, "op", binaryMap);
    else if (kind == "NamedValue")
        val = getStringSpace(item, "symbol");
    else if (kind == "StringLiteral")
        val = "\"" + getStringSpace(item, "literal") + "\"";
    else if (kind == "Concatenation")
        return "{" + getExprArray(item, "operands") + "}";
    else if (kind == "Conversion") {
        auto *op = getObject(item, "operand");
        std::string type = getString(item, "type");
        if (type == "reg" || startswith(type, "reg["))
            type = "logic" + type.substr(3);
        if (getString(op, "kind") == "Conversion")
            op = getObject(op, "operand");
        return "(" + type + ")" + getExprSingle(op);
    }
    else if (kind == "RangeSelect")
        return getExpr(item, "value") + "[" + left + ":" + right + "]";
    else if (kind == "MemberAccess")
        val = getExpr(item, "value") + "." + getStringSpace(item, "member");
    else if (kind == "ElementSelect")
        val = getExpr(item, "value") + "[" + getExpr(item, "selector") + "]";
    else if (kind == "Call")
        val = getStringSpace(item, "subroutine") + "(" + getExprArray(item, "arguments") + ")";
    else if (kind == "EmptyArgument")
        val = "EA";
    else if (kind == "ConditionalOp")
        return "(" + getExpr(item, "pred") + ") ? " + left + " : " + right;
    else if (kind == "HierarchicalValue") {
        val = "HV:" + getString(item, "symbol");
//printf("[%s:%d]val %s left %s righ %s kind %s op %s type %s\n", __FUNCTION__, __LINE__, val.c_str(), left.c_str(), right.c_str(), kind.c_str(), op.c_str(), type.c_str());
//dumpJson(item,stdout, 0);
    }
    if (val == "") {
        printf("[%s:%d] val %s left %s righ %s kind %s type %s\n", __FUNCTION__, __LINE__, val.c_str(), left.c_str(), right.c_str(), kind.c_str(), type.c_str());
        //dumpJson(item, stdout, 0);
        exit(-1);
    }
    return left + " " + val + " " + right;
}

static void processBlock(std::string startString, const cJSON *p, std::string &master, int depth)
{
    std::string kind = getString(p, "kind");
    if (!p || kind == "Empty")
        return;
    if (startswith(startString, "else"))
        for (int i = 0; i < depth-1; i++)
            master += "    ";
    master += startString;
    const cJSON *body = getObject(p, "body");
    std::string bkind = getString(body, "kind");
//fprintf(d, "[%s:%d] p %p body %p kind %s bkind %s\n", __FUNCTION__, __LINE__, p, body, kind.c_str(), bkind.c_str());
    if (bkind == "List") {
        const cJSON *item = NULL;
        cJSON_ArrayForEach(item, getObject(body, "list")) {
            processBlock("", item, master, depth);
        }
    }
    else {
        for (int i = 0; i < depth; i++)
            master += "    ";
        if (kind == "Conditional") {
            master += "if (" + getExpr(p, "cond") + ") ";
            processBlock("begin\n", getObject(p, "ifTrue"), master, depth+1);
            processBlock("else begin\n", getObject(p, "ifFalse"), master, depth+1);
        }
        else if (kind == "ExpressionStatement")
            master += getExpr(p, "expr") + ";\n";
        else if (kind == "Case") {
            master += "CASE: " + getString(p, "check") + " " + getExpr(p, "expr") + "\n";
            const cJSON *item = NULL;
            cJSON_ArrayForEach(item, getObject(p, "items")) {
                master += "    case " + getExprArray(item, "expressions") + ":\n";
                processBlock("", getObject(item, "stmt"), master, depth+1);
            }
            master += "ENDCASE\n";
        }
    }
    if (startString != "") {
        for (int i = 0; i < depth-1; i++)
            master += "    ";
        master += "end\n";
    }
}

static std::string setDefinition(const cJSON *arg)
{
    std::string master, val, sep;
    std::string objectName = getString(arg, "definition");
    const cJSON *memb = getObject(arg, "members");
    bool inParam = false;
    bool inPort = true;
    const cJSON *item = NULL;
    cJSON_ArrayForEach(item, memb) {
        std::string name = getString(item, "name");
        const cJSON *init = getObject(item, "initializer");
        std::string constVal = getString(init, "constant");
        int ind = constVal.find("'");
        int ind2 = constVal.find(".");
        if (ind < 0 && ind2 < 0 && name != "" && constVal != "" && objectName.length() < 40)
            objectName += "__" + name + "_" + constVal;
        std::string kind = getString(item, "kind");
        std::string type = getString(item, "type");
        std::string direction = getString(item, "direction", dirMap);
        std::string v = getString(item, "value");
        if (kind == "Port") {
            if (inParam) {
                val = "#(" + val + ")(";
                sep = "";
            }
            else if (sep == "")
                val += "(";
            inParam = false;
            val += sep + direction + " " + type + " " + name;
            if (v != "")
                val += "=" + v;
            sep = ", ";
        }
        else if (kind == "Parameter") {
            inParam = true;
            val += sep + name;
            if (v != "")
                val += "=" + v;
            sep = ", ";
        }
        else if (kind == "InterfacePort" || direction != "") {
            if (inParam) {
                val = "#(" + val + ")(";
                sep = "";
            }
            else if (sep == "")
                val += "(";
            inParam = false;
            if (direction != "") {
                val += sep + direction + " " + type + " " + name;
            }
            else
                val += sep + getString(item, "interfaceDef") + "." + getString(item, "modport") + " " + name;
            sep = ", ";
        }
    }
    if (inPort && val != "") {
        if (inParam)
            val = "#(" + val;
        val += ")";
    }
    std::string defineType = "module";
    master += " " + objectName + " " + val + ";\n";
    cJSON_ArrayForEach(item, memb) {
        std::string direction = getString(item, "direction", dirMap);
        std::string kind = getString(item, "kind");
        if (kind == "Port" || kind == "Parameter" || kind == "InterfacePort" || direction != "" || kind == "Net")
            continue;
        if (kind == "Variable") {
            master += "    " + getString(item, "type") + " " + getString(item, "name") + ";" + "\n";
        }
        else if (kind == "Modport") {
            defineType = "interface";
            std::string sep;
            master += "    modport (";
            const cJSON *mitem = NULL;
            cJSON_ArrayForEach(mitem, getObject(item, "members")) {
                master += sep + getString(mitem, "direction", dirMap) + " " //+ getString(mitem, "type") + " "
                           + getString(mitem, "name");
                sep = ", ";
            }
            master += ") " + getString(item, "name") + ";\n";
        }
        else
            dumpSingle(item, master, 1);
    }
    //dumpJson(arg->child, master, 0);
    return setDataMap(defineType + master + "end" + defineType + "\n", objectName);
}

static std::string dumpTiming(const cJSON *p)
{
    std::string kind = getString(p, "kind");
    if (kind != "SignalEvent")
        printf("[%s:%d]KIND %s\n", __FUNCTION__, __LINE__, kind.c_str());
    std::string edge = getString(p, "edge", edgeMap);
    std::string expr = getExpr(p, "expr");
    return "@(" + edge + " " + expr + ")";
}

static std::string getSignalEvent(const cJSON *p)
{
    return "@ (" + getString(p, "edge") + " " + getExpr(p, "expr") + ")";
}

static std::string getProp(const cJSON *parent, const char *name)
{
    const cJSON *p = getObject(parent, name);
    std::string kind = getString(p, "kind");
    std::string val;
    if (kind == "Clocking") {
        val = "CLOCKING" + getSignalEvent(getObject(p, "clocking")) + "(" + getProp(p, "expr") + ")";
    }
    else if (kind == "Simple")
        val = getExpr(p, "expr");
    else if (kind == "Binary") {
        std::string op = getString(p, "op", binaryPropMap);
        val = getProp(p, "left") + op + getProp(p, "right") + (endswith(op, ")") ? ")" : "");
    }
    else if (kind == "Unary") {
        std::string op = getString(p, "op", unaryPropMap);
        val = op + getProp(p, "expr");
    }
    else if (kind == "SequenceConcat") {
        const cJSON *item = NULL;
        bool tail = false;
        cJSON_ArrayForEach(item, getObject(p, "elements")) {
            std::string bkind = getString(item, "kind");
            int max = getInteger(item, "max");
            int min = getInteger(item, "min");
            if (max != min)
                val += "##[" + autostr(min) + "," + autostr(max) + "] ";
            else if (tail || max)
                val += "##" + autostr(max) + " ";
            val += getProp(item, "sequence");
            tail = true;
        }
    }
    else if (kind == "StrongWeak") {
        std::string op = getString(p, "strength");
        val = op + "(" + getProp(p, "expr") + ")";
    }
    else {
        dumpSingle(p, val, 0);
printf("[%s:%d]ERROROROROROR '%s'\n", __FUNCTION__, __LINE__, val.c_str());
    }
    if (const cJSON *rep = getObject(p, "repetition")) {
        int max = getInteger(rep, "max");
        int min = getInteger(rep, "min");
        val += "[" + getString(rep, "kind", repMap);
        if (max != min)
            val += autostr(min) + "," + autostr(max);
        else if (max)
            val += autostr(max);
        val += "] ";
    }
    return val;
}

static void dumpSingle(const cJSON *p, std::string &master, int depth)
{
        int type = p->type;
        std::string name, vstring;
        if (p->string)
            name = p->string;
        if (p->valuestring)
            vstring = p->valuestring;
        if (name == "addr")
            return;
        if (name == "name" && vstring == "")
            return;
        for (int i = 0; i < depth; i++)
            master += "    ";
        if (name != "")
            master += "ZZ_" + name + ": ";
        if (type & cJSON_False)
            master += "FALSE\n";
        if (type & cJSON_True)
            master += "TRUE\n";
        if (type & cJSON_NULL)
            master += "NULL\n";
        if (p && (type & cJSON_Raw))
            master += "RAW\n";
        if (type & cJSON_Number)
            master += autostr(p->valueint) + "\n";
        if (type & cJSON_String)
            master += "'" + vstring + "'\n";
        if (type & cJSON_Array) {
            master += "ARR\n";
            dumpJson(p->child, master, depth+1);
        }
        if (type & cJSON_Object) {
            std::string kind = getString(p, "kind");
            std::string definition = getString(p, "definition");
            if (kind == "Root")
                dumpJson(getObject(p, "members"), master, depth+1);
            else if (kind == "ContinuousAssign")
                master += "assign" + getExpr(p, "assignment") + "\n";
            else if (kind == "Instance") {
                master += setDefinition(getObject(p, "body")) + " " + getString(p, "name") + "(";
                std::string sep;
                const cJSON *item = NULL;
                cJSON_ArrayForEach(item, getObject(p, "connections")) {
                    bool isInterface = getBool(item, "isInterfacePort");
                    if (isInterface)
                        master += sep + "." + getStringSpace(item, "ifacePort") + "(" + getStringSpace(item, "ifaceInstance") + ")";
                    else {
                        const cJSON *expr = getObject(item, "expr");
                        if (getString(expr, "kind") == "Assignment") {
                            const cJSON *right = getObject(expr, "right");
                            if (getString(right, "kind") == "EmptyArgument") {
                                expr = getObject(expr, "left");
                            }
                            else {
master += "ZZZZZZZZZZZZZZZZZZZZ" + getExprSingle(right) + "\n";
                            }
                        }
                        std::string exprStr = getExprSingle(expr);
                        master += sep + "." + getStringSpace(item, "port") + "(" + exprStr + ")";
                    }
                    sep = ",\n        ";
                }
                master += ");\n";
#if 0
    const cJSON *pnext = p;
//getObject(json, "Root");
//int count = 0;
    while (pnext) {
std::string name;
if (pnext->string)
    name = pnext->string;
master += "INSTT " + name + " kind=" + getString(pnext, "kind") + " type=" + autostr(pnext->type) + "\n";
         //dumpSingle(pnext, master, 0);
         pnext = pnext->next;
    }
#endif
            }
            else if (kind == "PrimitiveInstance") {
                std::string name = getString(p, "name"), sep;
                master += "    " + getStringSpace(p, "primitiveType") + " " + name + "(";
                const cJSON *item = NULL;
                cJSON_ArrayForEach(item, getObject(p, "ports")) {
                    master += sep + getExprSingle(item);
                    sep = ", ";
                }
                master += ");\n";
            }
            else if (kind == "InstanceArray") {
                std::string name = getString(p, "name");
                const cJSON *item = NULL;
                cJSON_ArrayForEach(item, getObject(p, "members")) {
                    master += "INSTANCEARRAY: " + setDefinition(getObject(item, "body")) + " " + name + "\n";
                    //dumpJson(item, master, depth+1);
                }
            }
            else if (kind == "Block")
                processBlock("", p, master, depth);
            else if (kind == "SignalEvent")
                //master += "always @ " + getString(p, "edge") + " " + getExpr(p, "expr") + "\n";
                master += "always " + getSignalEvent(p) + "\n";
            else if (kind == "ProceduralBlock") {
                const cJSON *body = getObject(p, "body");
                std::string type = getString(p, "procedureKind", procKindMap);
                std::string bkind = getString(body, "kind");
                if (bkind == "ConcurrentAssertion")
                    master += "    assert property (" + getProp(body, "propertySpec") + ");\n";
                else if (bkind != "Timed")
                    master += "BKIND=" + bkind + "\n";
                master += type;
                if (const cJSON *timing = getObject(body, "timing"))
                    master += " " + dumpTiming(timing);
                master += " begin\n";
                if (const cJSON *stmt = getObject(body, "stmt"))
                    processBlock("", stmt, master, depth);
                master += "    end;\n";
            }
            else if (kind == "CompilationUnit") {
                const cJSON *item = NULL;
                cJSON_ArrayForEach(item, getObject(p, "members")) {
                    const cJSON *pnext = item;
                    while (pnext) {
                        std::string akind = getString(pnext, "kind");
                        std::string name;
                        if (pnext->string)
                            name = pnext->string;
                        master += "COMPUNIT " + name + " kind=" + akind + " type=" + autostr(pnext->type);
                        if (akind == "TypeAlias") {
                            master += "  TYPEALIAS: ";
                            std::string name = getString(pnext, "name");
                            std::string str = getString(pnext, "target");
                            if (startswith(str, "struct")) {
                                int ind = str.rfind("}");
                                if (ind != -1)
                                    str = str.substr(0, ind+1);
                            }
                            master += setDataMap("typedef " + str + " " + name + ";", "TYPE_" + name);
                        }
                        else
                            dumpSingle(pnext, master, 0);
                        master += "\n";
                        pnext = pnext->next;
                    }
                }
            }
            else if (definition != "")
                master += "FILEDEF: " + setDefinition(p) + "\n";
            else {
                master += "OBJ: " + kind + "\n";
                dumpJson(p->child, master, depth+1);
            }
        }
}

static void dumpJson(const cJSON *arg, std::string &master, int depth)
{
    const cJSON *pnext = arg;
    while (pnext) {
         dumpSingle(pnext, master, depth);
         pnext = pnext->next;
    }
}

int main(int argc, char *argv[])
{
    std::string outputFile = "yy.json.dump";
    int inFile = open("xx.json", O_RDONLY);
    unsigned long len = read(inFile, buffer, sizeof(buffer));
    if (inFile == -1 || len <= 0 || len >= sizeof(buffer) - 10) {
        printf("[%s:%d] error reading\n", __FUNCTION__, __LINE__);
        exit(-1);
    }
    printf("[%s:%d] value %p len %ld \n", __FUNCTION__, __LINE__, buffer, len);
    cJSON *json = cJSON_ParseWithLength(buffer, len);
    if (json == NULL) {
        const char *error_ptr = cJSON_GetErrorPtr();
        if (error_ptr != NULL) {
            static char foo[1000];
            memcpy(foo, error_ptr, 800);
            printf("Error before: %s\n", foo);
        }
        return -1;
    }
    outfile = fopen(outputFile.c_str(), "w");
    std::string master;
    dumpJson(json, master, 0);
    fprintf(outfile, "%s\n", master.c_str());
    cJSON_Delete(json);
    fclose(outfile);
    return 0;
}
