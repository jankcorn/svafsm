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
#include "cJSON.h"

#define BUFFER_LENGTH 20000000
#define getObject cJSON_GetObjectItemCaseSensitive

typedef struct {
    const char *name;
    const char *value;
} NameMap;

std::string autostr(uint64_t X, bool isNeg = false);
bool startswith(std::string str, std::string suffix);
bool endswith(std::string str, std::string suffix);

std::string getExprSingle(const cJSON *item);
std::string getProp(const cJSON *parent, const char *name);

std::string getString(const cJSON *arg, const char *name, NameMap *map = nullptr);
std::string getStringSpace(const cJSON *arg, const char *name);
bool getBool(const cJSON *parent, const char *name);
std::string getInteger(const cJSON *parent, const char *name);
std::string setDataMap(std::string temp, std::string base);
std::string getExpr(const cJSON *parent, const char *name);
std::string getExprArray(const cJSON *parent, const char *name);
std::string getExprSingle(const cJSON *item);
std::string dumpTiming(const cJSON *p);
std::string getSignalEvent(const cJSON *p);
std::string getProp(const cJSON *parent, const char *name);
void processBlock(std::string startString, const cJSON *p, std::string &master, int depth);
std::string setDefinition(const cJSON *arg);
void dumpSingle(const cJSON *p, std::string &master, int depth);
void dumpJson(const cJSON *arg, std::string &master, int depth);
