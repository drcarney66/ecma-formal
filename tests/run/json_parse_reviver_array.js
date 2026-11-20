// §25.5.1 JSON.parse with a reviver over arrays: CreateJSONParseRecord's
// JSONArrayLiteralContentNodes row `[ ElementList ]` asserts |Elision| is not present
// (the production has none: absent).
// expect: normal: undefined
// print: 1,2|3
// print: 0,1,0,
function r(k, v) { return typeof v === "number" ? v + 1 : v; }
var a = JSON.parse('[[0,1],[2]]', r);
print(a[0] + "|" + a[1]);
var keys = [];
JSON.parse('[[1,2]]', function (k, v) { keys.push(k); return v; });
print(keys.join());
