// JSON.parse with a reviver and its context's "source" (§25.5.2), then
// JSON.stringify with a replacer array and a gap (§25.5.4).
// expect: normal: "{\n \"a\": [\n  \"1.50\",\n  2\n ],\n \"c\": \"\\u0000\"\n}"
var o = JSON.parse('{"a": [1.50, 2], "b": true, "c": "\\u0000"}', function (k, v, cx) {
  return k === "0" ? cx.source : v;
});
JSON.stringify(o, ["a", "c", "0", 1], 1)
