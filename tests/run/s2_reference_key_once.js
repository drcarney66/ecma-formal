// GetValue step 3.c.i writes the property key back into the Reference Record,
// so a compound, update or logical assignment runs ToPropertyKey once.
// expect: normal: "3,3"
"use strict";
var n = 0; var k = { toString() { n++; return "a"; } }; var o = { a: 1 };
o[k] += 1; o[k]++; o[k] ??= 5;
n + "," + o.a
