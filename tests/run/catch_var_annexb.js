// §B.3.4 on a host that is not a web browser but otherwise supports it: a var
// in a Catch Block may bind the name of a simple CatchParameter, and the
// assignment goes to the CatchParameter's binding.
// args: --annex-b sec-variablestatements-in-catch-blocks
// expect: normal: "2,"
var r;
try { throw 1; } catch (e) { var e = 2; r = e; }
[r, e].join()
