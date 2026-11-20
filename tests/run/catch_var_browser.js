// §B.3.4 on a web browser host: a var in a Catch Block may bind the name of a
// simple CatchParameter (the Catch Early Error's exemption), and the
// assignment goes to the CatchParameter's binding.
// args: --web-browser
// expect: normal: "2,"
var r;
try { throw 1; } catch (e) { var e = 2; r = e; }
[r, e].join()
