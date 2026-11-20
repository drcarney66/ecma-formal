// Without §B.3.9 (not a web-browser host) a call is an invalid assignment
// target: an early SyntaxError.
// expect: normal: "SyntaxError"
function f() {}
var r;
try { eval("f() = 1"); } catch (e) { r = e.name; }
r
