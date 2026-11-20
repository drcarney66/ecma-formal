// §B.1.2 at run time (refactor R25): ParsePattern of `new RegExp` on a host
// that does not support §B.1.2 uses the main grammar, so an out-of-range
// DecimalEscape, `\1` with no group, is a SyntaxError; a valid pattern parses.
// expect: normal: "SyntaxError,true"
var r = [];
try { new RegExp("\\1"); r.push("parsed"); } catch (e) { r.push(e.name); }
r.push(new RegExp("(a)\\1").test("aa"));
r.join()
