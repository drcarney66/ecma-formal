// §22.2.1.1's modifier early errors are keyed on Atom; under §B.1.2 a pattern without `u` or `v` has an
// ExtendedAtom there, which no early error covers. Each pattern is compiled as a literal (indirect eval)
// and by the RegExp constructor.
if (typeof print === "undefined") globalThis.print = console.log;
var patterns = ["(?ii:a)", "(?-:a)", "(?i-i:a)", "(?i:a)", "(?i-m:a)"];
for (var p of patterns) {
  var lit, ctor;
  try { (0, eval)("/" + p + "/"); lit = "no error"; } catch (e) { lit = e.constructor.name; }
  try { new RegExp(p); ctor = "no error"; } catch (e) { ctor = e.constructor.name; }
  print("/" + p + "/: " + lit + "; new RegExp: " + ctor);
}
