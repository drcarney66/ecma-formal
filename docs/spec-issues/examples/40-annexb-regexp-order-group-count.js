// §B.1.2: "each alternative is considered only if previous production alternatives do not match", and
// AtomEscape's DecimalEscape "only if the CapturingGroupNumber of DecimalEscape is ≤
// CountLeftCapturingParensWithin(the Pattern containing DecimalEscape)". Each pattern is compiled with no
// flags; the string is matched against it.
if (typeof print === "undefined") globalThis.print = console.log;
var cases = [["a{1}", "a"], ["\\b*", ""], ["a\\b?", "ab"], ["\\x4", "x4"], ["{,1}", "{,1}"], ["[\\b]", "\b"],
             ["\\c1", "\\c1"], ["\\1(a)", "a"], ["\\2(a)(b)", "ab"], ["\\3(a)(b)", "\x03ab"], ["(a)\\10", "a\x08"],
             ["\\1", "\x01"]];
for (var [p, s] of cases) {
  var r;
  try { r = String(new RegExp(p).test(s)); } catch (e) { r = e.constructor.name; }
  print(JSON.stringify(p) + " on " + JSON.stringify(s) + ": " + r);
}
