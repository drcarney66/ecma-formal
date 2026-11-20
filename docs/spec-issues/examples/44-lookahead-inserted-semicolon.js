// ExpressionStatement's [lookahead ∉ { let [ }] and a semicolon that §12.10 inserts before `[`: whether the
// lookahead reads the inserted `;`. Each source is parsed (not run) as a function body in a Script.
if (typeof print === "undefined") globalThis.print = console.log;
var sources = ["if (false) let\n[a] = 0;", "while (false) let\n[a] = 0;", "if (false) let\n{}",
               "if (false) let;\n[a] = 0;"];
for (var s of sources) {
  try { (0, eval)("(function () {\n" + s + "\n})"); print(JSON.stringify(s) + ": no error"); }
  catch (e) { print(JSON.stringify(s) + ": " + e.constructor.name); }
}
