// §B.1.2.8: the range [\d-a] keeps both ClassAtoms, and CompileToCharSet on a host
// that supports §B.1.2 is CharacterRangeOrUnion: \d, "-" and "a", not "b"; with the
// u flag the range is an early error.
// Strict, so GlobalDeclarationInstantiation's B.3.2.2 step does not apply.
// args: --web-browser
// expect: normal: "true,true,true,false,SyntaxError"
"use strict";
var r = /[\d-a]/;
var u;
try { new RegExp("[\\d-a]", "u"); u = "none"; } catch (e) { u = e.name; }
[r.test("-"), r.test("5"), r.test("a"), r.test("b"), u].join()
