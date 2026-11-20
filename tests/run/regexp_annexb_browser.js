// §B.1.2 on a web browser host: `\1` with no group is a legacy octal escape
// (U+0001), and `[\d-a]` is the union of \d, "-" and "a" (CharacterRangeOrUnion).
// Strict, so GlobalDeclarationInstantiation's B.3.2.2 step does not apply.
// args: --web-browser
// expect: normal: "true,true,true"
"use strict";
[new RegExp("\\1").test("\u0001"), /[\d-a]/.test("-"), /[\d-a]/.test("5")].join()
