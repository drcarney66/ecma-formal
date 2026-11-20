// WhiteSpace (§12.2) is TAB, VT, FF, ZWNBSP and the Zs code points: U+0085
// (NEL) and U+200B (ZWSP) between tokens are SyntaxErrors; in a string, a
// comment or a template they are SourceCharacters.
// expect: normal: undefined
// print: SyntaxError
// print: SyntaxError
// print: 3
// print: 3
// print: 2
// print: 7
function t(s) { try { print(String(eval(s))); } catch (e) { print(e.name); } }
t("1\u0085+ 2");
t("1​+ 2");
t("1　+﻿2");
t("1 + 2");
t("'\u0085​'.length");
t("/*\u0085*/ `​`.length + 6");
