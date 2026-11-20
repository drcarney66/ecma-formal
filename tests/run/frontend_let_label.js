// `let` is a LabelIdentifier in non-strict code (§14.13): `let :` cannot start
// a LexicalDeclaration. In strict code it is an early error.
// expect: normal: undefined
// print: 0
// print: block
// print: SyntaxError
// print: 1 2
// print: 3
// print: 4
let: for (var i = 0; i < 3; i++) { if (i == 1) continue let; if (i == 2) break let; print(i); }
let: { print("block"); break let; print("not reached"); }
try { eval("'use strict'; let: 1"); } catch (e) { print(e.name); }
function g() { let: for (;;) { break let; } var n = 0; let: for (; n < 2; n++) { continue /* c */ let; } return 1 + " " + n; }
print(g());
let /* c */ : print(3);
let // c
: print(4);
