// §B.3.3 on a web-browser host: the synthetic Block's function is not bound in
// the var scope where `var f` would conflict with a `let f` (§B.3.2.2).
// args: --web-browser
// expect: normal: 1
let f = 1;
{ if (true) function f(){} }
f
