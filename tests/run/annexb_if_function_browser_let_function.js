// §B.3.3 on a web-browser host in function code: the synthetic Block's function
// is not bound in the function's var scope where `var f` would conflict with a
// `let f` (§B.3.2.1).
// args: --web-browser
// expect: normal: 1
function g(){ let f = 1; { if (true) function f(){} } return f; }
g()
