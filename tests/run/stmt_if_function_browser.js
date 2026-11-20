// §B.3.3 on a web browser host: `if (x) function f() {}` is the synthetic
// Block `{ function f() {} }`, whose function is instantiated and, by §B.3.2.1,
// also bound in the enclosing var scope.
// args: --web-browser
// expect: normal: "function"
if (true) function f() {}
typeof f
