// A FunctionDeclaration whose replacement by a var would conflict with an
// enclosing let (an Early Error) is not hoisted (§B.3.2.1 step 32.a.i.2).
// args: --web-browser
// expect: normal: "undefined,function"
function g() {
  var inner;
  { let f = 1; { function f() {} inner = typeof f; } }
  return [typeof f, inner].join();
}
g()
