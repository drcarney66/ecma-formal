// On a web-browser host, a FunctionDeclaration in a Block is also a var of the
// enclosing function (§B.3.2.1), set when the declaration is evaluated.
// args: --web-browser
// expect: normal: "undefined,function,2"
function g() {
  var before = typeof f;
  { function f() { return 2; } }
  return [before, typeof f, f()].join();
}
g()
