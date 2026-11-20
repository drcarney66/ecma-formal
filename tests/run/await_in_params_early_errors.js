// expect: normal: undefined
// print: async function: SyntaxError
// print: async function expression: SyntaxError
// print: async generator: SyntaxError
// print: async generator expression: SyntaxError
// print: async method: SyntaxError
// print: async generator method: SyntaxError
// print: arrow in async body: SyntaxError
// print: async arrow in async body: SyntaxError
// print: AsyncFunction: SyntaxError
// print: AsyncGeneratorFunction: SyntaxError
// print: await in async body: no error
// print: static block in async function: no error
// print: var await in nested function: no error
// print: async arrow parameters: no error
// print: await in static block: SyntaxError
// print: var await in static block function: no error
// The early errors "X Contains |AwaitExpression|" (§15.3.1, §15.6.1, §15.8.1,
// §15.9.1): an `await` expression is the cover of UnaryExpression :
// CoverAwaitExpressionAndAwaitUsingDeclarationHead, which Contains counts as an
// AwaitExpression (Erratum ContainsAwaitCover, its test262 reading).
// Contains does not look into nested functions, and a static block's rule is
// on the terminal `await`.
var AsyncFunction = (async function () {}).constructor;
var AsyncGeneratorFunction = (async function* () {}).constructor;
function check(name, run) {
  try { run(); print(name + ": no error"); }
  catch (e) { print(name + ": " + e.constructor.name); }
}
function script(src) { return function () { (0, eval)(src); }; }
check("async function", script("async function f(x = await 1) {}"));
check("async function expression", script("(async function (x = await 1) {})"));
check("async generator", script("async function* f(x = await 1) {}"));
check("async generator expression", script("(async function* (x = await 1) {})"));
check("async method", script("({ async m(x = await 1) {} })"));
check("async generator method", script("({ async *m(x = await 1) {} })"));
check("arrow in async body", script("async function g() { (x = await 1) => 0; }"));
check("async arrow in async body", script("async function g() { async (x = await 1) => 0; }"));
check("AsyncFunction", function () { AsyncFunction("x = await 1", ""); });
check("AsyncGeneratorFunction", function () { AsyncGeneratorFunction("x = await 1", ""); });
check("await in async body", script("async function h() { await 1; }"));
check("static block in async function", script("(async function () { class C { static { } } })"));
check("var await in nested function", script("async function k(x = function () { var await; }) {}"));
check("async arrow parameters", script("async (x = 1) => await x;"));
check("await in static block", script("class C { static { await 0; } }"));
check("var await in static block function", script("class C { static { (function () { var await; }); } }"));
