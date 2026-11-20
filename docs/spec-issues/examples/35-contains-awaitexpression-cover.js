// Contains (§8.5.1) has no row for UnaryExpression :
// CoverAwaitExpressionAndAwaitUsingDeclarationHead, the production an `await`
// expression parses as, so literally no Parse Node contains an
// AwaitExpression and the rules "FormalParameters Contains AwaitExpression"
// never apply. Each source is evaluated as a Script (indirect eval) or by the
// AsyncFunction constructor; test262 expects a SyntaxError for the first six
// and none for the last three.
if (typeof print === "undefined") globalThis.print = console.log;
var AsyncFunction = (async function () {}).constructor;
var cases = [
  ["async function f(x = await 1) {}", () => (0, eval)("async function f(x = await 1) {}")],
  ["(async function* (x = await 1) {})", () => (0, eval)("(async function* (x = await 1) {})")],
  ["({ async m(x = await 1) {} })", () => (0, eval)("({ async m(x = await 1) {} })")],
  ["({ async *m(x = await 1) {} })", () => (0, eval)("({ async *m(x = await 1) {} })")],
  ["async function g() { async (x = await 1) => 0; }", () => (0, eval)("async function g() { async (x = await 1) => 0; }")],
  ["AsyncFunction('x = await 1', '')", () => AsyncFunction("x = await 1", "")],
  ["async function h() { await 1; }", () => (0, eval)("async function h() { await 1; }")],
  ["async function k(x = function () { var await; }) {}", () => (0, eval)("async function k(x = function () { var await; }) {}")],
  ["(async function () { class C { static { } } })", () => (0, eval)("(async function () { class C { static { } } })")],
];
for (var [src, run] of cases) {
  try { run(); print(src + ": no error"); }
  catch (e) { print(src + ": " + e.constructor.name); }
}
