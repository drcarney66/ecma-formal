var srcs = [
  "let a; let a;", "break;", "x: while (1) { continue y; }", "({a} = 1)", "({a: 1} = 1)",
  "(a, b) => a", "(a, a) => 1", "function f(a, a) {}", "'use strict'; function g(a, a) {}",
  "new.target", "({__proto__: 1, __proto__: 2})", "class C { constructor() {} constructor() {} }",
  "class D { #p; m() { return this.#q; } }", "/(?<n>a)(?<n>b)/", "var yield;",
  "async function h() { await: 1; }", "for (let let of []) ;", "1 = 2", "({ get x(a) {} })",
  "if (1) function q() {}", "[a, ...b, c] = []", "`${1}` = 1", "super.x", "({ m() { super(); } })",
  "let [x, x] = [];", "try {} catch (e) { let e; }", "'use strict'; with (a) {}", "delete x",
  "export var z;", "return 1"
];
var out = [];
for (var i = 0; i < srcs.length; i++) {
  try { new Function(srcs[i]); out.push(0); } catch (e) { out.push(e instanceof SyntaxError ? 1 : 2); }
}
print(out.join(""));
