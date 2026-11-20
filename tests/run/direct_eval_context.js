// PerformEval's parse is a direct eval's: Script's early errors waive super,
// new.target and private names (§16.1.1), and PerformEval's own checks decide.
// expect: normal: "ok,SyntaxError,SyntaxError,ok,SyntaxError,ok,SyntaxError,SyntaxError,1,SyntaxError"
function name(thunk) { try { thunk(); return "ok"; } catch (e) { return e.constructor.name; } }
function nt() { return eval("new.target"); }
function ntIndirect() { return (0, eval)("new.target"); }
var o = { __proto__: { x: 3 }, m() { return eval("super.x"); } };
class B {}
class D extends B { constructor() { eval("super()"); } }
class E { constructor() { eval("super()"); } }
class F { f = eval("arguments"); }
var top;
try { eval("new.target"); top = "ok"; } catch (e) { top = e.constructor.name; }
class C {
  #x = 1;
  g() { return eval("this.#x"); }
  h() { return (0, eval)("this.#x"); }
}
var r = [
  name(function () { new nt(); }),
  top,
  name(function () { new ntIndirect(); }),
  name(function () { if (o.m() !== 3) throw 0; }),
  name(function () { (function () { return eval("super.x"); })(); }),
  name(function () { new D(); }),
  name(function () { new E(); }),
  name(function () { new F(); }),
  new C().g(),
  name(function () { new C().h(); })
];
r.join(",")
