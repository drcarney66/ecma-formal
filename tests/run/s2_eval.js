// eval (§19.2.1: PerformEval, EvalDeclarationInstantiation) and the Function
// constructor (§20.2.1: CreateDynamicFunction), parsed at run time by jsparse.
// expect: normal: "3|20|10|5,7|number,undefined|undefined|42,anonymous,2|function anonymous(a,b\n) {\nreturn a * b\n}|SyntaxError|SyntaxError|true|false,|3|false,true|,5|SyntaxError"
var x = 10;
function f() { var x = 20; return eval("x"); }
function g() { var x = 20; return (0, eval)("x"); }
function nt() { return eval("new.target"); }
function tag(s) { return s; }
function cache() { return tag`b`; }
function name(thunk) { try { thunk(); return "none"; } catch (e) { return e.name; } }
class C { #p = 3; get() { return eval("this.#p"); } }
var o = { m() { return eval("super.toString === Object.prototype.toString"); } };
eval("var y = 5; function h() { return 7; }");
var F = new Function("a", "b", "return a * b");
var r = [
  eval("1 + 2"),
  f(),
  g(),
  [y, h()],
  [typeof eval("let z = 1; z"), typeof z],
  (function () { "use strict"; eval("var w = 1"); return typeof w; })(),
  [F(6, 7), F.name, F.length],
  String(F),
  name(function () { eval("super.x"); }),
  // the parameters and the body are each parsed alone
  name(function () { new Function("/", "/ ) {"); }),
  o.m(),
  [new nt() === undefined, nt()],
  new C().get(),
  // two parses of one text are different Parse Nodes, with different template objects
  [eval("tag`a`") === eval("tag`a`"), cache() === cache()],
  [eval(""), eval(5)],
  name(function () { let q; eval("var q"); })
];
r.join("|")
