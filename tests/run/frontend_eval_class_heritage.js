// Direct eval: NewTarget and SuperProperty in a class's heritage or computed
// keys are the caller's (ClassTail Contains searches them, PerformEval step
// 11), not early errors of the eval code; a class element's own are.
// expect: normal: undefined
// print: function
// print: function
// print: function
// print: function
// print: SyntaxError
// print: SyntaxError
function t(f) { try { print(String(f())); } catch (e) { print(e.name); } }
var o = { m() { return eval("(class extends (super.constructor) {})"); } };
t(() => typeof o.m());
function f1() { return eval("(class extends (new.target ? Object : Object) {})"); }
t(() => typeof f1());
function f2() { return eval("(class { [new.target]() {} })"); }
t(() => typeof f2());
var o2 = { m() { return eval("(class { [super.x]() {} })"); } };
t(() => typeof o2.m());
t(() => eval("(class { [new.target]() {} })"));
function f3() { return eval("(class { x = super() })"); }
t(() => f3());
