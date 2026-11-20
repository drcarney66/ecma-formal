// expect: normal: "function|TypeError"
// IsCallable (§7.2.3), asked by EvaluateCall of a callee that is an Object: a function
// has a [[Call]] internal method (step 2 returns true); an ordinary object has none,
// step 3 returns false, and the call throws a TypeError.
function f() { return "function"; }
var o = {};
var r = f();
try { o(); } catch (e) { r += "|" + e.constructor.name; }
r;
