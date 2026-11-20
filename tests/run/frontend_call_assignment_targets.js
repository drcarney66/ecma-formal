// §B.3.9 on a web-browser host: a call is a ~web-compat~ assignment target in
// non-strict code; evaluation calls it, then throws a ReferenceError (the
// right-hand side is not evaluated). Strict code keeps the early error, and
// so do the lookahead restrictions of the for-of heads (§14.7.5: `let` cannot
// start the LeftHandSideExpression) and the early errors inside the call
// (§12.7 identifiers; the Annex B sections a host lacks: crates/jsparse/tests/lower.rs).
// args: --web-browser
// expect: normal: undefined
// print: ReferenceError 1 0
// print: ReferenceError 2 0
// print: ReferenceError 3 0
// print: ReferenceError 4 0
// print: ReferenceError 5 0
// print: ReferenceError 6 0
// print: ReferenceError 7 0
// print: SyntaxError
// print: SyntaxError
// print: SyntaxError
// print: SyntaxError
// print: ok
// print: ReferenceError
// print: SyntaxError
// print: ReferenceError
// print: ReferenceError
var calls = 0, rhs = 0;
function f() { calls++; return {}; }
function r() { rhs++; return 1; }
function t(g) { try { g(); print("no error"); } catch (e) { print(e.constructor.name + " " + calls + " " + rhs); } }
t(function () { f() = r(); });
t(function () { f()++; });
t(function () { ++(f()); });
t(function () { f() += r(); });
t(function () { for (f() in { a: 1 }) ; });
t(function () { for (f() of [1]) ; });
t(function () { (f()) = r(); });
try { eval("'use strict'; f() = 1"); } catch (e) { print(e.name); }
try { eval("f() &&= 1"); } catch (e) { print(e.name); }
try { eval("for (let() of []);"); } catch (e) { print(e.name); }
try { eval("async function g() { for await (let() of []); }"); } catch (e) { print(e.name); }
function let() { return {}; }
try { eval("for ((let()) of []); for (let() in {}); print('ok'); for (let() in { a: 1 });"); } catch (e) { print(e.name); }
try { eval("f(\\u0558) = 1"); } catch (e) { print(e.name); }
try { (f() <!-- comment
) = 1; } catch (e) { print(e.name); }
try { (f() /* comment */ ) = 1; } catch (e) { print(e.name); }
