// expect: normal: "ok"
// IsStrict is computed in Lean from the source (§11.2.2), never taken from the
// frontend: 'use\x20strict' has the SV "use strict" but is not a Use Strict
// Directive, so f is sloppy and its `this` is the global object.
function f() { 'use\x20strict'; return this; }
function g() { 'use strict'; return this; }
// A function nested in strict code is strict; one in sloppy code is not.
function h() { 'use strict'; return function () { return this; }; }
function k() { return function () { return this; }; }
// A class body is strict code, so its methods are.
class C { static m() { return (function () { return this; })(); } }
// A strict generator keeps its strictness after a `yield` (the resumed frame's
// Cx comes from F.[[Strict]]).
function* gen() { 'use strict'; yield 1; yield this; try { undeclared = 1; } catch (e) { yield e instanceof ReferenceError; } }
var it = gen();
it.next();
var afterYield = it.next().value;
var refErr = it.next().value;
// A sloppy generator is not strict after a `yield` either.
function* sgen() { yield 1; yield this; }
var sit = sgen();
sit.next();
var sloppyAfterYield = sit.next().value;
// Dynamic function code is strict only by its own directive.
var df = Function("return this;");
var dg = Function("'use strict'; return this;");
(f() === globalThis && g() === undefined && h()() === undefined && k()() === globalThis &&
  C.m() === undefined && afterYield === undefined && refErr === true &&
  sloppyAfterYield === globalThis && df() === globalThis && dg() === undefined) ? "ok" : "fail"
