// Proxy [[Get]] (§10.5.8) step 9.a.i: a trap may not report another value for
// a non-writable, non-configurable data property of the target.
// expect: throw: TypeError
var target = {};
Object.defineProperty(target, "x", { value: 1, writable: false, configurable: false });
var p = new Proxy(target, { get: function () { return 2; } });
p.x
