// Math.random (§21.3.2.28) has no algorithm: EvaluateBuiltin asks the host's hook, and the
// default host answers by its seeded generator (a fixed seed without --host-seed), a Number in
// [+0, 1). Called as a method and through call, with an argument it ignores;
// `new` throws, as it is no constructor.
// expect: normal: "true|true|TypeError"
var r = Math.random();
var s = Math.random.call(undefined, 5);
function unit(x) { return typeof x === "number" && x >= 0 && x < 1 && !(x === 0 && 1 / x < 0); }
function name(thunk) { try { thunk(); return "none"; } catch (err) { return err.name; } }
unit(r) + "|" + unit(s) + "|" + name(function () { return new Math.random(); });
