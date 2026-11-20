// Proxy [[OwnPropertyKeys]] (§10.5.11): the trap's result must list every
// non-configurable key of the target (step 19.a) and no duplicates (step 9).
// expect: normal: "TypeError|TypeError|y"
var target = {};
Object.defineProperty(target, "x", { value: 1, configurable: false });
var missing = new Proxy(target, { ownKeys: function () { return ["y"]; } });
var dup = new Proxy({}, { ownKeys: function () { return ["a", "a"]; } });
var r1, r2;
try { Object.keys(missing); } catch (e) { r1 = e.constructor.name; }
try { Reflect.ownKeys(dup); } catch (e) { r2 = e.constructor.name; }
var ok = new Proxy({}, { ownKeys: function () { return ["y"]; } });
r1 + "|" + r2 + "|" + Reflect.ownKeys(ok).join(",")
