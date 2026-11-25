// expect: normal: undefined
// print: ok

function assertEq(actual, expected, msg) {
  if (!Object.is(actual, expected)) {
    throw new Error((msg || "mismatch") + ": got " + String(actual) + ", expected " + String(expected));
  }
}

// 1. Identity & canonical key ordering
const c1 = Composite({ y: 4, x: 1, 10: "ten", 2: "two" });
const c2 = Composite({ 2: "two", x: 1, 10: "ten", y: 4 });
assertEq(c1 === c2, true, "interned identity regardless of input key order");
assertEq(Object.keys(c1).join(","), "2,10,x,y", "canonical key order: numeric array indices then lexicographic");
assertEq(Object.getPrototypeOf(c1), null, "null prototype");
assertEq(Object.isFrozen(c1), true, "frozen");
assertEq(Composite.isComposite(c1), true, "Composite.isComposite true");
assertEq(Composite.isComposite({}), false, "Composite.isComposite false on ordinary object");

// 2. Map/Set value-based lookup via interned identity
const set = new Set([Composite({ a: 1, b: 2 })]);
assertEq(set.has(Composite({ b: 2, a: 1 })), true, "Set lookup by composite equality");

// 3. -0 normalization vs preserveNegativeZero
const posZero = Composite({ z: -0 });
assertEq(Object.is(posZero.z, +0), true, "-0 normalized to +0 by default");
const negZero = Composite({ z: -0 }, { preserveNegativeZero: true });
assertEq(Object.is(negZero.z, -0), true, "-0 preserved with option");
assertEq(posZero === negZero, false, "+0 and -0 composites are distinct");
assertEq(Composite(negZero) === negZero, true, "passing a composite preserves -0 by default");

// 4. Not constructible with `new`, Symbol keys rejected, WeakSet/WeakMap rejected (CanBeHeldWeakly = false)
let newThrew = false;
try { new Composite({}); } catch (e) { newThrew = e instanceof TypeError; }
assertEq(newThrew, true, "new Composite throws TypeError");

let symThrew = false;
try { Composite({ [Symbol("s")]: 1 }); } catch (e) { symThrew = e instanceof TypeError; }
assertEq(symThrew, true, "enumerable Symbol key throws TypeError");

let weakThrew = false;
try { new WeakSet().add(c1); } catch (e) { weakThrew = e instanceof TypeError; }
assertEq(weakThrew, true, "composite cannot be held weakly");

print("ok");
