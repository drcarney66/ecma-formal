// expect: normal: undefined
// print: ok

function assertEq(actual, expected, msg) {
  if (!Object.is(actual, expected)) {
    throw new Error((msg || "mismatch") + ": got " + String(actual) + ", expected " + String(expected));
  }
}

function assertThrowsTypeError(fn, msg) {
  let threw = false;
  try {
    fn();
  } catch (e) {
    threw = e instanceof TypeError;
    if (!threw) throw e;
  }
  if (!threw) throw new Error("expected TypeError: " + msg);
}

// Descriptor and metadata
const desc = Object.getOwnPropertyDescriptor(Math, "fusedMultiplyAdd");
assertEq(desc.writable, true, "writable");
assertEq(desc.enumerable, false, "enumerable");
assertEq(desc.configurable, true, "configurable");
assertEq(Math.fusedMultiplyAdd.length, 3, "length");
assertEq(Math.fusedMultiplyAdd.name, "fusedMultiplyAdd", "name");

// Single rounding (no intermediate rounding of x * y):
// (1 + 2^-52) * (1 - 2^-52) = 1 - 2^-104 exactly; adding -1 yields -2^-104.
// Naive (a * b) + (-1) rounds (a * b) to 1 first and yields +0!
const a = 1 + 2 ** -52;
const b = 1 - 2 ** -52;
assertEq((a * b) + (-1), 0, "naive double rounding");
assertEq(Math.fusedMultiplyAdd(a, b, -1), -(2 ** -104), "exact FMA single rounding");

// Exact cancellation of large products
const c = 1 + 2 ** -27;
assertEq(Math.fusedMultiplyAdd(c, c, -(1 + 2 ** -26)), 2 ** -54, "exact low bit preserved");

// Signed zero rules (IEEE 754-2019)
assertEq(Math.fusedMultiplyAdd(0, 5, 0), 0, "+0 * 5 + +0");
assertEq(Math.fusedMultiplyAdd(-0, 5, 0), 0, "-0 * 5 + +0");
assertEq(Math.fusedMultiplyAdd(-0, 5, -0), -0, "-0 * 5 + -0");
assertEq(Math.fusedMultiplyAdd(0, -5, -0), -0, "+0 * -5 + -0");
assertEq(Math.fusedMultiplyAdd(2, 3, -6), 0, "exact cancellation yields +0");

// Infinities and NaN
assertEq(Math.fusedMultiplyAdd(Infinity, 2, -Infinity), NaN, "+Inf + -Inf = NaN");
assertEq(Math.fusedMultiplyAdd(-Infinity, 2, Infinity), NaN, "-Inf + +Inf = NaN");
assertEq(Math.fusedMultiplyAdd(Infinity, 0, 1), NaN, "Inf * 0 + 1 = NaN");
assertEq(Math.fusedMultiplyAdd(0, -Infinity, 1), NaN, "0 * -Inf + 1 = NaN");
assertEq(Math.fusedMultiplyAdd(1, 2, Infinity), Infinity, "finite + +Inf");
assertEq(Math.fusedMultiplyAdd(1, 2, -Infinity), -Infinity, "finite + -Inf");
assertEq(Math.fusedMultiplyAdd(NaN, 1, 2), NaN, "NaN x");
assertEq(Math.fusedMultiplyAdd(1, NaN, 2), NaN, "NaN y");
assertEq(Math.fusedMultiplyAdd(1, 2, NaN), NaN, "NaN z");

// Strict Number check (no coercion; throws TypeError on non-Numbers)
assertThrowsTypeError(() => Math.fusedMultiplyAdd("1", 2, 3), "string x");
assertThrowsTypeError(() => Math.fusedMultiplyAdd(1, "2", 3), "string y");
assertThrowsTypeError(() => Math.fusedMultiplyAdd(1, 2, "3"), "string z");
assertThrowsTypeError(() => Math.fusedMultiplyAdd(1n, 2, 3), "BigInt x");
assertThrowsTypeError(() => Math.fusedMultiplyAdd(1, 2), "missing z (undefined)");

print("ok");
