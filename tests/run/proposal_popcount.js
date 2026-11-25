// expect: normal: undefined
// print: ok

function assertEq(actual, expected, msg) {
  if (!Object.is(actual, expected)) {
    throw new Error((msg || "mismatch") + ": got " + String(actual) + ", expected " + String(expected));
  }
}

assertEq(Math.ctz32.length, 1, "ctz32 length");
assertEq(Math.ctz32.name, "ctz32", "ctz32 name");
assertEq(Math.popcount32.length, 1, "popcount32 length");
assertEq(Math.popcount32.name, "popcount32", "popcount32 name");

// Zero & signed zero
assertEq(Math.ctz32(0), 32, "ctz32(+0)");
assertEq(Math.ctz32(-0), 32, "ctz32(-0)");
assertEq(Math.popcount32(0), 0, "popcount32(+0)");
assertEq(Math.popcount32(-0), 0, "popcount32(-0)");

// Powers of 2 and bit patterns
for (let k = 0; k < 32; k++) {
  const v = (1 << k) >>> 0;
  assertEq(Math.ctz32(v), k, "ctz32 2^" + k);
  assertEq(Math.popcount32(v), 1, "popcount32 2^" + k);
}

assertEq(Math.ctz32(-1), 0, "ctz32(-1)");
assertEq(Math.popcount32(-1), 32, "popcount32(-1)");
assertEq(Math.ctz32(0x80000000), 31, "ctz32(0x80000000)");
assertEq(Math.popcount32(0xaaaaaaaa), 16, "popcount32(0xaaaaaaaa)");
assertEq(Math.popcount32(0x55555555), 16, "popcount32(0x55555555)");
assertEq(Math.ctz32(12), 2, "ctz32(12)");
assertEq(Math.popcount32(12), 2, "popcount32(12)");

// ToUint32 coercion
assertEq(Math.ctz32(NaN), 32, "ctz32(NaN)");
assertEq(Math.ctz32(Infinity), 32, "ctz32(Infinity)");
assertEq(Math.popcount32(NaN), 0, "popcount32(NaN)");
assertEq(Math.ctz32("8"), 3, "ctz32('8')");
assertEq(Math.popcount32("7"), 3, "popcount32('7')");

print("ok");
