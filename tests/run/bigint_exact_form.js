// expect: throw: RangeError
// print: 0 0 0
// Shifting 0n avoids forming 2^y; under default BigIntMaximumSize=proposed,
// an operation exceeding 2^30 bits (3n ** (1n << 40n)) throws a RangeError.
print([0n << (2n ** 100n), 0n >> -(2n ** 100n), 0n << 16777217n].join(" "));
var a = 1n << 33554432n;
print([a > 0n, 3n ** (1n << 40n) > 0n, a < (1n << 33554431n), a === 2n ** 33554432n].join(" "));
print([(a - 1n) % 2n, BigInt.asUintN(64, a + 3n), BigInt.asIntN(8, -a - 1n), -a < 0n].join(" "));
