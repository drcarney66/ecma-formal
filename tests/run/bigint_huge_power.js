// expect: throw: RangeError
// BigInt::exponentiate throws a RangeError (erratum BigIntMaximumSize, proposed
// reading), not a runtime abort, when the result would have more than 2^30 bits
// (BigInt.pow).
3n ** (1n << 40n);
