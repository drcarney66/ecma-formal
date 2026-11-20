// expect: throw: RangeError
// BigInt::leftShift whose result has more than 2^30 bits throws a RangeError
// (erratum BigIntMaximumSize, proposed reading), not a runtime abort
// (BigInt.shiftLeft).
2n << (1n << 64n);
