// expect: normal: undefined
// print: 0 -1 0 0
// print: 0 -1 0
// print: 1 1 -1 0 1
// print: 40 -3 1024 -3
// BigInt::leftShift, signedRightShift and exponentiate with a shift count or
// exponent of 2^32 or more give the spec's result when it is small: the
// executable never builds the power 2^n (before, its Nat.pow aborted the run).
var big = 1n << 64n;
print([5n >> big, -5n >> big, 0n << big, 5n >> 4294967296n].join(" "));
print([1n >> 4294967296n, -1n >> big, 0n << 4294967296n].join(" "));
print([1n ** big, (-1n) ** big, (-1n) ** (big + 1n), 0n ** big, 0n ** 0n].join(" "));
print([5n << 3n, -5n >> 1n, 2n ** 10n, -5n << -1n].join(" "));
