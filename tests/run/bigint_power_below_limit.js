// expect: normal: undefined
// print: true 729 4
// print: true -243 1
// BigInt::exponentiate whose result has at most 2^30 bits is computed: the
// bound is the result's size (3n ** 5592406n has 8863754 bits).
print([3n ** 5592406n > 0n, (3n ** 5592406n) % 1000n, (10n ** 4000000n) % 7n].join(" "));
print([(-3n) ** 5592405n < 0n, ((-3n) ** 5592405n) % 1000n, BigInt.asUintN(8, 3n ** 6000000n)].join(" "));
