// expect: normal: undefined
// print: 5 -5 5 1
// print: 0 -1 -4 -4 3 7 18446744073709551615
// BigInt.asIntN and BigInt.asUintN with bits up to 2^53 - 1 (ToIndex): the
// result is ℝ(bigint) itself when it is already in range, which the
// executable computes without forming 2^bits (§21.2.2.1, §21.2.2.2).
print(String(BigInt.asUintN(2**53-1, 5n)) + " " + String(BigInt.asIntN(2**53-1, -5n)) + " " +
  String(BigInt.asIntN(2**40, 5n)) + " " + String(BigInt.asUintN(2**32, 1n)));
print(String(BigInt.asIntN(0, 5n)) + " " + String(BigInt.asIntN(1, 1n)) + " " + String(BigInt.asIntN(3, 4n)) + " " +
  String(BigInt.asIntN(3, -4n)) + " " + String(BigInt.asIntN(3, -5n)) + " " + String(BigInt.asUintN(3, -1n)) + " " +
  String(BigInt.asUintN(64, -1n)));
