// Unary + on a BigInt is a TypeError (ToNumber), unlike unary -.
// expect: throw: TypeError
-1n, +1n
