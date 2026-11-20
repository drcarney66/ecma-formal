// The left operand is evaluated first: its TypeError, not the right's, is thrown.
// expect: throw: TypeError
("x" in 1) == void 0
