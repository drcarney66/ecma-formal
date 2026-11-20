// The conditional operator (§13.14.1), each operand suspending.
// sections: sec-conditional-operator-runtime-semantics-evaluation
function plain() {
  Math.max();
  (void 1) ? 2 : 3;
  1 ? (void 2) : 3;
  0 ? 2 : (void 3);
  Math.min();
}
function* gen() {
  Math.max();
  (yield 1) ? 2 : 3;
  1 ? (yield 2) : 3;
  0 ? 2 : (yield 3);
  Math.min();
}
