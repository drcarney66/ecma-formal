// The equality operators (§13.11.1), an operand suspending.
// sections: sec-equality-operators-runtime-semantics-evaluation
function plain() {
  Math.max();
  (void 1) == 2; (void 1) != 2; (void 1) === 2; (void 1) !== 2;
  1 == (void 2);
  Math.min();
}
function* gen() {
  Math.max();
  (yield 1) == 2; (yield 1) != 2; (yield 1) === 2; (yield 1) !== 2;
  1 == (yield 2);
  Math.min();
}
