// The comma operator (§13.16.1), both operands suspending.
// sections: sec-comma-operator-runtime-semantics-evaluation
function plain() {
  Math.max();
  (void 1), (void 2);
  Math.min();
}
function* gen() {
  Math.max();
  (yield 1), (yield 2);
  Math.min();
}
