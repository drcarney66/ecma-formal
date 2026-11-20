// Nested operators of one kind, an operand suspending: the steps of the inner
// one come between those of the outer, in the same order (§13.13.1, §13.14.1,
// §13.16.1).
// sections: sec-binary-logical-operators-runtime-semantics-evaluation sec-conditional-operator-runtime-semantics-evaluation sec-comma-operator-runtime-semantics-evaluation
function plain() {
  Math.max();
  (void 1) || ((void 2) && 3);
  1 && (0 || (void 3));
  (void 1) ? 2 : ((void 3) ? 4 : 5);
  1 ? (0 ? 2 : (void 3)) : 4;
  ((void 1), (void 2)), (void 3);
  Math.min();
}
function* gen() {
  Math.max();
  (yield 1) || ((yield 2) && 3);
  1 && (0 || (yield 3));
  (yield 1) ? 2 : ((yield 3) ? 4 : 5);
  1 ? (0 ? 2 : (yield 3)) : 4;
  ((yield 1), (yield 2)), (yield 3);
  Math.min();
}
