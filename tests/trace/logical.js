// The binary logical operators (§13.13.1), each operand suspending, with and
// without the short circuit.
// sections: sec-binary-logical-operators-runtime-semantics-evaluation
function plain() {
  Math.max();
  (void 1) && 2; 1 && (void 2);
  (void 1) || 2; 0 || (void 2);
  (void 1) ?? 2; null ?? (void 2); 1 ?? (void 2);
  Math.min();
}
function* gen() {
  Math.max();
  (yield 1) && 2; 1 && (yield 2);
  (yield 1) || 2; 0 || (yield 2);
  (yield 1) ?? 2; null ?? (yield 2); 1 ?? (yield 2);
  Math.min();
}
