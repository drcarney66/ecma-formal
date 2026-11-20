// The relational operators (§13.10.1), an operand suspending.
// sections: sec-relational-operators-runtime-semantics-evaluation
function plain() {
  Math.max();
  (void 1) < 2; (void 1) > 2; (void 1) <= 2; (void 1) >= 2;
  1 < (void 2);
  try { (void 1) instanceof Object; (void 1) in {}; } catch (e) {}
  Math.min();
}
function* gen() {
  Math.max();
  (yield 1) < 2; (yield 1) > 2; (yield 1) <= 2; (yield 1) >= 2;
  1 < (yield 2);
  try { (yield 1) instanceof Object; (yield 1) in {}; } catch (e) {}
  Math.min();
}
