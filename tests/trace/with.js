// The WithStatement (§14.11.2): its Expression and Statement suspending.
// sections: sec-with-statement-runtime-semantics-evaluation
function plain() {
  Math.max();
  with (void 0, {}) 0;
  with ({}) void 1;
  Math.min();
}
function* gen() {
  Math.max();
  with (yield 0, {}) 0;
  with ({}) yield 1;
  Math.min();
}
