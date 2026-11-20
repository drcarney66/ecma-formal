// Property accesses (§13.3.2), calls (§13.3.6), `new` (§13.3.5) and
// argument lists (§13.3.8), an operand or an argument suspending.
// sections: sec-property-accessors-runtime-semantics-evaluation sec-evaluate-property-access-with-expression-key sec-function-calls-runtime-semantics-evaluation sec-evaluatecall sec-new-operator-runtime-semantics-evaluation sec-evaluatenew sec-runtime-semantics-argumentlistevaluation
function plain() {
  Math.max();
  var o = { m(a, b) { return a; }, p: 1 };
  function F(a) {}
  o[(void 0, "p")]; (void 0, o).p;
  o.m(void 1, ...[2]);
  o[(void 0, "m")](3);
  (void 0, o.m)(4);
  new F(void 1);
  Math.min();
}
function* gen() {
  Math.max();
  var o = { m(a, b) { return a; }, p: 1 };
  function F(a) {}
  o[(yield 0, "p")]; (yield 0, o).p;
  o.m(yield 1, ...[2]);
  o[(yield 0, "m")](3);
  (yield 0, o.m)(4);
  new F(yield 1);
  Math.min();
}
