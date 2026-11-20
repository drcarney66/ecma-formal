// Identifier references, `this` and literals (§13.1, §13.2.1, §13.2.3), the
// grouping operator (§13.2.9), function and arrow function expressions
// (§15.2, §15.3) and expression statements (§14.5), an operand suspending.
// sections: sec-identifiers-runtime-semantics-evaluation sec-this-keyword-runtime-semantics-evaluation sec-literals-runtime-semantics-evaluation sec-grouping-operator-runtime-semantics-evaluation sec-function-definitions-runtime-semantics-evaluation sec-arrow-function-definitions-runtime-semantics-evaluation sec-expression-statement-runtime-semantics-evaluation
function plain() {
  Math.max();
  var x = 1, a;
  (void x);
  ((void 1), x);
  [this, x, null, true, false, "s", 2n, 3, void 1];
  a = [function () {}, function f() {}, () => x, void 1];
  Math.min();
}
function* gen() {
  Math.max();
  var x = 1, a;
  (yield x);
  ((yield 1), x);
  [this, x, null, true, false, "s", 2n, 3, yield 1];
  a = [function () {}, function f() {}, () => x, yield 1];
  Math.min();
}
