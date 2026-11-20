// The unary operators (§13.5) and the update operators (§13.4), the operand
// suspending.
// sections: sec-delete-operator-runtime-semantics-evaluation sec-typeof-operator-runtime-semantics-evaluation sec-unary-plus-operator-runtime-semantics-evaluation sec-unary-minus-operator-runtime-semantics-evaluation sec-bitwise-not-operator-runtime-semantics-evaluation sec-logical-not-operator-runtime-semantics-evaluation sec-postfix-increment-operator-runtime-semantics-evaluation sec-postfix-decrement-operator-runtime-semantics-evaluation sec-prefix-increment-operator-runtime-semantics-evaluation sec-prefix-decrement-operator-runtime-semantics-evaluation sec-property-accessors-runtime-semantics-evaluation sec-evaluate-property-access-with-expression-key
function plain() {
  Math.max();
  var o = { p: 1 };
  typeof (void 1); +(void 1); -(void 1); ~(void 1); !(void 1);
  delete o[void "p"];
  o[void "p"]++; o[void "p"]--; ++o[void "p"]; --o[void "p"];
  Math.min();
}
function* gen() {
  Math.max();
  var o = { p: 1 };
  typeof (yield 1); +(yield 1); -(yield 1); ~(yield 1); !(yield 1);
  delete o[yield "p"];
  o[yield "p"]++; o[yield "p"]--; ++o[yield "p"]; --o[yield "p"];
  Math.min();
}
