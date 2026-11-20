// The productions whose meaning is EvaluateStringOrNumericBinaryExpression
// (§13.6–§13.9, §13.12, §13.15.4), an operand suspending.
// sections: sec-evaluatestringornumericbinaryexpression sec-exp-operator-runtime-semantics-evaluation sec-multiplicative-operators-runtime-semantics-evaluation sec-addition-operator-plus-runtime-semantics-evaluation sec-subtraction-operator-minus-runtime-semantics-evaluation sec-left-shift-operator-runtime-semantics-evaluation sec-signed-right-shift-operator-runtime-semantics-evaluation sec-unsigned-right-shift-operator-runtime-semantics-evaluation sec-binary-bitwise-operators-runtime-semantics-evaluation sec-applystringornumericbinaryoperator
function plain() {
  Math.max();
  (void 1) ** 2; (void 1) * 2; (void 1) / 2; (void 1) % 2; (void 1) + 2; (void 1) - 2;
  (void 1) << 2; (void 1) >> 2; (void 1) >>> 2; (void 1) & 2; (void 1) ^ 2; (void 1) | 2;
  1 + (void 2);
  Math.min();
}
function* gen() {
  Math.max();
  (yield 1) ** 2; (yield 1) * 2; (yield 1) / 2; (yield 1) % 2; (yield 1) + 2; (yield 1) - 2;
  (yield 1) << 2; (yield 1) >> 2; (yield 1) >>> 2; (yield 1) & 2; (yield 1) ^ 2; (yield 1) | 2;
  1 + (yield 2);
  Math.min();
}
