// Optional chains (§13.3.9), an argument or a key suspending.
// sections: sec-optional-chaining-evaluation sec-optional-chaining-chain-evaluation sec-runtime-semantics-argumentlistevaluation sec-evaluatecall
function plain() {
  Math.max();
  var o = { f(x) { return x; }, p: 1 };
  o?.f(void 1);
  o?.[void "p"];
  o?.p.toString(void 2);
  Math.min();
}
function* gen() {
  Math.max();
  var o = { f(x) { return x; }, p: 1 };
  o?.f(yield 1);
  o?.[yield "p"];
  o?.p.toString(yield 2);
  Math.min();
}
