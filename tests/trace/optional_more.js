// Optional chains (§13.3.9): `?.()`, short circuits, chains of several
// links, the base or an argument suspending.
// sections: sec-optional-chaining-evaluation sec-optional-chaining-chain-evaluation sec-runtime-semantics-argumentlistevaluation sec-evaluatecall sec-property-accessors-runtime-semantics-evaluation sec-evaluate-property-access-with-expression-key
function plain() {
  var o = { f(x) { return { g: x }; }, p: { q: 1 } }, n = null;
  Math.max();
  o.f?.(void 1);
  o?.f?.(void 2).g;
  n?.p(void 3);
  n?.[void "p"].q;
  o?.p?.q;
  o?.p[void "q"];
  (void 0, o)?.p;
  o.f(void 4)?.g;
  Math.min();
}
function* gen() {
  var o = { f(x) { return { g: x }; }, p: { q: 1 } }, n = null;
  Math.max();
  o.f?.(yield 1);
  o?.f?.(yield 2).g;
  n?.p(yield 3);
  n?.[yield "p"].q;
  o?.p?.q;
  o?.p[yield "q"];
  (yield 0, o)?.p;
  o.f(yield 4)?.g;
  Math.min();
}
