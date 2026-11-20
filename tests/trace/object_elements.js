// Object initializers (§13.2.5): every kind of PropertyDefinition, a value
// or a key suspending.
// sections: sec-object-initializer-runtime-semantics-evaluation sec-runtime-semantics-propertydefinitionevaluation sec-runtime-semantics-methoddefinitionevaluation sec-runtime-semantics-definemethod sec-runtime-semantics-namedevaluation sec-identifiers-runtime-semantics-evaluation
function plain() {
  var a = 1;
  Math.max();
  ({ a, b: void 1, get c() { return 1; }, set c(v) {}, d() {}, *e() {}, async f() {}, async *g() {},
     h: function () {}, i: () => 1, "j": 2, 3: 4, ["k"]: void 5, ...{ l: 6 }, __proto__: null });
  ({ __proto__: (void 0, {}), m: 1 });
  Math.min();
}
function* gen() {
  var a = 1;
  Math.max();
  ({ a, b: yield 1, get c() { return 1; }, set c(v) {}, d() {}, *e() {}, async f() {}, async *g() {},
     h: function () {}, i: () => 1, "j": 2, 3: 4, ["k"]: yield 5, ...{ l: 6 }, __proto__: null });
  ({ __proto__: (yield 0, {}), m: 1 });
  Math.min();
}
