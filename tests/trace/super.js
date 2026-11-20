// The super keyword (§13.3.7): super properties in a method, a key
// suspending.
// sections: sec-super-keyword-runtime-semantics-evaluation sec-makesuperpropertyreference
function plain() {
  var o = { __proto__: { p: 1 }, m() { Math.max(); var r = [super[void "p"], super.p]; Math.min(); return r; } };
  o.m();
}
function* gen() {
  var o = { __proto__: { p: 1 }, *m() { Math.max(); var r = [super[yield "p"], super.p]; Math.min(); return r; } };
  yield* o.m();
}
