// Class definitions (§15.7.14, §15.7.16), a computed key and a heritage
// suspending.
// sections: sec-class-definitions-runtime-semantics-evaluation sec-runtime-semantics-classdefinitionevaluation sec-runtime-semantics-bindingclassdeclarationevaluation sec-static-semantics-classelementevaluation sec-runtime-semantics-classfielddefinitionevaluation
function plain() {
  Math.max();
  (class { [void "a"]() {} static [void "b"] = 1; });
  class C extends (void 0, Object) {}
  Math.min();
}
function* gen() {
  Math.max();
  (class { [yield "a"]() {} static [yield "b"] = 1; });
  class C extends (yield 0, Object) {}
  Math.min();
}
