// `#x in` (§13.10.1), the right operand suspending, and private member
// accesses (§13.3.2) whose object suspends.
// sections: sec-relational-operators-runtime-semantics-evaluation sec-property-accessors-runtime-semantics-evaluation sec-makeprivatereference sec-privateelementfind sec-privateget sec-privateset
function plain() {
  class A {
    #g = 1;
    static t(o) {
      Math.max();
      #g in (void 0, o);
      #g in (void 0, {});
      (void 0, o).#g;
      (void 0, o).#g = 2;
      Math.min();
    }
  }
  A.t(new A());
}
function* gen() {
  class A {
    #g = 1;
    static *t(o) {
      Math.max();
      #g in (yield 0, o);
      #g in (yield 0, {});
      (yield 0, o).#g;
      (yield 0, o).#g = 2;
      Math.min();
    }
  }
  yield* A.t(new A());
}
