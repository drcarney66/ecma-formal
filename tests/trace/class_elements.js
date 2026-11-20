// Class elements (§15.7): methods, accessors, generator and async methods,
// public and private fields, private methods and accessors, static blocks,
// a computed key suspending.
// sections: sec-runtime-semantics-classdefinitionevaluation sec-static-semantics-classelementevaluation sec-runtime-semantics-classfielddefinitionevaluation sec-runtime-semantics-classstaticblockdefinitionevaluation sec-runtime-semantics-methoddefinitionevaluation sec-runtime-semantics-definemethod sec-class-definitions-runtime-semantics-evaluation sec-runtime-semantics-bindingclassdeclarationevaluation sec-privatemethodoraccessoradd sec-privatefieldadd sec-definefield sec-initializeinstanceelements sec-object-initializer-runtime-semantics-evaluation
function plain() {
  Math.max();
  class A {
    [void "a"]() {}
    get b() { return 1; }
    set b(v) {}
    static *c() {}
    async d() {}
    e = 1;
    static f;
    #g = 2;
    #h() {}
    get #i() { return 1; }
    set #i(v) {}
    static #j() {}
    static { this.k = 1; }
    ["l"] = 3;
    static async *m() {}
  }
  new A();
  Math.min();
}
function* gen() {
  Math.max();
  class A {
    [yield "a"]() {}
    get b() { return 1; }
    set b(v) {}
    static *c() {}
    async d() {}
    e = 1;
    static f;
    #g = 2;
    #h() {}
    get #i() { return 1; }
    set #i(v) {}
    static #j() {}
    static { this.k = 1; }
    ["l"] = 3;
    static async *m() {}
  }
  new A();
  Math.min();
}
