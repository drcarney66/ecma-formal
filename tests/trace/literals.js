// Array and object initializers (§13.2.4, §13.2.5), template literals and
// tagged templates (§13.2.8, §13.3.11), an element suspending.
// sections: sec-array-initializer-runtime-semantics-evaluation sec-runtime-semantics-arrayaccumulation sec-object-initializer-runtime-semantics-evaluation sec-runtime-semantics-propertydefinitionevaluation sec-template-literals-runtime-semantics-evaluation sec-runtime-semantics-substitutionevaluation sec-tagged-templates-runtime-semantics-evaluation
function plain() {
  Math.max();
  function tag() {}
  [1, void 2, , ...[3]];
  ({ a: void 1, [void "b"]: 2, ...(void 3), c() {} });
  `x${void 1}y${2}z`;
  tag`x${void 1}y`;
  Math.min();
}
function* gen() {
  Math.max();
  function tag() {}
  [1, yield 2, , ...[3]];
  ({ a: yield 1, [yield "b"]: 2, ...(yield 3), c() {} });
  `x${yield 1}y${2}z`;
  tag`x${yield 1}y`;
  Math.min();
}
