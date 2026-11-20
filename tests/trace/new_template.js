// `new` with and without Arguments (§13.3.5), spread arguments (§13.3.8),
// template literals and tagged templates of several substitutions (§13.2.8,
// §13.3.11), a callee, an argument or a substitution suspending.
// sections: sec-new-operator-runtime-semantics-evaluation sec-evaluatenew sec-runtime-semantics-argumentlistevaluation sec-tagged-templates-runtime-semantics-evaluation sec-template-literals-runtime-semantics-evaluation sec-runtime-semantics-substitutionevaluation sec-function-calls-runtime-semantics-evaluation sec-evaluatecall
function plain() {
  Math.max();
  function F() {}
  var o = { t() {} };
  new (void 0, F);
  new (void 0, F)();
  new F(...[void 1], void 2, ...[3]);
  o.t`a${void 1}b${void 2}c`;
  (void 0, o.t)`a${3}b`;
  `${void 1}${void 2}`;
  `a${1}b${void 2}c${3}d`;
  Math.min();
}
function* gen() {
  Math.max();
  function F() {}
  var o = { t() {} };
  new (yield 0, F);
  new (yield 0, F)();
  new F(...[yield 1], yield 2, ...[3]);
  o.t`a${yield 1}b${yield 2}c`;
  (yield 0, o.t)`a${3}b`;
  `${yield 1}${yield 2}`;
  `a${1}b${yield 2}c${3}d`;
  Math.min();
}
