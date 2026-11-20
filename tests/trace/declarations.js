// Variable, `let` and `const` declarations (§14.3.1.2, §14.3.2.1) whose
// Initializers, or binding patterns, suspend.
// sections: sec-variable-statement-runtime-semantics-evaluation sec-let-and-const-declarations-runtime-semantics-evaluation sec-runtime-semantics-bindinginitialization sec-runtime-semantics-iteratorbindinginitialization sec-destructuring-binding-patterns-runtime-semantics-propertybindinginitialization sec-runtime-semantics-keyedbindinginitialization sec-destructuring-binding-patterns-runtime-semantics-restbindinginitialization sec-bindingevaluation
function plain() {
  Math.max();
  var a = void 1, b = 2;
  let c = void 3, d;
  const e = void 4;
  var [f = void 5] = [];
  let { g = void 6, ...h } = {};
  var { [void 7]: i } = {};
  Math.min();
}
function* gen() {
  Math.max();
  var a = yield 1, b = 2;
  let c = yield 3, d;
  const e = yield 4;
  var [f = yield 5] = [];
  let { g = yield 6, ...h } = {};
  var { [yield 7]: i } = {};
  Math.min();
}
