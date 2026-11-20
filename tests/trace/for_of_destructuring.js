// The `for`-`of` statement (§14.7.5) with destructuring heads: assignment
// patterns and `var` and `let` binding patterns, the body suspending.
// sections: sec-runtime-semantics-forinofloopevaluation sec-runtime-semantics-forinofheadevaluation sec-runtime-semantics-forin-div-ofbodyevaluation-lhs-stmt-iterator-lhskind-labelset sec-runtime-semantics-fordeclarationbindinginitialization sec-runtime-semantics-fordeclarationbindinginstantiation sec-runtime-semantics-loopevaluation sec-runtime-semantics-labelledevaluation
function plain() {
  Math.max();
  var x, y;
  for ([x] of [[1]]) void x;
  for ({ y } of [{ y: 2 }]) void y;
  for (var [a] of [[1]]) void a;
  for (let { b } of [{ b: 2 }]) void b;
  Math.min();
}
function* gen() {
  Math.max();
  var x, y;
  for ([x] of [[1]]) yield x;
  for ({ y } of [{ y: 2 }]) yield y;
  for (var [a] of [[1]]) yield a;
  for (let { b } of [{ b: 2 }]) yield b;
  Math.min();
}
