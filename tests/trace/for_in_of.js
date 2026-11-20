// The `for`-`in` and `for`-`of` statements (§14.7.5): the body, and the
// Expression, suspending; `var`, `let` and assignment heads.
// sections: sec-runtime-semantics-forinofloopevaluation sec-runtime-semantics-forinofheadevaluation sec-runtime-semantics-forin-div-ofbodyevaluation-lhs-stmt-iterator-lhskind-labelset sec-runtime-semantics-fordeclarationbindinginstantiation sec-runtime-semantics-loopevaluation sec-runtime-semantics-labelledevaluation
function plain() {
  Math.max();
  var k, v;
  for (var a in { p: 1 }) void a;
  for (let b in { p: 1 }) void b;
  for (k in { p: 1 }) void k;
  for (var c of [1]) void c;
  for (const d of [1]) void d;
  for (v of [1]) void v;
  for (var e of (void 0, [1])) 0;
  for (let f in (void 0, { p: 1 })) 0;
  Math.min();
}
function* gen() {
  Math.max();
  var k, v;
  for (var a in { p: 1 }) yield a;
  for (let b in { p: 1 }) yield b;
  for (k in { p: 1 }) yield k;
  for (var c of [1]) yield c;
  for (const d of [1]) yield d;
  for (v of [1]) yield v;
  for (var e of (yield 0, [1])) 0;
  for (let f in (yield 0, { p: 1 })) 0;
  Math.min();
}
