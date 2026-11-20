// A Block that suspends (§14.2.2): steps 1–8, once each.
// sections: sec-block-runtime-semantics-evaluation sec-blockdeclarationinstantiation
function plain() {
  Math.max();
  { let x = 1; void x; }
  Math.min();
}
function* gen() {
  Math.max();
  { let x = 1; yield x; }
  Math.min();
}
