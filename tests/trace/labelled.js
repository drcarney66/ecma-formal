// The LabelledStatement (§14.13.3, §14.13.4): a labelled block and a
// labelled loop that suspend, with `break` and `continue`.
// sections: sec-labelled-statements-runtime-semantics-evaluation sec-runtime-semantics-labelledevaluation sec-runtime-semantics-loopevaluation sec-runtime-semantics-whileloopevaluation sec-block-runtime-semantics-evaluation
function plain() {
  Math.max();
  l1: { void 1; break l1; }
  var i = 0;
  l2: while (i < 2) { i++; void i; continue l2; }
  Math.min();
}
function* gen() {
  Math.max();
  l1: { yield 1; break l1; }
  var i = 0;
  l2: while (i < 2) { i++; yield i; continue l2; }
  Math.min();
}
