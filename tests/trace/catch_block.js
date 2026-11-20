// CatchClauseEvaluation (§14.15.2) of `Catch : catch Block`, whose one step
// both evaluators trace, the Block suspending.
// sections: sec-runtime-semantics-catchclauseevaluation sec-block-runtime-semantics-evaluation
// expect: sec-runtime-semantics-catchclauseevaluation 1. Return ? Evaluation of Block.
function plain() {
  Math.max();
  try { throw 1; } catch { void 2; }
  try { throw void 3; } catch { 0; }
  Math.min();
}
function* gen() {
  Math.max();
  try { throw 1; } catch { yield 2; }
  try { throw yield 3; } catch { 0; }
  Math.min();
}
