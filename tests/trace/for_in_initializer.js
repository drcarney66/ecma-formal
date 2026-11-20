// The `for`-`in` statement with an Initializer (§B.3.5), suspending in its
// body: an abrupt completion of the head's steps (here GetValue's
// ReferenceError, step 4.b) is the LoopEvaluation's, which LabelledEvaluation
// (§14.13.4) receives as stmtResult (steps 2-3), on the frame machine as on
// the direct evaluator.
// sections: sec-initializers-in-forin-statement-heads sec-runtime-semantics-labelledevaluation sec-try-statement-runtime-semantics-evaluation
// args: --web-browser
// expect: sec-runtime-semantics-labelledevaluation 3. Return ? stmtResult.
function plain() {
  Math.max();
  try { for (var x = missing in {}) void x; } catch (e) { 0; }
  Math.min();
}
function* gen() {
  Math.max();
  try { for (var x = missing in {}) yield x; } catch (e) { 0; }
  Math.min();
}
