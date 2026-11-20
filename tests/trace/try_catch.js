// The TryStatement `try` Block Catch (§14.15.3), its Block suspending, then
// throwing, and CatchClauseEvaluation (§14.15.2).
// sections: sec-try-statement-runtime-semantics-evaluation sec-block-runtime-semantics-evaluation sec-runtime-semantics-catchclauseevaluation
function plain() {
  Math.max();
  try { void 1; throw 2; } catch (e) { 0; }
  try { void 3; } catch { 0; }
  Math.min();
}
function* gen() {
  Math.max();
  try { yield 1; throw 2; } catch (e) { 0; }
  try { yield 3; } catch { 0; }
  Math.min();
}
