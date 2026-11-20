// The TryStatement's Catch and Finally suspending (§14.15.2, §14.15.3).
// sections: sec-try-statement-runtime-semantics-evaluation sec-block-runtime-semantics-evaluation sec-runtime-semantics-catchclauseevaluation
function plain() {
  Math.max();
  try { throw 1; } catch (e) { void 2; } finally { void 3; }
  try { 0; } finally { void 4; }
  Math.min();
}
function* gen() {
  Math.max();
  try { throw 1; } catch (e) { yield 2; } finally { yield 3; }
  try { 0; } finally { yield 4; }
  Math.min();
}
