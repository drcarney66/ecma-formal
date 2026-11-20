// The ThrowStatement (§14.14.1), its Expression suspending.
// sections: sec-throw-statement-runtime-semantics-evaluation sec-try-statement-runtime-semantics-evaluation sec-runtime-semantics-catchclauseevaluation
function plain() {
  Math.max();
  try { throw void 1; } catch { 0; }
  Math.min();
}
function* gen() {
  Math.max();
  try { throw yield 1; } catch { 0; }
  Math.min();
}
