// The TryStatement `try` Block Catch Finally (§14.15.3), its Block suspending,
// with and without a throw.
// sections: sec-try-statement-runtime-semantics-evaluation sec-block-runtime-semantics-evaluation sec-runtime-semantics-catchclauseevaluation
function plain() {
  Math.max();
  try { void 1; throw 2; } catch (e) { 0; } finally { 0; }
  try { void 3; } catch (e) { 0; } finally { 0; }
  Math.min();
}
function* gen() {
  Math.max();
  try { yield 1; throw 2; } catch (e) { 0; } finally { 0; }
  try { yield 3; } catch (e) { 0; } finally { 0; }
  Math.min();
}
