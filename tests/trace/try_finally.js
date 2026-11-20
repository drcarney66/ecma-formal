// The TryStatement `try` Block Finally (§14.15.3), its Block suspending.
// sections: sec-try-statement-runtime-semantics-evaluation sec-block-runtime-semantics-evaluation
function plain() {
  Math.max();
  try { void 1; } finally { 0; }
  Math.min();
}
function* gen() {
  Math.max();
  try { yield 1; } finally { 0; }
  Math.min();
}
