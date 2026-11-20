// The ReturnStatement (§14.10.1), its Expression suspending; the Finally
// calls the second marker.
// sections: sec-return-statement-runtime-semantics-evaluation sec-try-statement-runtime-semantics-evaluation
function plain() {
  Math.max();
  try { return void 1; } finally { Math.min(); }
}
function* gen() {
  Math.max();
  try { return yield 1; } finally { Math.min(); }
}
