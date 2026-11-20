// The IfStatement (§14.6.2): its Expression, then each branch, suspending.
// sections: sec-if-statement-runtime-semantics-evaluation
function plain() {
  Math.max();
  if (void 1) 0; else 1;
  if (void 1) 0;
  if (1) void 2; else 3;
  if (0) 2; else void 3;
  if (1) void 2;
  Math.min();
}
function* gen() {
  Math.max();
  if (yield 1) 0; else 1;
  if (yield 1) 0;
  if (1) yield 2; else 3;
  if (0) 2; else yield 3;
  if (1) yield 2;
  Math.min();
}
