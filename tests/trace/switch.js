// The SwitchStatement (§14.12.4) and CaseBlockEvaluation (§14.12.2): the
// discriminant, a selector and a clause's statements suspending.
// sections: sec-switch-statement-runtime-semantics-evaluation sec-runtime-semantics-caseblockevaluation sec-runtime-semantics-caseclauseisselected sec-block-runtime-semantics-evaluation
function plain() {
  Math.max();
  switch (void 1) { case 1: 0; default: 1; }
  switch (2) { case (void 1): 0; case 2: void 3; break; default: 4; }
  switch (5) { case 1: 0; default: void 6; case 7: 8; }
  Math.min();
}
function* gen() {
  Math.max();
  switch (yield 1) { case 1: 0; default: 1; }
  switch (2) { case (yield 1): 0; case 2: yield 3; break; default: 4; }
  switch (5) { case 1: 0; default: yield 6; case 7: 8; }
  Math.min();
}
