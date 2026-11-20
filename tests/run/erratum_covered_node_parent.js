// Erratum CoveredNodeParent at its test262 reading: the covered
// |ParenthesizedExpression| takes its cover's place, so `return (f(n - 1))` is
// in tail position (test262 tco-pos.js).
// expect: normal: 0
"use strict";
function f(n) {
  if (n === 0) return 0;
  return (f(n - 1));
}
f(3);
