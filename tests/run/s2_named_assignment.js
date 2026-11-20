// S2 end to end: `x = function () {}` names the function "x" (NamedEvaluation).
// expect: normal: "x"
var x; x = function () {}; x.name
