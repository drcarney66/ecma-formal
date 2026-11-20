// S2 end to end: a closure keeps its environment across calls.
// expect: normal: 2
"use strict"; function mk() { var c = 0; return () => ++c; } var g = mk(); g(); g()
