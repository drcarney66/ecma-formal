// An inner label does not catch `break a`; the StatementList's UpdateEmpty
// gives the break the value 2, and the labelled statement makes it normal.
// expect: normal: 2
9; a: { 1; b: { 2; break a; } 3; }
