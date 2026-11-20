// CaseBlockEvaluation: the DefaultClause runs when no clause is selected, then
// falls through into the second CaseClauses.
// expect: normal: 11
switch (1) { case 0: 10; case 1: 11; case 2: 12; break; default: 13; }
switch (5) { case 0: 10; default: 13; case 1: 11; }
