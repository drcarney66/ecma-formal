// Blocks nested 16 deep: each `Block : { StatementList }` is a chain production, so an SDO
// without a row for it walks the whole nest as one chain.
// expect: normal: 1
{ { { { { { { { { { { { { { { { 1; } } } } } } } } } } } } } } } }
