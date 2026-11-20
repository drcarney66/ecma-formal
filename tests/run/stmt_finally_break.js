// An abrupt Finally replaces the Block's completion: the labelled statement is
// UpdateEmpty(break, undefined).
// expect: normal: undefined
a: try { 3 } finally { break a; }
