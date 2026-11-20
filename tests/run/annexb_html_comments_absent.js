// Without §B.1.1 (a host that supports only §B.1.2) `<!--` is the
// punctuators `<`, `!` and `--`, so `<` at the start of a statement is a
// SyntaxError.
// args: --annex-b sec-regular-expressions-patterns
// expect: throw: SyntaxError
var a = 1; <!-- a = 2;
a
