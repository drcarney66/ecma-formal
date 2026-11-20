// Without §B.1.2 (a host that supports only §B.1.1) a Pattern is the main
// grammar's, where `{` is no PatternCharacter: an early error.
// args: --annex-b sec-html-like-comments
// expect: throw: SyntaxError
function f() { return /{/; }
typeof f
