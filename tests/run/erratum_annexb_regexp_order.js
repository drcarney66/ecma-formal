// B.1.2's alternatives commit in order: `\b*` is an Assertion, which no
// quantifier follows, and the literal has no parse (Erratum AnnexBRegExpOrder,
// test262's reading).
// args: --annex-b sec-regular-expressions-patterns
// expect: throw: SyntaxError
/\b*/;
