// The inserted `;` after `let` is no source token: ExpressionStatement's lookahead
// reads `let [` and the program has no parse (Erratum LookaheadSourceTokens,
// test262's reading).
// expect: throw: SyntaxError
if (0) let
[a] = 0;
