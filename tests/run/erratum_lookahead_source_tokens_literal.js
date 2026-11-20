// expect: stop: residue formal-parsetextin#0 2
// Erratum LookaheadSourceTokens read literally: a lookahead over the `;` §12.10
// inserts after `let` gives no parse decision, and the run stops.
// args: --literal LookaheadSourceTokens
if (0) let
[a] = 0;
