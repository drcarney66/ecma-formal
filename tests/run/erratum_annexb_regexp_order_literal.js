// expect: stop: residue formal-parsetextin#0 2
// Erratum AnnexBRegExpOrder read literally: B.1.2's grammar gives a pattern
// more than one parse, and the parse stops.
// args: --annex-b sec-regular-expressions-patterns --literal AnnexBRegExpOrder
/]/.test("]");
