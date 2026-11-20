// expect: stop: residue formal-parsetextin#0 2
// Erratum AnnexBGroupCount read literally: the group-number condition reads
// the Pattern whose parse it decides, and the parse stops.
// args: --annex-b sec-regular-expressions-patterns --literal AnnexBGroupCount
/(a)\1/.test("aa");
