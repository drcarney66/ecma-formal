// Erratum AnnexBModifierEarlyErrors read literally: B.1.2.1 adds no modifier
// rule to ExtendedAtom, so `(?ii:a)` is a valid pattern without u or v.
// args: --annex-b sec-regular-expressions-patterns --literal AnnexBModifierEarlyErrors
// expect: normal: true
/(?ii:a)/.test("a");
