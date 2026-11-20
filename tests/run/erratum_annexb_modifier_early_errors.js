// §22.2.1.1's modifier rules hold on B.1.2's ExtendedAtom: `(?ii:a)` repeats a
// modifier (Erratum AnnexBModifierEarlyErrors, test262's reading).
// args: --annex-b sec-regular-expressions-patterns
// expect: throw: SyntaxError
/(?ii:a)/;
