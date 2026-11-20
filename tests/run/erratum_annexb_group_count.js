// `\1` with one capturing group is a backreference: the group count is read
// from a committed parse (Erratum AnnexBGroupCount, test262's reading).
// args: --annex-b sec-regular-expressions-patterns
// expect: normal: true
/(a)\1/.test("aa");
