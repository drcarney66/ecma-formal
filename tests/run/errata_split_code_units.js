// expect: normal: "string"
// String.prototype.split with the empty String as separator (Erratum SplitCodeUnitStrings):
// the test262 reading makes each element a String of one code unit.
typeof "ab".split("")[1];
