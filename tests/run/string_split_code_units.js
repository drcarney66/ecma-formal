// expect: normal: " |string|a,b|2|true"
// String.prototype.split with an empty separator yields Strings of one code unit
// (Erratum SplitCodeUnitStrings, docs/spec-issues/37).
var a = new String(" ").split("");
var b = "ab".split("");
a[0] + "|" + typeof b[1] + "|" + b.join(",") + "|" + "abc".split("", 2).length + "|" + ("😀".split("")[1] === "\uDE00")
