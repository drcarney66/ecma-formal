// expect: normal: "false,false,false,false,null,null,false,false,false,false,false,false,false,false,true,true,2+1@0,2+1@0,2+1@0,null,1+1@2,null,false,1+1@0,-1,1,null,abc"
// RegExpBuiltinExec over one CharacterSetMatcher (§22.2.7.2): a search that finds no character of a class or of its
// complement answers null, under no flag, u and v, over astral characters and lone surrogates, with lastIndex any
// Number; then the searches that match, and the forms it does not cover: global, sticky, hasIndices, ignoreCase.
function ex(re, s, from) {
  if (from !== undefined) re.lastIndex = from;
  var r = re.exec(s);
  return r === null ? "null" : r.index + "+" + r[0].length + "@" + re.lastIndex;
}
[/\d/.test("abc"), /\d/.test(""), /\d/u.test("xyz"), /\d/v.test("xyz"), ex(/\d/, "abc", 7), ex(/\d/, "abc", NaN),
 /[^a-c]/.test("abcba"), /[^0-9]/.test("0123"), /[^\s]/.test(" \t\n"), /[a-z_0-9]/.test("+-*"),
 /[^a-z_0-9]/.test("abc_9"), /A/u.test("\u{1D49C}b"), /[\uD835]/u.test("\u{1D49C}a"),
 /[\uDC9C]/u.test("\uD835\uDC9C\uD835"), /[\uD835]/.test("\u{1D49C}"), /[\uDC9C]/u.test("a\uDC9Cb"),
 ex(/\d/, "ab1"), ex(/\d/u, "\u{1D49C}7"), ex(/[^a]/, "aab"), ex(/\d/g, "abc"), ex(/\d/g, "a1", 0), ex(/\d/y, "1a", 1),
 /\d/d.test("ab"), ex(/[a]/i, "xA"), "abc".search(/\d/), "a1".search(/\d/), String("abc".match(/\s/)),
 "abc".replace(/\d/, "x")].join()
