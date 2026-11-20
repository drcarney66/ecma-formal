// expect: normal: "true,false,false,true,2+3@0,3+3@0,0+2@0,false,true,true,false,true,false,true,true,false,true,false,1+3(x)@0,2+2@0,2+2@4,3+1@4,1|22|333,true,1+4@0,true,true,0+1@0,2+1@0"
// RepeatMatcher over one CharacterSetMatcher (§22.2.2.3.1): greedy runs of a class and its complement,
// anchored by ^ and $ or not, with min and max, under no flag, u and v, astral characters, a capture before
// the run, sticky and global lastIndex; then the forms it does not cover: a continuation past the class,
// multiline, ignoreCase, lazy, lookbehind.
function ex(re, s, from) {
  if (from !== undefined) re.lastIndex = from;
  var r = re.exec(s);
  return r === null ? "null" : r.index + "+" + r[0].length + (r.length > 1 ? "(" + r[1] + ")" : "") + "@" + re.lastIndex;
}
[/^\d+$/.test("0123456789"), /^\d+$/.test("01a"), /^\d+$/.test(""), /^\d*$/.test(""),
 ex(/\d+/, "ab123cd"), ex(/\d{3,}/, "12a345"), ex(/\d{2}/, "12345"), /^\d{2,3}$/.test("1234"),
 /^[a-c]{2,3}$/.test("abc"), /^[^a]+$/.test("bcd"), /^[^a]+$/.test("bad"), /^\s+$/.test(" \t\n"),
 /^\d+$/u.test("12\u{1D49C}"), /^[a\u{1D49C}]+$/u.test("a\u{1D49C}a"), /^[^a]+$/.test("\u{1D49C}"),
 /^[\uD835]+$/u.test("\u{1D49C}"), /^[\d--[5]]+$/v.test("1234"), /^[\d--[5]]+$/v.test("125"),
 ex(/(x)\d+/, "yx12"), ex(/[^ ]+/, "  ab  "), ex(/\d+/y, "ab12x", 2), ex(/\d+/g, "ab12x", 3),
 "a1b22c333".match(/\d+/g).join("|"), /^\d+$/.test("1".repeat(40)),
 ex(/a\d*b/, "xa12b"), /^\d+$/m.test("12\n"), /^[a-z]+$/i.test("AbC"), ex(/\d+?/, "123"), ex(/(?<=\d+)a/, "12a")].join()
