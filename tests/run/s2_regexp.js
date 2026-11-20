// RegExp (§22.2): literals and the constructor (patterns parsed by jsparse), exec with
// captures and named groups, the Symbol methods through String methods, lookbehind,
// Unicode mode, the s and i flags and modifiers, source and toString.
// expect: normal: "true | 29/02/2016 | 3 | 2020-12 | 2020 | 12 | a|b||c | aXc | 1,22,333 | true | false | 42 | true | true | -a-a-a- | true | true | false | /a\\/b/ | \\/ | \\n | 2 | 1,2 | true | true | true | true | false | true | true"
var r = [];
r.push(/a+b/.test("xaab"));
r.push("2016-02-29".replace(/(\d+)-(\d+)-(\d+)/, "$3/$2/$1"));
var m = /(?<year>\d{4})-(?<m>\d\d)/.exec("on 2020-12 ok");
r.push(m.index, m[0], m.groups.year, m.groups.m);
r.push("a,b;;c".split(/[,;]/).join("|"));
r.push("aBc".replace(/b/i, "X"));
r.push("x1y22z333".match(/\d+/g).join());
r.push(new RegExp("^\\w+$").test("abc_1"), /^\w+$/.test("ab-c"));
r.push(/(?<=\$)\d+/.exec("cost $42")[0]);
r.push(/(a)|(b)/.exec("b")[1] === undefined);
r.push(/(a*)*b/.test("aaab"));
r.push("aaa".replace(/a*?/g, "-"));
r.push(/\u{1F600}/u.test("😀"), /^.$/u.test("😀"), /^.$/.test("😀"));
r.push(String(/a\/b/), new RegExp("/").source, RegExp("\n").source);
r.push("abc".search(/c/), [..."a1b2".matchAll(/\d/g)].map(x => x[0]).join());
r.push(/[^]/.test("\n"), /./s.test("\n"), /(?i:a)b/.test("Ab"));
r.push(/\bfoo\b/.test("a foo b"), /ſ/i.test("s"), /ſ/iu.test("s"), /K/iu.test("K"));
r.join(" | ")
