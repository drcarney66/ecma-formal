// §B.1.2.5-7 on a web-browser host: the Annex B Term and ExtendedAtom rows compile. A quantified
// lookahead repeats the lookahead (CompileAssertion of |QuantifiableAssertion|): + and {2} match
// it at the same place, an empty iteration past the minimum fails; \1 with no group is U+0001,
// \c is "\" then "c", and ], { are pattern characters. Groups count Atom's and ExtendedAtom's
// (B.1.2.2): an unmatched capture is u.
// Strict, so GlobalDeclarationInstantiation's B.3.2.2 step does not apply.
// args: --web-browser
// expect: normal: "true,1,true,true,false,true,true,true,true,true,true,false,ab/u,b/u/b"
"use strict";
const show = m => m.map(x => x === undefined ? "u" : x).join("/");
[/a/.test("a"), /a/.exec("ba").index,
  /(?=a)*/.exec("b")[0] === "", /(?=a)+a/.test("a"), /(?=a)+b/.test("b"), /(?=a){2}a/.test("a"),
  /(?!a)+b/.test("b"), /\1/.test("\u0001"), /\c/.test("\\c"), /]/.test("]"), /a{,5}/.test("a{,5}"),
  /a{,5}/.test("aa"), show(/(?:(a)|b)+/.exec("ab")), show(/(a)|(b)/.exec("b"))].join()
