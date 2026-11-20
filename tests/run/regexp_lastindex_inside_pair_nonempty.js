// expect: normal: undefined
// print: 1 1 de00 2
// RegExpBuiltinExec with /u and lastIndex on the trailing surrogate of a pair,
// before a non-empty match: step 13.b starts at the code point that contains
// lastIndex, step 22 reports index lastIndex (1), and step 28's matched
// substring is from 1 to the match's end (2), a lone trailing surrogate. The
// literal result (docs/spec-issues/11; V8 and SpiderMonkey report index 0
// and the whole pair; JavaScriptCore reports the next code point, index 2).
// The empty match is regexp_lastindex_inside_pair.js (the stop of
// Erratum GetMatchStringStartAfterEnd).
var n = /./gu;
n.lastIndex = 1;
var m = n.exec("\u{1F600}x");
print(m.index + " " + m[0].length + " " + m[0].charCodeAt(0).toString(16) + " " + n.lastIndex);
