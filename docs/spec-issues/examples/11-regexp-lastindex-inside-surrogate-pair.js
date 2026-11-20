// RegExpBuiltinExec with /u and lastIndex on the trailing surrogate of a pair.
// A non-empty match (steps 13.b, 22, 24, 28): the literal text reports index 1
// and a lone trailing surrogate as the match.
// An empty match: match = { [[StartIndex]]: 1, [[EndIndex]]: 0 }, which the
// Match Record table does not allow, and GetMatchString step 1's Assert fails.
if (typeof print === "undefined") globalThis.print = console.log;
var n = /./gu;
n.lastIndex = 1;
var mn = n.exec("\u{1F600}x");
print("non-empty: index " + mn.index + ", match length " + mn[0].length +
  ", first unit " + mn[0].charCodeAt(0).toString(16) + ", lastIndex " + n.lastIndex);
var r = /(?:)/gu;
r.lastIndex = 1;
var m = r.exec("\u{1F600}");
print("empty: index " + m.index + ", match length " + m[0].length + ", lastIndex " + r.lastIndex);
var rd = /(?:)/gud;
rd.lastIndex = 1;
var md = rd.exec("\u{1F600}");
print("indices[0] " + JSON.stringify(md.indices[0]));
