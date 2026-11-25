// expect: stop: assertFailed sec-getmatchstring#0 1
// RegExpBuiltinExec with /u and lastIndex on the trailing surrogate of a pair:
// step 13.b starts at the code point that contains it, the empty pattern
// matches there with [[EndIndex]] 0, and step 24's Match Record { 1, 0 } fails
// GetMatchString step 1's Assert. No test262 test sets lastIndex inside a
// pair before an empty match; the default reading is the text as written
// (Erratum GetMatchStringStartAfterEnd), so the run stops.
// V8 and SpiderMonkey report index 0; JavaScriptCore reports index 1.
// (The non-empty case, which does not stop, is
// regexp_lastindex_inside_pair_nonempty.js.)
var r = /(?:)/gu;
r.lastIndex = 1;
r.exec("\u{1F600}");
