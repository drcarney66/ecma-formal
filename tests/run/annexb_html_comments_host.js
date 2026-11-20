// §B.1.1 on a host that is not a web browser but otherwise supports it: `<!--`
// starts a SingleLineHTMLOpenComment, and `-->` at the start of a line a
// SingleLineHTMLCloseComment.
// args: --annex-b sec-html-like-comments
// expect: normal: 1
var a = 1; <!-- a = 2;
--> a = 3;
a
