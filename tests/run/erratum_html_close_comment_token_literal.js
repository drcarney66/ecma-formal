--> the Script's first input element: an HTMLCloseComment
// Erratum HTMLCloseCommentToken read literally: a first-line HTMLCloseComment
// is a token no syntactic production has, and the parse stops.
// args: --annex-b sec-html-like-comments --literal HTMLCloseCommentToken
// expect: stop: residue formal-parsetextin#0 2
1
