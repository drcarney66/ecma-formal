// Without §B.1.2 (a host that supports only §B.1.1) /[\d-a]/ is a SyntaxError:
// a class escape cannot end a range (22.2.1.1).
// args: --annex-b sec-html-like-comments
// expect: throw: SyntaxError
/[\d-a]/;
