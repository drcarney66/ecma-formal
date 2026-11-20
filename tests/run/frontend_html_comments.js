// §B.1.1: HTML-like comments are trivia between tokens (the parentheses of a
// target and an array's elision are seen through them), and a strict direct
// eval may start with an HTMLCloseComment.
// args: --web-browser
// expect: normal: undefined
// print: ""
// print: 2
// print: 1
// print: 2
var a;
(a <!-- c
) = function () {};
print(JSON.stringify(a.name));
print([a <!-- c
,,].length);
print((function () { "use strict"; return eval("--> c\n1"); })());
print((function () { return eval("--> c\n2"); })());
