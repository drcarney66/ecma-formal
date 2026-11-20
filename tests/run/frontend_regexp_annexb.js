// §B.1.2: `\4xx`–`\7xx` is the LegacyOctalEscapeSequence of two digits then
// the third as a character; `c` ClassControlLetter in a class.
// args: --web-browser
// expect: normal: undefined
// print: [" 0"] false
// print: true true
// print: true false
// print: SyntaxError
function t(f) { try { print(f()); } catch (e) { print(e.name); } }
t(() => JSON.stringify(/\400/.exec(" 0")) + " " + /^\400$/.test(" "));
t(() => /^[\777]$/.test("7") + " " + /^\770$/.test("?0"));
t(() => /[\c1-\c5]/.test("\x13") + " " + /[\c1-\c5]/.test("A"));
t(() => new RegExp("[\\c5-\\c1]"));
