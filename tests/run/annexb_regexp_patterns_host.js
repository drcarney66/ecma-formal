// §B.1.2 on a host that is not a web browser but otherwise supports it: `{`, `\1`
// with no group, `a{,5}` and `]` are Patterns (ExtendedPatternCharacter,
// LegacyOctalEscapeSequence, ...), so the function parses.
// args: --annex-b sec-regular-expressions-patterns
// expect: normal: "function"
function f() { return [/{/, /\1/, /a{,5}/, /]/]; }
typeof f
