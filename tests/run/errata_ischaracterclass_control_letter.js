// expect: normal: true
// args: --annex-b sec-regular-expressions-patterns
// A class range between two \c escapes of B.1.2 (Erratum IsCharacterClassControlLetter):
// the test262 reading gives IsCharacterClass a row for ClassEscape :: `c` ClassControlLetter.
/[\c1-\c5]/.test("\x11");
