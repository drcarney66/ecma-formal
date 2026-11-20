// expect: stop: sortError row-ischaracterclass-classcontrolletter#0 1
// args: --annex-b sec-regular-expressions-patterns --erratum IsCharacterClassControlLetter=literal
// A class range between two \c escapes of B.1.2 (Erratum IsCharacterClassControlLetter):
// IsCharacterClass has no row for ClassEscape :: `c` ClassControlLetter, and the run stops.
/[\c1-\c5]/.test("\x11");
