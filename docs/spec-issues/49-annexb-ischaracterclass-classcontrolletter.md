# 49. Annex B: `/[\c1-\c5]/` asks for the IsCharacterClass of `ClassEscape :: c ClassControlLetter`, which has none

- **Location:** §B.1.2 Regular Expressions Patterns (`#sec-regular-expressions-patterns`), ClassEscape's
  `[~UnicodeMode] c ClassControlLetter`; §B.1.2.1 Static Semantics: Early Errors
  (`#sec-patterns-static-semantics-early-errors-annexb`), the range rules; §B.1.2.3 Static Semantics:
  IsCharacterClass (`#sec-patterns-static-semantics-is-character-class-annexb`); §B.1.2.4 Static Semantics:
  CharacterValue (`#sec-patterns-static-semantics-character-value-annexb`); §22.2.1.6 Static Semantics:
  IsCharacterClass (`#sec-patterns-static-semantics-is-character-class`).
- **Kind:** missing case (an operation applied to a production it does not define).
- **Model erratum:** `IsCharacterClassControlLetter`, default reading test262; its readings: literal, test262,
  proposed. The test262 and proposed readings add the row of the proposed wording to §B.1.2.3's clause; the literal
  reading (no row) stops at a range with such an end.
- **Upstream:** Checked 2026-11-19: none found (searched for "IsCharacterClass" and "ClassControlLetter"). Related: PR
  #2445 (open, 2021-06) rewrites the grammar line of §B.1.2.3 and adds no rule for `ClassEscape :: c
  ClassControlLetter`.

## Text

§B.1.2 adds an alternative to ClassEscape:

> ClassEscape[UnicodeMode, NamedCaptureGroups] ::
>   `b`
>   [+UnicodeMode] `-`
>   [~UnicodeMode] `c` ClassControlLetter
>   CharacterClassEscape[?UnicodeMode]
>   CharacterEscape[?UnicodeMode, ?NamedCaptureGroups]
>
> ClassControlLetter ::
>   DecimalDigit
>   `_`

§B.1.2.1, for `NonemptyClassRanges :: ClassAtom - ClassAtom ClassContents` (and likewise
`NonemptyClassRangesNoDash`):

> - It is a Syntax Error if IsCharacterClass of the first |ClassAtom| is *true* or IsCharacterClass of the second
>   |ClassAtom| is *true* and this production has a [UnicodeMode] parameter.
> - It is a Syntax Error if IsCharacterClass of the first |ClassAtom| is *false*, IsCharacterClass of the second
>   |ClassAtom| is *false*, and the CharacterValue of the first |ClassAtom| is strictly greater than the
>   CharacterValue of the second |ClassAtom|.

§B.1.2.3 extends IsCharacterClass only with `ClassAtomNoDash :: \ [lookahead == c]`. §B.1.2.4 extends CharacterValue
with that production and with `ClassEscape :: c ClassControlLetter` ("the remainder of dividing _i_ by 32").
§22.2.1.6 defines IsCharacterClass for `ClassAtom :: -`, `ClassAtomNoDash :: SourceCharacter but not one of \ or ]
or -`, and `ClassEscape :: b`, `-`, CharacterEscape and CharacterClassEscape.

## Problem

`/[\c1-\c5]/` parses with each end a `ClassAtom :: ClassAtomNoDash :: \ ClassEscape` whose ClassEscape is
`c ClassControlLetter`. The range rules ask for IsCharacterClass of each ClassAtom, which reaches that production
through chain productions, and no clause defines it there: it is a chain production, and its implicit rule reaches
ClassControlLetter's alternatives `_` and DecimalDigit's digits, which have no rule. Both rules have no value, and
the second also needs CharacterValue, which §B.1.2.4 does define for it. §B.1.2.4's row and the other
single-character escapes say what is meant: the escape is one character, and IsCharacterClass is *false*.

## Examples

```js
print(/[\c1-\c5]/.test("\x13") + " " + /[\c1-\c5]/.test("A"));
try { new RegExp("[\\c5-\\c1]"); print("no error"); } catch (e) { print(e.name); }
```

With the row of the proposed wording the first line prints `true false` (`\c1` is U+0011 and `\c5` U+0015) and the
second `SyntaxError` (out of order). The formal model, run with `--web-browser` (Annex B on):

| | first line | second line |
|---|---|---|
| literal reading | `stop: sortError row-ischaracterclass-classcontrolletter#0` (at the range rules, at IsCharacterClass) | (not reached) |
| test262 and proposed readings (the default: test262) | `true false` | `SyntaxError` |

The model's test `tests/run/frontend_regexp_annexb.js` (`--web-browser`) checks the same two lines under the default
reading and prints `true false` and `SyntaxError` for them. test262's `annexB/language/literals/regexp/class-escape.js`
requires `[\c1]` to match U+0011.

## Proposed wording

Proposed: add the production to §B.1.2.3's row.

```diff
--- a/spec.html
+++ b/spec.html
@@ -53998,8 +53998,10 @@
         <h1>Static Semantics: IsCharacterClass</h1>
         <p>The semantics of IsCharacterClass is extended as follows:</p>
         <emu-grammar>
           ClassAtomNoDash :: `\` [lookahead == `c`]
+
+          ClassEscape :: `c` ClassControlLetter
         </emu-grammar>
         <emu-alg>
           1. Return *false*.
         </emu-alg>
```

## test262

None has `\c` with a digit or `_` at an end of a range: `annexB/language/literals/regexp/class-escape.js` tests
`[\c0]`, `[\c1]`, `[\c8]`, `[\c9]`, `[\c_]` and `[\c00]+`, `[\c10]+`, `[\c80]+`, `[\c90]+`, which ask for no
IsCharacterClass, and `annexB/built-ins/RegExp/RegExp-invalid-control-escape-character-class-range.js` tests
`/[\\c-f]/`.
