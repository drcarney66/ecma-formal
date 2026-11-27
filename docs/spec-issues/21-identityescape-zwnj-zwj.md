# 21. `/\<ZWNJ>/` and `/\<ZWJ>/` became SyntaxErrors with Unicode 15.1

- **Location:** §22.2.1 Patterns (`#sec-patterns`), the production IdentityEscape, with §12.7 Names and Keywords
  (`#sec-names-and-keywords`, UnicodeIDContinue), reached from §22.2.3.4 ParsePattern (`#sec-parsepattern`), step 4.a.
- **Kind:** contradiction (an unrecorded normative change: a change of the Unicode Standard turned valid patterns into
  SyntaxErrors).
- **Model erratum:** `IdentityEscapeJoinControls`, baked-in SpecTec reading proposed (`kind="proposal"`, layer `parser`,
  `spec/spectec/04-grammar-regexp.spectec`); its readings: literal, proposed.
- **Upstream:** Checked 2026-11-19: none found (searched for "IdentityEscape"). Issue #3073 (closed, 2024-02),
  "[Informative] Observable changes because of Unicode 15.1", and PR #3074 (merged 2024-02, commit 467819a42),
  "Editorial: Remove special-casing of U+200C and U+200D", concern the same two code points; the PR removed
  &lt;ZWNJ&gt; and &lt;ZWJ&gt; from IdentifierPartChar.

## Text

§22.2.1:

> IdentityEscape[UnicodeMode] ::
>   [+UnicodeMode] SyntaxCharacter
>   [+UnicodeMode] `/`
>   [~UnicodeMode] SourceCharacter but not UnicodeIDContinue

§12.7:

> IdentifierPartChar ::
>   UnicodeIDContinue
>   `$`
>
> UnicodeIDContinue ::
>   &gt; any Unicode code point with the Unicode property “ID_Continue”

The Unicode Character Database since 15.1.0 (PropList.txt and DerivedCoreProperties.txt):

<!-- quote: Unicode Character Database 17.0.0, PropList.txt and DerivedCoreProperties.txt -->
> 200C..200D    ; Other_ID_Continue # Cf   [2] ZERO WIDTH NON-JOINER..ZERO WIDTH JOINER
>
> 200C..200D    ; ID_Continue # Cf   [2] ZERO WIDTH NON-JOINER..ZERO WIDTH JOINER

## Problem

U+200C ZERO WIDTH NON-JOINER and U+200D ZERO WIDTH JOINER are now UnicodeIDContinue, so neither is an IdentityEscape
without [UnicodeMode], and no other alternative of CharacterEscape derives them. A pattern of `\` and one of them is
not a Pattern[~UnicodeMode, ~UnicodeSetsMode, +NamedCaptureGroups]: ParsePattern step 4.a returns a List of errors,
`new RegExp("\\‍")` throws a *SyntaxError* (RegExpInitialize step 15), and so does a RegularExpressionLiteral of a
backslash and a ZWJ (the early error of §13.2.7.1). A ClassEscape of them fails the same way.

These escapes were valid until Unicode 15.1 (September 2023). IdentityEscape has read "SourceCharacter but not
UnicodeIDContinue" since ECMAScript 2015, when ID_Continue did not contain the two code points and IdentifierPart
listed them beside UnicodeIDContinue: the exclusion covered the identifier characters that are UnicodeIDContinue, and
the identity escapes of ZWNJ, ZWJ and `$` stayed valid. Unicode 15.1 added both to ID_Continue. The pinned
IdentifierPartChar no longer lists &lt;ZWNJ&gt; and &lt;ZWJ&gt; beside UnicodeIDContinue: for IdentifierName they
would be redundant, and dropping them is editorial. For IdentityEscape, which also reads ID_Continue, the same Unicode
change is normative, and neither the text nor Annex F (Additions and Changes That Introduce Incompatibilities with
Prior Editions) records it.

Only the main grammar without [UnicodeMode] is affected: a pattern without the `u` or `v` flag on a host that does not
implement §B.1.2. With [+UnicodeMode], IdentityEscape is SyntaxCharacter or `/`, which never included the code points.
§B.1.2 (which web browsers implement) has its own IdentityEscape[~UnicodeMode], SourceCharacterIdentityEscape:
SourceCharacter but not `c` (or not `c` or `k`), which does not read ID_Continue. Group names (RegExpIdentifierName)
read IdentifierPartChar and accept the two code points either way.

## Examples

[examples/21-identityescape-zwnj-zwj.js](examples/21-identityescape-zwnj-zwj.js) (outputs:
[RESULTS.md](examples/RESULTS.md#21-identityescape-zwnj-zwjjs)) evaluates `/\X/` (through eval), `new RegExp("\\" +
X)` and the same with the `u` flag, for X = U+200C, U+200D, their neighbours U+200B and U+200E (not ID_Continue) and
`a` (ID_Continue):

| | `\` U+200C, `\` U+200D | `\` U+200B, `\` U+200E | `\a` | with `u` |
|---|---|---|---|---|
| literal text, main grammar | `SyntaxError` | valid | `SyntaxError` | `SyntaxError` |
| literal text, §B.1.2 | valid | valid | valid | `SyntaxError` |
| V8, SpiderMonkey | valid | valid | valid | `SyntaxError` |
| JavaScriptCore | valid | valid | valid | valid, but `SyntaxError` for `a` |
| formal model (proposed reading, main grammar) | valid | valid | `SyntaxError` | `SyntaxError` |
| formal model (literal reading, main grammar) | `SyntaxError` | valid | `SyntaxError` | `SyntaxError` |

The engines implement §B.1.2, under which the escapes are valid anyway: their output shows that none rejects them, not
which reading of the main grammar they take. The model's default host runs without §B.1.2 (`--web-browser` enables §B.1.2). JavaScriptCore's acceptance
of non-ASCII identity escapes with the `u` flag is a separate deviation: test262's
`built-ins/RegExp/unicode_restricted_identity_escape*.js` check ASCII characters only.

## Proposed wording

Proposed: the two code points become IdentityEscapes again, with their abbreviations &lt;ZWNJ&gt; and &lt;ZWJ&gt;
(which the pinned text no longer defines) defined in §12.1:

```diff
--- a/spec.html
+++ b/spec.html
@@ -16601,6 +16601,7 @@
     <h1>Unicode Format-Control Characters</h1>
     <p>The Unicode format-control characters (i.e., the characters in category “Cf” in the Unicode Character Database such as LEFT-TO-RIGHT MARK or RIGHT-TO-LEFT MARK) are control codes used to control the formatting of a range of text in the absence of higher-level protocols for this (such as mark-up languages).</p>
     <p>It is useful to allow format-control characters in source text to facilitate editing and display. All format control characters may be used within comments, and within string literals, template literals, and regular expression literals.</p>
+    <p>U+200C (ZERO WIDTH NON-JOINER) and U+200D (ZERO WIDTH JOINER), abbreviated &lt;ZWNJ> and &lt;ZWJ>, are format-control characters that are used to make necessary distinctions when forming words or phrases in certain languages.</p>
     <p>U+FEFF (ZERO WIDTH NO-BREAK SPACE) is a format-control character used primarily at the start of a text to mark it as Unicode and to allow detection of the text's encoding and byte order. &lt;ZWNBSP> characters intended for this purpose can sometimes also appear after the start of a text, for example as a result of concatenating files. In ECMAScript source text &lt;ZWNBSP> code points are treated as white space characters (see <emu-xref href="#sec-white-space"></emu-xref>) outside of comments, string literals, template literals, and regular expression literals.</p>
   </emu-clause>
 
@@ -37016,6 +37017,8 @@
           [+UnicodeMode] SyntaxCharacter
           [+UnicodeMode] `/`
           [~UnicodeMode] SourceCharacter but not UnicodeIDContinue
+          [~UnicodeMode] &lt;ZWNJ&gt;
+          [~UnicodeMode] &lt;ZWJ&gt;
 
         DecimalEscape ::
           NonZeroDigit DecimalDigits[~Sep]? [lookahead &notin; DecimalDigit]
```

A production `SourceCharacter but not IdentifierPartChar` would not do: it also excludes `$`, whose identity escape
`\$` is valid and which the tests below require. If the committee prefers the escapes to stay invalid, the change is
normative and needs an entry in Annex F.

## test262

`language/literals/regexp/S7.8.5_A1.4_T2.js` and `S7.8.5_A2.4_T2.js` (outside `annexB/`) evaluate `/\X/` and `/a\X/`
for every code unit X but the line terminators. They accept a *SyntaxError* only when X can continue an identifier
(`eval("var _" + X)` succeeds) and X is not `$` (the one code unit they name, "`$` is not ID_Continue"). U+200C and
U+200D continue identifiers, so the tests accept a *SyntaxError* for them: they pass under the literal text, and do not
decide between the two readings. No test requires the escapes of U+200C and U+200D to be valid, or to be
*SyntaxError*s.
