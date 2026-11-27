# 56. Post-ASI `/` lexical goal selection and non-Script `ParseText` starting goals

- **Location:** §12 ECMAScript Language: Lexical Grammar (`#sec-ecmascript-language-lexical-grammar`); §12.10.1 Rules of
  Automatic Semicolon Insertion (`#sec-rules-of-automatic-semicolon-insertion`), rule 1; §5.1.5 The Syntactic Grammar
  (`#sec-syntactic-grammar`); §11.1.6 ParseText (`#sec-parsetext`).
- **Kind:** contradiction (literal scanning before ASI rejects valid post-ASI regular expression literals, and §12 omits
  starting lexical goals for non-Script/Module `ParseText` calls).
- **Model erratum:** `PostASILexicalGoal`, baked-in SpecTec reading test262 (layer `parser`, `GoalsAt` and `NextASI` in
  `spec/spectec/prose/04-derives.spectec`). Candidate offending tokens are probed under `InputElementDiv` (so `a = b\n/hi/g`
  continues as division without ASI), and once ASI inserts a virtual `;`, `GoalsAt` re-scans the following source text
  under its post-ASI syntactic context (`InputElementRegExp` at statement start); `InputElementHashbangOrRegExp` is used
  only at index 0 of `|Script|` or `|Module|`.
- **Upstream:** Checked 2026-11-19: none found (searched for "InputElementRegExp" with "semicolon insertion").

## Text

§12:

> The |InputElementRegExp| goal symbol is used in all syntactic grammar contexts where a |RegularExpressionLiteral| is permitted … In all other contexts, |InputElementDiv| is used as the lexical goal symbol.

> For example, there are no syntactic grammar contexts where both a leading division or division-assignment, and a leading |RegularExpressionLiteral| are permitted. This is not affected by semicolon insertion …

§12.10.1:

> In the following rules, “token” means the actual recognized lexical token determined using the current lexical goal symbol as described in clause …

## Problem

1. **Regular expression literals after ASI.** In `let a\n/x/.test("x")` and `do {} while (false) /z/.test("z")`, before
   a semicolon is inserted no `|RegularExpressionLiteral|` is syntactically permitted (only `=`, `,` or `;` can follow a
   `LexicalBinding`; only `;` can follow `do … while (…)`). By §12, `/` is therefore scanned under `InputElementDiv` as
   `DivPunctuator`. §12.10.1 then inserts `;` before that already-recognized `DivPunctuator` without re-lexing it under
   `InputElementRegExp`, leaving `/ x /` starting the next `Statement` with `DivPunctuator` — a *SyntaxError*! Every
   engine instead re-scans from `/` under `InputElementRegExp` after inserting `;`.
2. **Non-Script/Module `ParseText` goals.** §12 defines initial lexical goal selection (`InputElementHashbangOrRegExp`)
   only for `|Script|` and `|Module|`, omitting `CreateDynamicFunction`'s `|FormalParameters|` and `|FunctionBody|`
   variants (where `#!` at index 0 must *not* scan as `HashbangComment`, yet `/x/` at index 0 of `|FunctionBody|` must
   scan under `InputElementRegExp`).

## Examples

Tested by `tests/run/post_asi_regexp.js`:

```js
let a
/x/.test("x");
do {} while (false) /z/.test("z");
```

| | `let a` LF `/x/.test("x")` | `do {} while (false) /z/.test("z")` | `a = b` LF `/hi/g` |
|---|---|---|---|
| literal text (no re-lex after ASI) | `SyntaxError` | `SyntaxError` | division `(a = b) / hi / g` |
| V8, SpiderMonkey, JavaScriptCore | valid (`true`) | valid (`true`) | division `(a = b) / hi / g` |
| formal model (test262 reading) | valid (`true`) | valid (`true`) | division `(a = b) / hi / g` |

## Proposed wording

Specify in §12 and §12.10.1 that when ASI inserts a semicolon before an offending token, lexical scanning resumes from
the offending token's start offset under the lexical goal symbol permitted after the inserted semicolon; and specify
initial lexical goals for all syntactic `ParseText` goals (`InputElementHashbangOrRegExp` at offset 0 only for `|Script|`
and `|Module|`).

## test262

`language/asi/` and `language/expressions/postfix-increment/` test ASI before `/` expressions, and engines uniformly
re-scan `/` as a `RegularExpressionLiteral` when ASI closes the preceding statement.
