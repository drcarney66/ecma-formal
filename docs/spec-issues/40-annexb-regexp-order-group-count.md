# 40. Annex B: what §B.1.2's ordered alternatives choose, and which |Pattern| its group-number condition counts

- **Location:** §B.1.2 Regular Expressions Patterns (`#sec-regular-expressions-patterns`), its first paragraph and
  AtomEscape's second alternative, with its note; §22.2.1.2 CountLeftCapturingParensWithin
  (`#sec-countleftcapturingparenswithin`) and §B.1.2.2 CountLeftCapturingParensWithin and
  CountLeftCapturingParensBefore (`#sec-countleftcapturingparens-annexb`).
- **Kind:** ambiguity (the ordering sentence); self-reference (the condition).
- **Model erratum:** `AnnexBRegExpOrder` and `AnnexBGroupCount`, default reading test262 for both; the readings of
  each: literal, test262, proposed. The test262 and proposed readings read the ordering as commitment for the
  nonterminals §B.1.2 gives, and take the count from a parse with the condition taken as true: the proposed wording
  below. Under the literal reading the run stops on a pattern with more than one parse.
- **Upstream:** Checked 2026-11-19: PR #2445 (open, 2021-06), "Editorial: Eliminate order-disambiguation from Annex B
  Pattern-grammar", replaces the ordering sentence by lookahead restrictions; its ConstrainedDecimalEscape keeps the
  condition's "the |Pattern| containing |DecimalEscape|"; it is not merged. PR #2228 (merged 2020-12, commit
  67dc0c208), "Editorial: Swap 2 alternatives of Term in Annex B", swapped Term's alternatives because, under the
  ordering sentence, `Atom` matches wherever `Atom Quantifier` would.

## Text

The first paragraph of §B.1.2 (its "…" is a cross-reference to §22.2.1 Patterns):

> The syntax of … is modified and extended as follows. These changes introduce ambiguities that are broken by
> the ordering of grammar productions and by contextual information. When parsing using the following grammar, each
> alternative is considered only if previous production alternatives do not match.

> AtomEscape[UnicodeMode, NamedCaptureGroups] ::
>   [+UnicodeMode] DecimalEscape
>   [~UnicodeMode] DecimalEscape [> but only if the CapturingGroupNumber of |DecimalEscape| is ≤
>   CountLeftCapturingParensWithin(the |Pattern| containing |DecimalEscape|)]
>   …

and the note after the grammar (the guard elided is [~UnicodeMode]):

> When the same left-hand sides occurs with both [+UnicodeMode] and … guards it is to control the disambiguation
> priority.

## Problem

The grammar needs an order: `/a{1}/` is one Term (`a` quantified) or four (`a`, `{`, `1`, `}`), `\b` is an Assertion
or an identity escape, `\1` a DecimalEscape or a LegacyOctalEscapeSequence. §5.1 defines a grammar's language and
parse trees declaratively; the sentence is procedural, and says neither what an alternative "matches" nor how nested
choices combine. Three readings:

- Commitment for every nonterminal, as in a parsing expression grammar: no pattern with a Term parses, since §22.2.1's
  `Alternative :: [empty] | Alternative Term` always takes `[empty]`. But Alternative and Disjunction are §22.2.1's,
  not "the following grammar".
- Commitment for the nonterminals §B.1.2 gives: a node uses an alternative only if no earlier alternative of its
  nonterminal derives any span from where it starts. It is well defined and gives the engines' answers: `\b` is an
  Assertion wherever it occurs, so `/\b*/` has nothing to repeat.
- A priority among complete parses (a later alternative is used only where no earlier one leads to a parse of the
  whole pattern): also well defined, but it accepts `/\b*/`, `/\B+/` and `/a\b?/`, whose only complete parse
  quantifies `b` read as an identity escape.

The condition reads "the |Pattern| containing |DecimalEscape|", the tree being chosen, and whether `\N` is a
DecimalEscape is part of that choice: it is evaluated on the tree it selects. For `/\1(a)/` the Pattern has one
capturing group however `\1` is read, so only the backreference is consistent; but the text gives no rule for finding
the tree, and a pattern whose count depended on the choice could have no consistent parse or two. It does not: the
alternatives the condition decides between derive only digits, never a `(`. So the count can be taken from the parse
with the condition true.

## Examples

[examples/40-annexb-regexp-order-group-count.js](examples/40-annexb-regexp-order-group-count.js) (outputs:
[RESULTS.md](examples/RESULTS.md#40-annexb-regexp-order-group-countjs)) compiles each pattern with no flags and tests
the string against it:

| pattern on string | commitment for B.1.2's nonterminals | priority among complete parses | V8, SpiderMonkey, JavaScriptCore | formal model, §B.1.2 on (test262, proposed) |
|---|---|---|---|---|
| `a{1}` on `a` | `true` (one Term) | `true` | `true` | `true` |
| `\b*` on `` | SyntaxError (`\b` an Assertion) | `true` (`b*`) | SyntaxError | SyntaxError |
| `a\b?` on `ab` | SyntaxError | `true` (`b?`) | SyntaxError | SyntaxError |
| `\x4` on `x4` | `true` (identity escape `x`, then `4`) | `true` | `true` | `true` |
| `{,1}` on `{,1}` | `true` (four pattern characters) | `true` | `true` | `true` |
| `[\b]` on backspace | `true` (ClassEscape `b`) | `true` | `true` | `true` |
| `\c1` on `\c1` | `true` (a lone `\`, then `c1`) | `true` | `true` | `true` |
| `\1(a)` on `a` | `true` (a backreference) | `true` | `true` | `true` |
| `\2(a)(b)` on `ab` | `true` (a backreference) | `true` | `true` | `true` |
| `\3(a)(b)` on `\x03ab` | `true` (an octal escape) | `true` | `true` | `true` |
| `(a)\10` on `a\x08` | `true` (an octal escape) | `true` | `true` | `true` |
| `\1` on `\x01` | `true` (an octal escape) | `true` | `true` | `true` |

The formal model's column is `ecma-run --annex-b sec-regular-expressions-patterns`, under the test262 and the
proposed readings of both errata (the same output). Under the literal reading of either
erratum the run stops at the first pattern, `a{1}`, which has more than one parse (`stop: residue
formal-parsetextin#0 2`). The model's run in RESULTS.md is on ecma-run's default host, with Annex B off, and is not a
witness here.

## Proposed wording

```diff
--- a/spec.html
+++ b/spec.html
@@ -53867,7 +53867,7 @@
 
     <emu-annex id="sec-regular-expressions-patterns">
       <h1>Regular Expressions Patterns</h1>
-      <p>The syntax of <emu-xref href="#sec-patterns"></emu-xref> is modified and extended as follows. These changes introduce ambiguities that are broken by the ordering of grammar productions and by contextual information. When parsing using the following grammar, each alternative is considered only if previous production alternatives do not match.</p>
+      <p>The syntax of <emu-xref href="#sec-patterns"></emu-xref> is modified and extended as follows. These changes introduce ambiguities that are broken by the ordering of grammar productions and by contextual information. When parsing using the following grammar, a Parse Node of a nonterminal whose productions are given below uses an alternative only if no earlier alternative of that nonterminal matches any sequence of code points starting at the same position.</p>
       <p>This alternative pattern grammar and semantics only changes the syntax and semantics of BMP patterns. The following grammar extensions include productions parameterized with the [UnicodeMode] parameter. However, none of these extensions change the syntax of Unicode patterns recognized when parsing with the [UnicodeMode] parameter present on the goal symbol.</p>
       <h2>Syntax</h2>
       <emu-grammar type="definition">
@@ -53916,7 +53916,7 @@
 
         AtomEscape[UnicodeMode, NamedCaptureGroups] ::
           [+UnicodeMode] DecimalEscape
-          [~UnicodeMode] DecimalEscape [> but only if the CapturingGroupNumber of |DecimalEscape| is &le; CountLeftCapturingParensWithin(the |Pattern| containing |DecimalEscape|)]
+          [~UnicodeMode] DecimalEscape [> but only if the CapturingGroupNumber of |DecimalEscape| is &le; CountLeftCapturingParensWithin(_P_), where _P_ is the |Pattern| that results from parsing the source text matched by the |Pattern| containing |DecimalEscape| again, with this condition taken to be true]
           CharacterClassEscape[?UnicodeMode]
           CharacterEscape[?UnicodeMode, ?NamedCaptureGroups]
           [+NamedCaptureGroups] `k` GroupName[?UnicodeMode]
```

## test262

`annexB/built-ins/RegExp` and `annexB/language/literals/regexp` test these choices (`legacy-octal-escape.js` for
`\1`, `RegExp-decimal-escape-not-capturing.js` for `\2` with one group, `extended-pattern-char.js`,
`identity-escape.js`, `quantifiable-assertion-followed-by.js`); they pass under both commitment for B.1.2's
nonterminals and priority among complete parses. None tests `/\b*/` or `/a\b?/` under Annex B, where the two
readings differ.
