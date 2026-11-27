# 58. Cover-grammar reparsing omits semicolons inserted by ASI inside the cover

- **Location:** §5.1.5 The Syntactic Grammar (`#sec-syntactic-grammar`), the definition of "must cover", step 2; §12.10
  Automatic Semicolon Insertion (`#sec-automatic-semicolon-insertion`).
- **Kind:** missing case (reparse of a cover containing ASI-terminated statements inside nested function or class bodies).
- **Model erratum:** `CoverMatchedVirtualSemis`, baked-in SpecTec reading test262 (layer `parser`, `GrammarCtx.CoverIs`
  in `spec/spectec/prose/06-node-rel.spectec`, `Ecma.reparse` in `lean/Ecma/Ops/Parse.lean`, and `Relabel.relabel` in
  `lean/Engine/Model/Relabel.lean`). SpecTec preserves virtual semicolons inside reparsed covers so nested statements
  closed by ASI remain valid when the cover is refined.
- **Upstream:** Checked 2026-11-19: none found (searched for "originally matched by" with "semicolon insertion").

## Text

§5.1.5:

> The sequence of tokens originally matched by _p_ is parsed again using _n_ as the goal symbol.

§12.10:

> Most ECMAScript statements and declarations must be terminated with a semicolon. Such semicolons may always appear explicitly in the source text. For convenience, however, such semicolons may be omitted from the source text in certain situations. These situations are described by saying that semicolons are automatically inserted into the source code token stream in those situations.

## Problem

§5.1.5 and §12 define lexical scanning and ASI only when parsing `|Script|` or `|Module|`, not supplemental cover goals
(`|ParenthesizedExpression|`, `|ArrowFormalParameters|`, `|AsyncArrowHead|`, `|AssignmentPattern|`). When a cover `_p_`
contains a nested function or class body with an omitted semicolon — such as `(function () { let a\n return 1 })()`,
`(x = function () { let a\n return 2 }) => x()`, or `({ m() { let a\n return 3 } } = {})` — if *"the sequence of tokens
originally matched by _p_"* meant only source lexical tokens and cover reparsing did not perform ASI, reparsing `_p_`
as `_n_` would fail with an early *SyntaxError*.

## Examples

```js
print((function () { let a
  return 1 })());
print(((x = function () { let b
  return 2 }) => x())());
```

| | `(function () { let a` LF `return 1 })()` | `((x = function () { let b` LF `return 2 }) => x())()` |
|---|---|---|
| source lexical tokens only, no ASI on cover | `SyntaxError` | `SyntaxError` |
| V8, SpiderMonkey, JavaScriptCore | `1` | `2` |
| formal model (test262 reading) | `1` | `2` |

## Proposed wording

Clarify in §5.1.5 ("must cover", step 2) that the sequence of tokens matched by `_p_` includes any semicolons
automatically inserted within `_p_` during the enclosing parse (with no fresh lexing or semicolon insertion performed
during the cover reparse).

## test262

Hundreds of `test262` files wrap ASI-terminated statements inside IIFEs `(function() { ... })()` or arrow default
initializers, all of which parse through `CoverParenthesizedExpressionAndArrowParameterList`.
