# 55. `RegExpUnicodeEscapeSequence`: escaped surrogate pairs are ambiguous in the formal grammar

- **Location:** §22.2.1 Patterns (`#sec-patterns`), `RegExpUnicodeEscapeSequence`, with §5.1.6.7 Lookahead Restrictions
  (`#sec-lookahead-restrictions`).
- **Kind:** ambiguity in the formal context-free grammar (an incomplete prose disambiguation sentence outside §5.1.6).
- **Model erratum:** `RegExpUnicodeEscapeLookahead`, baked-in SpecTec reading test262 (layer `parser`,
  `spec/html/grammar-meta.txt` and `spec/spectec/04-grammar-regexp.spectec`). SpecTec attaches a 16-prefix lookahead
  exclusion (`[lookahead ∉ { "\uDC", …, "\udf" }]`) to `[+UnicodeMode] u HexLeadSurrogate` so greedy surrogate pairing is
  unambiguous in the formal grammar and `ParseLaws.complete` holds.
- **Upstream:** Checked 2026-11-19: none found (searched for "RegExpUnicodeEscapeSequence" and "HexLeadSurrogate").

## Text

§22.2.1:

> RegExpUnicodeEscapeSequence[UnicodeMode] ::
>   `[+UnicodeMode]` `u` HexLeadSurrogate `\u` HexTrailSurrogate
>   `[+UnicodeMode]` `u` HexLeadSurrogate
>   `[+UnicodeMode]` `u` HexTrailSurrogate
>   `[+UnicodeMode]` `u` HexNonSurrogate
>   `[~UnicodeMode]` `u` Hex4Digits
>   `[+UnicodeMode]` `u{` CodePoint `}`

> Each `\\\\u` |HexTrailSurrogate| for which the choice of associated `u` |HexLeadSurrogate| is ambiguous shall be associated with the nearest possible `u` |HexLeadSurrogate| that would otherwise have no corresponding `\\\\u` |HexTrailSurrogate|.

## Problem

Under §5.1's context-free derivation relation, `RegExpUnicodeEscapeSequence[+UnicodeMode]` has both
`u HexLeadSurrogate \u HexTrailSurrogate` and unguarded `u HexLeadSurrogate` alongside `u HexTrailSurrogate`. Every
escaped surrogate pair in `[+UnicodeMode]` — and in `RegExpIdentifierStart` / `RegExpIdentifierPart` even without `/u`
or `/v`, since group names invoke `RegExpUnicodeEscapeSequence[+UnicodeMode]` unconditionally — therefore admits two
parse trees with observably different semantics:

- `/\uD800\uDC00+/u`: one quantified astral atom U+10000 vs U+D800 followed by quantified U+DC00+;
- `/[\uD800\uDC00]/u`: CharSet `{ U+10000 }` (matching `"\u{10000}"`) vs `{ 0xD800, 0xDC00 }`;
- `/(?<\uD835\uDC9C>a)/`: valid astral `ID_Start` group name vs two lone surrogates (an early *SyntaxError*).

The prose sentence after the grammar lies outside §5.1.6's formal grammar notation and literally only resolves *which*
lead surrogate a trail surrogate pairs with when multiple leads compete — presupposing, rather than stating, that
`\u` |HexTrailSurrogate| cannot remain unassociated and parse via `[+UnicodeMode] u HexTrailSurrogate`.

## Examples

```js
print(/\uD800\uDC00+/u.test("\u{10000}\u{10000}"));
print(/[\uD800\uDC00]/u.test("\u{10000}"));
print(/(?<\uD835\uDC9C>a)/.exec("a").groups["\u{1D49C}"]);
```

| | `/\uD800\uDC00+/u` | `/[\uD800\uDC00]/u` | `/(?<\uD835\uDC9C>a)/` |
|---|---|---|---|
| formal grammar without lookahead | ambiguous (2 parses) | ambiguous (2 parses) | ambiguous (valid vs SyntaxError) |
| V8, SpiderMonkey, JavaScriptCore | `true` | `true` | `"a"` |
| formal model (test262 reading) | `true` | `true` | `"a"` |

## Proposed wording

Replace the prose sentence with a formal §5.1.6.7 lookahead exclusion `[lookahead ∉ BackslashHexTrailSurrogate]` (where
`BackslashHexTrailSurrogate :: \u HexTrailSurrogate`) on `[+UnicodeMode] u HexLeadSurrogate`.

## test262

`built-ins/RegExp/unicode_restricted_quantifiable_assertion.js`, `language/literals/regexp/u-surrogate-pairs*.js` and
`language/literals/regexp/named-groups/` require greedy surrogate pairing.
