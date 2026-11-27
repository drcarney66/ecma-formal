# 61. Annex B.1.2.5 `CompileSubpattern` calls undefined 2-argument `CompileAtom` on `QuantifiableAssertion`

- **Location:** §B.1.2.5 Runtime Semantics: CompileSubpattern (`#sec-compilesubpattern-annexb`), against §22.2.2.5
  CompileSubpattern (`#sec-compilesubpattern`) and §B.1.2.6 CompileAssertion (`#sec-compileassertion-annexb`).
- **Kind:** missing syntax-directed operation and arity mismatch (`/(?=a)*/` in Annex B mode has no defined compilation).
- **Model erratum:** `AnnexBQuantifiableAssertion`, baked-in SpecTec reading test262
  (`@row-compilesubpattern-quantifiableassertion-quantifier` in `spec/spectec/clauses/Helpers.spectec`). SpecTec adds an
  explicit `CompileSubpattern` row for `Term :: QuantifiableAssertion Quantifier` calling 1-argument `CompileAssertion`
  with `_regexpRecord_`.
- **Upstream:** Checked 2026-11-19: none found (searched for "QuantifiableAssertion" with "CompileSubpattern").

## Text

§B.1.2.5:

> The rule for `Term :: QuantifiableAssertion Quantifier` is the same as for `Term :: Atom Quantifier` but with |QuantifiableAssertion| substituted for |Atom|.

§22.2.2.5 (`Term :: Atom Quantifier`):

> 1. Let _m_ be CompileAtom of |Atom| with arguments _regexpRecord_ and _direction_.

## Problem

Substituting `|QuantifiableAssertion|` for `|Atom|` in `Term :: Atom Quantifier` produces `CompileAtom of
|QuantifiableAssertion| with arguments _regexpRecord_ and _direction_`. However, `|QuantifiableAssertion|` has *no*
`CompileAtom` rule — its semantics in §B.1.2.6 (`#sec-compileassertion-annexb`) is `CompileAssertion`, which takes a
*single* argument `_regexpRecord_` (no `_direction_`). Read literally, quantifying a lookahead assertion such as
`/(?=a)*/` or `/(?!b)+/` under §B.1.2 calls a non-existent SDO with the wrong number of arguments.

## Examples

```js
var m = /(?=a)+a/.exec("a");
print(m[0], /(?!b)*a/.exec("a")[0]);
```

| | `/(?=a)+a/.exec("a")[0]` | `/(?!b)*a/.exec("a")[0]` |
|---|---|---|
| literal §B.1.2.5 | undefined (`CompileAtom` has no row for `QuantifiableAssertion`) | undefined |
| V8, SpiderMonkey, JavaScriptCore | `"a"` | `"a"` |
| formal model (`--web-browser`, test262 reading) | `"a"` | `"a"` |

## Proposed wording

Write out the explicit 6-step `CompileSubpattern` algorithm for `Term :: QuantifiableAssertion Quantifier` in §B.1.2.5
with step 1 calling `CompileAssertion of |QuantifiableAssertion| with argument _regexpRecord_`.

## test262

`annexB/built-ins/RegExp/quantifiable-assertion-*.js` and `annexB/language/literals/regexp/quantifiable-assertion-*.js`
test quantified `(?=…)` and `(?!…)` assertions and require them to compile via `CompileAssertion`.
