# 62. `CountLeftCapturingParensWithin` step 1 fails its `#sec-patterns` `Assert:` on every quantified §B.1.2 term

- **Location:** §22.2.1.2 Static Semantics: CountLeftCapturingParensWithin (`#sec-countleftcapturingparenswithin`),
  step 1, with §B.1.2.2 CountLeftCapturingParensWithin (`#sec-countleftcapturingparens-annexb`) and §B.1.2
  (`#sec-regular-expressions-patterns`).
- **Kind:** failing Assert (every quantified `ExtendedAtom` or `QuantifiableAssertion` under §B.1.2 fails step 1).
- **Model erratum:** `AnnexBCapturingParensAssert`, baked-in SpecTec reading test262 (`clause_prods @sec-patterns` in
  `spec/spectec/00-decls.spectec` and `S22.spectec`). SpecTec includes the 36 Annex B RegExp productions in
  `clause_prods @sec-patterns` so `$InstanceOf(parseNode, clause @sec-patterns)` succeeds, and dispatches `ParsePattern`
  and `CompileToCharSet` to §B.1.2 when the host supports `@sec-regular-expressions-patterns`.
- **Upstream:** Checked 2026-11-19: none found (searched for "CountLeftCapturingParensWithin" with "Annex B").

## Text

§22.2.1.2:

> 1. Assert: _parseNode_ is an instance of a production in the RegExp Pattern grammar.
> 2. Return the number of `Atom :: ( GroupSpecifier? Disjunction )` Parse Nodes contained within _parseNode_.

(where "the RegExp Pattern grammar" is `<emu-xref href="#sec-patterns">`). §B.1.2.2:

> In the definitions of CountLeftCapturingParensWithin and CountLeftCapturingParensBefore, references to “Atom :: `(` GroupSpecifier? Disjunction `)`” are to be interpreted as meaning “Atom :: `(` GroupSpecifier? Disjunction `)`” or “ExtendedAtom :: `(` GroupSpecifier? Disjunction `)`”.

## Problem

Under §B.1.2 (`#sec-regular-expressions-patterns`), every quantified atom parses as `Term :: ExtendedAtom Quantifier` or
`Term :: QuantifiableAssertion Quantifier`, and `CompileSubpattern` passes that `|ExtendedAtom|` or
`|QuantifiableAssertion|` node to `CountLeftCapturingParensWithin`. §B.1.2.2 updates step 2 to count `ExtendedAtom`
groups, but forgets to widen step 1's `Assert:` from `#sec-patterns` to include `#sec-regular-expressions-patterns` — so
every quantified term under §B.1.2 (even `/a+/`) falsifies step 1's `Assert:`!

## Examples

```js
print(/a+/.test("aa"), /(a)+/.exec("aa")[1]);
```

| | `/a+/.test("aa")` under §B.1.2 | `/(a)+/.exec("aa")[1]` under §B.1.2 |
|---|---|---|
| literal step 1 `Assert:` | fails (`ExtendedAtom` is in `#sec-regular-expressions-patterns`, not `#sec-patterns`) | fails |
| V8, SpiderMonkey, JavaScriptCore | `true` | `"a"` |
| formal model (`--web-browser`, test262 reading) | `true` | `"a"` |

## Proposed wording

In §B.1.2.2, amend step 1 of `CountLeftCapturingParensWithin` to allow productions in `#sec-patterns` or
`#sec-regular-expressions-patterns`.

## test262

Every `annexB/` RegExp test containing a quantifier exercises `CountLeftCapturingParensWithin` on an `ExtendedAtom` or
`QuantifiableAssertion`.
