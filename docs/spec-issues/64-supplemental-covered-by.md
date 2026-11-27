# 64. Supplemental syntax `"covered by"` without `"must cover"`, and `DestructuringAssignmentTarget` cover-node mismatch

- **Location:** §13.3.6.1 Function Calls Evaluation (`#sec-function-calls-runtime-semantics-evaluation`), step 1;
  §15.8.5 Async Function Definitions Evaluation (`#sec-async-function-definitions-runtime-semantics-evaluation`), step 1;
  §13.15.5 Destructuring Assignment (`#sec-destructuring-assignment`), early errors, against §13.15.5.5
  IteratorDestructuringAssignmentEvaluation (`#sec-runtime-semantics-iteratordestructuringassignmentevaluation`) and
  §13.15.5.6 KeyedDestructuringAssignmentEvaluation (`#sec-runtime-semantics-keyeddestructuringassignmentevaluation`),
  step 1.a; with §5.1.5 (`#sec-syntactic-grammar`).
- **Kind:** undefined Parse Node reference (`"covered by"` used where no `"must cover"` rule exists, and on a parent
  node rather than the covering child).
- **Model erratum:** `SupplementalCoveredBy`, baked-in SpecTec reading test262 (`Ecma.reparse` / `$CoveredBy` in
  `lean/Ecma/Ops/Parse.lean` and `ProgPrim.lean`). Whenever `(n, k)` was not pre-populated by a `"must cover"` early-error
  rule, `$CoveredBy` reparses `n`'s source text on demand under goal `k`.
- **Upstream:** Checked 2026-11-19: none found (searched for "CallMemberExpression" and "DestructuringAssignmentTarget"
  with "covered by"). PR #3223 (open, 2023-11) refactors §5.1.5's cover text without adding `"must cover"` rules for
  `CallMemberExpression` or `AwaitExpression`.

## Text

§13.3.6.1 (`CallExpression : CoverCallExpressionAndAsyncArrowHead`):

> 1. Let _expr_ be the |CallMemberExpression| that is covered by |CoverCallExpressionAndAsyncArrowHead|.

§15.8.5 (`UnaryExpression : CoverAwaitExpressionAndAwaitUsingDeclarationHead`):

> 1. Let _expr_ be the |AwaitExpression| that is covered by |CoverAwaitExpressionAndAwaitUsingDeclarationHead|.

§13.15.5 (`DestructuringAssignmentTarget : LeftHandSideExpression`):

> |LeftHandSideExpression| must cover an |AssignmentPattern|.

against §13.15.5.6 (`KeyedDestructuringAssignmentEvaluation`):

> Let _assignmentPattern_ be the |AssignmentPattern| that is covered by |DestructuringAssignmentTarget|.

## Problem

1. **Supplemental syntax without `"must cover"`.** §5.1.5 defines *"the _n_ that is covered by _p_"* exclusively as the
   result of an early-error rule of the form *"_p_ must cover an _n_"*. No `"must cover"` rule anywhere in ECMA-262
   names `|CallMemberExpression|` or `|AwaitExpression|` (only prose in §13.3 and §13.5 says their interpretation *"is
   refined using"* the supplemental grammar), so step 1 of ordinary function call evaluation (`f()`) and `await`
   evaluation (`await 1`) names an undefined term!
2. **Mismatched covering node in destructuring.** §13.15.5's `"must cover"` rule is on `|LeftHandSideExpression|`, yet
   `IteratorDestructuringAssignmentEvaluation` and `KeyedDestructuringAssignmentEvaluation` ask for the
   `|AssignmentPattern|` covered by its parent `|DestructuringAssignmentTarget|`.

## Examples

```js
async function run() {
  var a, b;
  ({ x: { a }, y: [b] } = { x: { a: 10 }, y: [20] });
  return (await Promise.resolve(a)) + b;
}
run().then(v => print(v));
```

| | `run()` |
|---|---|
| literal §5.1.5 (`"covered by"` defined only for `"must cover"` target nodes) | undefined on `CallMemberExpression`, `AwaitExpression`, and `DestructuringAssignmentTarget` |
| V8, SpiderMonkey, JavaScriptCore | `30` |
| formal model (test262 reading) | `30` |

## Proposed wording

Extend §5.1.5 to define *"the _n_ that is covered by _p_"* for Supplemental Syntax refinements as well as `"must cover"`
rules, and in `IteratorDestructuringAssignmentEvaluation` / `KeyedDestructuringAssignmentEvaluation` read the
`|AssignmentPattern|` covered by the `|LeftHandSideExpression|` of `|DestructuringAssignmentTarget|`.

## test262

Every function call `f()`, `await x`, and nested destructuring assignment exercises these three sites.
