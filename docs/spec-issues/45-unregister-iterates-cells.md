# 45. FinalizationRegistry.prototype.unregister removes cells from the List it iterates

- **Location:** §26.2.3.3 FinalizationRegistry.prototype.unregister
  (`#sec-finalization-registry.prototype.unregister`), step 5.
- **Kind:** ambiguity (a For each over a List its own body changes).
- **Model erratum:** `UnregisterIteratesCopy`, default reading test262; its readings: literal, test262, proposed.
  The test262 and proposed readings iterate a copy of [[Cells]], the proposed wording below; the literal reading
  walks [[Cells]] by position, as it is at each round.
- **Upstream:** Checked 2026-11-19: none found (searched for FinalizationRegistry with unregister). The step came with
  PR #2089 (merged 2020-08, commit 71c089717), "Normative: Add Weakrefs and FinalizationRegistry".

## Text

> 5. For each Record { [[WeakRefTarget]], [[HeldValue]], [[UnregisterToken]] } _cell_ of
> _finalizationRegistry_.[[Cells]], do
>     a. If _cell_.[[UnregisterToken]] is not ~empty~ and SameValue(_cell_.[[UnregisterToken]], _unregisterToken_)
> is *true*, then
>         i. Remove _cell_ from _finalizationRegistry_.[[Cells]].
>         ii. Set _removed_ to *true*.

## Problem

Step 5.a.i removes _cell_ from the List step 5 iterates. The text says what a For each is ("the iterative
application of its substeps", §5.2) and in which order it visits a List ("the order of the
elements in the List", §6.2.2), but not what it visits when its body changes that List. Two readings:

- The loop walks the List as it is at each round, by position. Removing the current cell moves the next one into
  its position, which the loop has passed: of two cells in a row with the token, the second stays.
- The loop walks the elements the List had when it started. Every cell with the token is removed.

No other For each of the specification removes from the List it iterates. CleanupFinalizationRegistry (§9.12), which
also removes cells, avoids the question: its While loop chooses a cell again each round.

## Examples

[examples/45-finalizationregistry-unregister.js](examples/45-finalizationregistry-unregister.js) (outputs:
[RESULTS.md](examples/RESULTS.md#45-finalizationregistry-unregisterjs)):

```js
var fr = new FinalizationRegistry(function () {});
var token = {}, t1 = {}, t2 = {}, t3 = {};
fr.register(t1, 1, token);
fr.register(t2, 2, token);
fr.register(t3, 3, {});
print(fr.unregister(token));
print(fr.unregister(token));
```

| | first `unregister` | second `unregister` |
|---|---|---|
| walked by position (first reading) | `true` | `true` |
| walked over the starting elements (second reading) | `true` | `false` |
| V8, SpiderMonkey, JavaScriptCore | `true` | `false` |
| formal model, literal reading | `true` | `true` |
| formal model, test262 and proposed readings (the default: test262) | `true` | `false` |

The model's rows are `ecma-run --erratum UnregisterIteratesCopy=literal|test262|proposed` on the example. The
model's test `tests/run/errata_unregister_two_cells_literal.js`, run with `--erratum UnregisterIteratesCopy=literal`,
prints `normal: "true|true"`.

## Proposed wording

Iterate a copy (§5.2's "Let _x_ be a copy of _someValue_"):

```diff
-          1. For each Record { [[WeakRefTarget]], [[HeldValue]], [[UnregisterToken]] } _cell_ of _finalizationRegistry_.[[Cells]], do
+          1. Let _cells_ be a copy of _finalizationRegistry_.[[Cells]].
+          1. For each Record { [[WeakRefTarget]], [[HeldValue]], [[UnregisterToken]] } _cell_ of _cells_, do
```

Or say once, in §5.2, that a For each over a List visits the elements the List has when the step starts.

## test262

`built-ins/FinalizationRegistry/prototype/unregister/unregister-object-token.js` and `unregister-symbol-token.js`
register two cells with one token in a row (target1 twice with one token; target2 and target3 with another: `token2`
in the first file, `Symbol.hasInstance` in the second) and require the second unregister of each token to return
*false*: the second reading.
