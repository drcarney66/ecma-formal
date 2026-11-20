# 02. GatherAvailableAncestors reads the [[CycleRoot]] of a module whose evaluation threw

- **Location:** §16.2.1.6.1.3.3 GatherAvailableAncestors (`#sec-gather-available-ancestors`), step 1.a;
  §16.2.1.6.1.3.1 InnerModuleEvaluation (`#sec-innermoduleevaluation`), steps 11.c.v.2 and 16.b.viii.
- **Kind:** failing read (a field of ~empty~).
- **Model erratum:** `GatherAvailableAncestorsEmptyCycleRoot`, default reading literal; its readings: literal,
  proposed. The literal reading stops the run at step 1.a; the proposed reading is the step 1.a of Proposed wording.
- **Upstream:** Checked 2026-11-19: issue #3766 (open, 2026-03), "m.[[CycleRoot]] can be null in
  GatherAvailableAncestors", reports it; PR #3769 (open, 2026-03), "Normative: Do not read from empty [[CycleRoot]] in
  GatherAvailableAncestors", fixes it (step 1.a tests _m_.[[EvaluationError]] instead of
  _m_.[[CycleRoot]].[[EvaluationError]]) and is not merged.

## Text

> 1. For each Cyclic Module Record _ancestorModule_ of _module_.[[AsyncParentModules]], do
>    a. If _execList_ does not contain _ancestorModule_ and _ancestorModule_.[[CycleRoot]].[[EvaluationError]] is
>       ~empty~, then

## Problem

InnerModuleEvaluation (step 11.c.v.2) adds a module to the [[AsyncParentModules]] of an asynchronous dependency
before it evaluates the module's later dependencies. When a later dependency throws, InnerModuleEvaluation returns the throw completion
before step 16.b.viii sets the module's [[CycleRoot]], so [[CycleRoot]] stays ~empty~. When the asynchronous
dependency later fulfils, GatherAvailableAncestors step 1.a reads [[EvaluationError]] of ~empty~. (Evaluate step 9.a
has meanwhile set the module's own [[EvaluationError]], which the proposed step 1.a reads instead.)

## Examples

[examples/02-gather-available-ancestors/](examples/02-gather-available-ancestors/) (outputs:
[RESULTS.md](examples/RESULTS.md#02-gather-available-ancestors)): `a.mjs` imports `b.mjs` (top-level await) and
then `c.mjs` (throws); `main.mjs` imports `a.mjs`, then `b.mjs`.

```js
// b.mjs
print("b starts"); await 0; print("b ends");
// c.mjs
print("c throws"); throw "c-error";
// main.mjs
import("./a.mjs").then(() => print("a fulfilled"), e => print("a rejected: " + e))
  .then(() => import("./b.mjs")).then(() => print("b fulfilled"), e => print("b rejected: " + e));
```

| | output |
|---|---|
| literal text | `b starts`, `c throws`, `b ends`; then `b`'s fulfilment reaches step 1.a, which reads a field of ~empty~ |
| V8, SpiderMonkey | `b starts`, `c throws`, `b ends`, `a rejected: c-error`, `b fulfilled` |
| JavaScriptCore | `b starts`, `b ends`, `c throws`, `a rejected: c-error`, `b fulfilled` |
| formal model, literal reading (default) | stops at step 1.a (`stop: erratum GatherAvailableAncestorsEmptyCycleRoot sec-gather-available-ancestors#0 1.a`) |
| formal model, proposed reading | `b starts`, `c throws`, `b ends`, `a rejected: c-error`, `b fulfilled` |

JavaScriptCore evaluates `c` only after `b` resumes, a separate deviation.

## Proposed wording

Proposed: step 1.a tests the module's own [[EvaluationError]], and reads [[CycleRoot]] only after asserting that it is
set:

```diff
--- a/spec.html
+++ b/spec.html
@@ -27647,15 +27647,16 @@
               </dl>
               <emu-alg>
                 1. For each Cyclic Module Record _ancestorModule_ of _module_.[[AsyncParentModules]], do
-                  1. If _execList_ does not contain _ancestorModule_ and _ancestorModule_.[[CycleRoot]].[[EvaluationError]] is ~empty~, then
+                  1. If _execList_ does not contain _ancestorModule_ and _ancestorModule_.[[EvaluationError]] is ~empty~, then
                     1. Assert: _ancestorModule_.[[Status]] is ~evaluating-async~.
-                    1. Assert: _ancestorModule_.[[EvaluationError]] is ~empty~.
-                    1. Assert: _ancestorModule_.[[AsyncEvaluationOrder]] is an integer.
-                    1. Assert: _ancestorModule_.[[PendingAsyncDependencies]] > 0.
-                    1. Set _ancestorModule_.[[PendingAsyncDependencies]] to _ancestorModule_.[[PendingAsyncDependencies]] - 1.
-                    1. If _ancestorModule_.[[PendingAsyncDependencies]] = 0, then
-                      1. Append _ancestorModule_ to _execList_.
-                      1. If _ancestorModule_.[[HasTLA]] is *false*, perform GatherAvailableAncestors(_ancestorModule_, _execList_).
+                    1. Assert: _ancestorModule_.[[CycleRoot]] is not ~empty~.
+                    1. If _ancestorModule_.[[CycleRoot]].[[EvaluationError]] is ~empty~, then
+                      1. Assert: _ancestorModule_.[[AsyncEvaluationOrder]] is an integer.
+                      1. Assert: _ancestorModule_.[[PendingAsyncDependencies]] > 0.
+                      1. Set _ancestorModule_.[[PendingAsyncDependencies]] to _ancestorModule_.[[PendingAsyncDependencies]] - 1.
+                      1. If _ancestorModule_.[[PendingAsyncDependencies]] = 0, then
+                        1. Append _ancestorModule_ to _execList_.
+                        1. If _ancestorModule_.[[HasTLA]] is *false*, perform GatherAvailableAncestors(_ancestorModule_, _execList_).
                 1. Return ~unused~.
               </emu-alg>
               <emu-note>
```

## test262

None found: no test in `language/module-code/top-level-await/` imports a module with top-level await followed by a
module that throws.
