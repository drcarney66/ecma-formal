# 04. A module with top-level await never disposes its top-level resources

- **Location:** §16.2.1.7.3.2 ExecuteModule (`#sec-source-text-module-record-execute-module`), step 4.b, against step
  3.f.
- **Kind:** missing step.
- **Model erratum:** `ExecuteModuleAsyncDisposeResources`, default reading test262; its readings: literal, test262,
  proposed. The test262 and proposed readings are the same: step 4.b passes AsyncBlockStart the closure of Proposed
  wording.
- **Upstream:** Checked 2026-11-19: issue #4039 (open, 2026-10), "Disposers are not run for modules with top-level
  await", reports it; PR #4007 (closed without merging, 2026-10), "Normative: dispose resources during async module
  evaluation", proposed passing AsyncBlockStart a closure that calls DisposeResources. The declarations `using` and
  `await using` came with PR #3000 (merged 2026-06, commit f792966f2).

## Text

> 3. If _module_.[[HasTLA]] is *false*, then
>    …
>    e. Let _result_ be Completion(Evaluation of _module_.[[ECMAScriptCode]]).
>    f. Set _result_ to Completion(DisposeResources(_env_.[[DisposableResourceStack]], _result_)).
>    …
> 4. Else,
>    a. Assert: _capability_ is a PromiseCapability Record.
>    b. Perform AsyncBlockStart(_capability_, _module_.[[ECMAScriptCode]], _moduleContext_).

## Problem

A module's top-level `using` and `await using` declarations add resources to the module environment's
[[DisposableResourceStack]]. Step 3.f disposes them for a module without top-level await. Step 4.b hands the Module
Parse Node to AsyncBlockStart, which evaluates it and settles the capability. Neither AsyncBlockStart nor the
Evaluation of Module and ModuleBody (§16.2.1.14) calls DisposeResources, and no other algorithm disposes the module
environment.

So the resources of a module with [[HasTLA]] *true* are never disposed. An `await using` declaration contains an
await, so every module with one at top level has [[HasTLA]] *true*: `await using` at the top level of a module
never disposes anything, and neither does `using` in a module that awaits.

## Examples

[examples/04-execute-module-tla-dispose/](examples/04-execute-module-tla-dispose/) (outputs:
[RESULTS.md](examples/RESULTS.md#04-execute-module-tla-dispose)):

```js
// m.mjs
await using a = { async [Symbol.asyncDispose]() { print("dispose a"); } };
using b = { [Symbol.dispose]() { print("dispose b"); } };
await null;
print("end of module body");
// main.mjs
import("./m.mjs").then(function () { print("evaluation promise fulfilled"); });
```

| | output |
|---|---|
| literal text | `end of module body`, `evaluation promise fulfilled` |
| V8, JavaScriptCore | `end of module body`, `dispose b`, `dispose a`, `evaluation promise fulfilled` |
| SpiderMonkey 140 | `rejected: SyntaxError: unexpected token: identifier` (its shell parses neither `using` nor `await using`, with or without `--enable-explicit-resource-management`) |
| formal model, literal reading | `end of module body`, `evaluation promise fulfilled` |
| formal model, test262 reading (default) and proposed reading | `end of module body`, `dispose b`, `dispose a`, `evaluation promise fulfilled` |

## Proposed wording

Proposed: give AsyncBlockStart a closure that performs steps 3.e–3.f:

```diff
--- a/spec.html
+++ b/spec.html
@@ -28969,7 +28969,12 @@
                   1. Return ? _result_.
               1. Else,
                 1. Assert: _capability_ is a PromiseCapability Record.
-                1. Perform AsyncBlockStart(_capability_, _module_.[[ECMAScriptCode]], _moduleContext_).
+                1. Let _env_ be _module_.[[Environment]].
+                1. Let _asyncBody_ be a new Abstract Closure with no parameters that captures _module_ and _env_ and performs the following steps when called:
+                  1. Let _result_ be Completion(Evaluation of _module_.[[ECMAScriptCode]]).
+                  1. Set _result_ to Completion(DisposeResources(_env_.[[DisposableResourceStack]], _result_)).
+                  1. Return Completion(_result_).
+                1. Perform AsyncBlockStart(_capability_, _asyncBody_, _moduleContext_).
               1. Return ~unused~.
             </emu-alg>
           </emu-clause>
```

The closure ends in "Return Completion(_result_)", as BuiltinCallOrConstruct's _resultsClosure_ does: an Abstract
Closure gets no implicit normal completion (§5.2.4.4).

## test262

`language/statements/await-using/initializer-Symbol.asyncDispose-disposed-at-end-of-module.js`,
`initializer-Symbol.dispose-disposed-at-end-of-module.js` and the two `…-disposed-at-end-of-imported-module.js`
tests in the same directory require the disposal. They fail under the literal text.
