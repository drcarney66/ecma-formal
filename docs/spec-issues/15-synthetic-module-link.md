# 15. A second Link of a Synthetic Module Record resets its exports, observably with JSON modules

- **Location:** §16.2.1.8.4.4 Link ( ) of a Synthetic Module Record (`#sec-smr-Link`), steps 1–4, reached from
  §16.2.1.6.1.2.1 InnerModuleLinking (`#sec-InnerModuleLinking`), step 1.a, and §16.2.1.6.1.3.1 InnerModuleEvaluation
  (`#sec-innermoduleevaluation`), step 1.a.
- **Kind:** missing step (an idempotence check).
- **Model erratum:** `SyntheticModuleLinkResets`, default reading literal; its readings: literal, proposed (the
  proposed reading is the proposed wording below); the literal reading has no stop.
- **Upstream:** Checked 2026-11-19: issue #3989 (open, 2026-09), "Bug: Link() and Evaluate() on synthetic module
  records should be idempotent", reports it for Link and Evaluate and says it is "not observable on the web because
  both JSON modules and CSS modules are pre-evaluated"; it has no comments, and no pull request was found.

## Text

Link of a Synthetic Module Record:

> 1. Let _realm_ be _module_.[[Realm]].
> 2. Let _envRecord_ be NewModuleEnvironment(_realm_.[[GlobalEnv]]).
> 3. Set _module_.[[Environment]] to _envRecord_.
> 4. For each String _exportName_ of _module_.[[ExportNames]], do
>    a. Perform ! _envRecord_.CreateMutableBinding(_exportName_, *false*).
>    b. Perform ! _envRecord_.InitializeBinding(_exportName_, *undefined*).

InnerModuleLinking:

> 1. If _module_ is not a Cyclic Module Record, then
>    a. Perform ? _module_.Link().

InnerModuleEvaluation:

> 1. If _module_ is not a Cyclic Module Record, then
>    a. Perform ? EvaluateModuleSync(_module_).

## Problem

Every graph that reaches a Synthetic Module Record links it again and evaluates it again. Link replaces its
environment with one whose bindings are *undefined*, and an importer's indirect binding reads the module's current
[[Environment]] (§9.1.1.5.1 GetBindingValue), so every earlier importer sees *undefined* until Evaluate runs again.
For a JSON module, re-evaluation sets the same value back, which hides the reset once Evaluate has run again; but
between the two, a module that the second graph evaluates first can read the old importer's binding. Below,
`main.mjs` imports `j.json`; a later `import("./other.mjs")` links `j.json` again and evaluates `probe.mjs`, which
calls back into `main.mjs`, before `j.json`.

## Examples

[examples/15-synthetic-module-link/](examples/15-synthetic-module-link/) (outputs:
[RESULTS.md](examples/RESULTS.md#15-synthetic-module-link)):

```js
// j.json
{"a": 1}
// main.mjs
import j from "./j.json" with { type: "json" };
export function readJ() { return j; }
print("main sees " + JSON.stringify(j));
import("./other.mjs").then(function () { print("after other: " + JSON.stringify(j)); },
                           function (e) { print("rejected: " + e); });
// other.mjs
import "./probe.mjs";
import k from "./j.json" with { type: "json" };
export { k };
// probe.mjs
import { readJ } from "./main.mjs";
print("probe sees " + JSON.stringify(readJ()));
```

| | output |
|---|---|
| literal text | `main sees {"a":1}`, `probe sees undefined`, `after other: {"a":1}` |
| V8, SpiderMonkey (with `--enable-import-attributes`), JavaScriptCore | `main sees {"a":1}`, `probe sees {"a":1}`, `after other: {"a":1}` |
| formal model (literal reading) | `main sees {"a":1}`, `probe sees undefined`, `after other: {"a":1}` |
| formal model (proposed reading) | `main sees {"a":1}`, `probe sees {"a":1}`, `after other: {"a":1}` |

Without `--enable-import-attributes`, the SpiderMonkey 140 shell rejects the import attribute (a SyntaxError). The
model's rows are `ecma-run --module --module-dir examples/15-synthetic-module-link/
examples/15-synthetic-module-link/main.mjs`, with `--erratum SyntheticModuleLinkResets=proposed` for the second.

## Proposed wording

Proposed: return when the module is already linked, as a Cyclic Module Record's Link does through its [[Status]]:

```diff
--- a/spec.html
+++ b/spec.html
@@ -29135,6 +29135,7 @@
             </dl>
 
             <emu-alg>
+              1. If _module_.[[Environment]] is not ~empty~, return NormalCompletion(~unused~).
               1. Let _realm_ be _module_.[[Realm]].
               1. Let _envRecord_ be NewModuleEnvironment(_realm_.[[GlobalEnv]]).
               1. Set _module_.[[Environment]] to _envRecord_.
```

Evaluate has the same shape, but making it idempotent needs state that a Synthetic Module Record does not have (it
has no [[Status]]), for example a stored promise to return; the check above is enough for the reset shown here.

## test262

No test imports a JSON module from two graphs linked at different times and reads it in between.
`language/import/import-attributes/json-idempotency.js` links its JSON module again with a dynamic `import()`, but
reads it only once that import has settled, after the second Evaluate has set the value back.
