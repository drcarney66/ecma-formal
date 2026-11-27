# 66. `GetExportedNames` and `ResolveExport` assert circularity on acyclic diamond `export *` module graphs

- **Location:** §16.2.1.7.2.1 GetExportedNames (`#sec-getexportednames`), step 3.a; §16.2.1.7.2.2 ResolveExport
  (`#sec-resolveexport`), step 3.a.i.
- **Kind:** failing Assert (both assertions fail on any cycle-free diamond `export *` DAG).
- **Model erratum:** `ModuleDiamondCircularityAsserts`, baked-in SpecTec reading test262 (`assert pass` at lines 528 and
  563 of `spec/spectec/clauses/S16.spectec`). SpecTec silences both false circularity `Assert:`s so diamond `export *`
  module graphs link and evaluate without stopping.
- **Upstream:** Checked 2026-11-19: none found (searched for "starting point of an `export *` circularity" and "circular
  import request").

## Text

`GetExportedNames`:

> 3. If _exportStarSet_ contains _module_, then
>    a. Assert: We've reached the starting point of an `export *` circularity.
>    b. Return a new empty List.
> 4. Append _module_ to _exportStarSet_.

`ResolveExport`:

> 3. For each Record { [[Module]], [[ExportName]] } _record_ of _resolveSet_, do
>    a. If _module_ and _record_.[[Module]] are the same Module Record and _exportName_ is _record_.[[ExportName]], then
>       i. Assert: This is a circular import request.
>       ii. Return *null*.
> 4. Append the Record { [[Module]]: _module_, [[ExportName]]: _exportName_ } to _resolveSet_.

## Problem

Both algorithms pass a *single mutable List* (`_exportStarSet_` / `_resolveSet_`) across all recursive `export *`
branches and `Append` visited modules without popping or copying between sibling branches:

- Consider the acyclic 4-module DAG where `main.mjs` has `export * from "./b.mjs"; export * from "./c.mjs";`, both
  `b.mjs` and `c.mjs` have `export * from "./d.mjs";`, and `d.mjs` has `export const x = 1;`.
- During `main.GetExportedNames()` (e.g. `import * as ns from "./main.mjs"`), the first branch visits `b` then `d`,
  appending `d` to `_exportStarSet_`. The second branch visits `c` then `d`, sees `d` already in `_exportStarSet_`, and
  hits step 3.a (`Assert: We've reached the starting point of an export * circularity`) in a graph with **zero cycles**!
- Likewise, resolving an absent name (`import { missing } from "./main.mjs"`) or a name exported by a later star branch
  reaches `d.ResolveExport` twice and falsifies step 3.a.i (`Assert: This is a circular import request`). (Even on a
  lasso cycle `a -> b -> c -> b`, `GetExportedNames` hits step 3.a at `b`, not at the starting point `a`.)

## Examples

```js
// d.mjs: export const x = 1;
// b.mjs: export * from "./d.mjs";
// c.mjs: export * from "./d.mjs";
// main.mjs:
// export * from "./b.mjs";
// export * from "./c.mjs";
// entry.mjs:
import * as ns from "./main.mjs";
print(Object.keys(ns).join(","), ns.x);
```

| | `entry.mjs` on diamond `a -> {b, c} -> d` |
|---|---|
| literal text | `GetExportedNames` step 3.a's circularity `Assert:` fails (and `ResolveExport` step 3.a.i fails when resolving an unexported name) |
| V8, SpiderMonkey, JavaScriptCore | `"x"`, `1` |
| formal model (test262 reading, `assert pass`) | `"x"`, `1` |

## Proposed wording

Replace step 3.a of `GetExportedNames` and step 3.a.i of `ResolveExport` with `NOTE:` steps explaining that `_module_`
(or `(_module_, _exportName_)`) was already visited along the current or an earlier `export *` path.

## test262

`language/module-code/ambiguous-export-bindings/` and `namespace/` test `export *` graphs including shared targets.
