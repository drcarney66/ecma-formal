# 60. Annex B.3.2 block-function replacement steps return `~unused~` instead of `~empty~`

- **Location:** §10.2.11 FunctionDeclarationInstantiation (`#sec-functiondeclarationinstantiation`), §16.1.7
  GlobalDeclarationInstantiation (`#sec-globaldeclarationinstantiation`), and §19.2.1.3 EvalDeclarationInstantiation
  (`#sec-evaldeclarationinstantiation`), the Annex B.3.2 replacement steps, against §15.2.6 Runtime Semantics:
  Evaluation (`#sec-function-definitions-runtime-semantics-evaluation`).
- **Kind:** contradiction / wrong completion value (`eval("{ function f() {} }")` would yield `~unused~` instead of
  `*undefined*`).
- **Model erratum:** `AnnexBFunctionEvalEmpty`, baked-in SpecTec reading test262 (`@sec-function-definitions-runtime-semantics-evaluation`
  in `spec/spectec/clauses/S15.spectec`). SpecTec runs the dynamically installed B.3.2 closure, propagates abrupt
  completions, and discards its normal `~unused~` return value to return `~empty~`.
- **Upstream:** Checked 2026-11-19: none found (searched for "in place of the |FunctionDeclaration| Evaluation" and
  "Return ~unused~").

## Text

§15.2.6 (`FunctionDeclaration` Evaluation):

> 1. Return ~empty~.

§10.2.11, §16.1.7, and §19.2.1.3 (the Annex B.3.2 replacement steps):

> When the |FunctionDeclaration| _funcDecl_ is evaluated, perform the following steps in place of the |FunctionDeclaration| Evaluation algorithm … Let _funcEnv_ be the running execution context's VariableEnvironment. … Return ~unused~.

## Problem

Statement evaluation relies on `~empty~` (`UpdateEmpty`) so statements without a value preserve the prior statement's
completion value (or yield `*undefined*` in `PerformEval` when the final completion value is `~empty~`). Standard
`FunctionDeclaration` Evaluation (§15.2.6) returns `~empty~`, whereas all three Annex B.3.2 replacement algorithms run
*in place of* `FunctionDeclaration` Evaluation and end with `Return ~unused~`! Read literally on a web-browser host:

- `eval("{ function f() {} }")` evaluates `Block` → `StatementList` → `FunctionDeclaration`, returning
  `NormalCompletion(~unused~)` to `PerformEval`, where `~unused~` is neither `~empty~` nor an ECMAScript language value!
- `eval("42; { function f() {} }")` overwrites `42` with `~unused~` instead of returning `42`!

## Examples

```js
print(eval("{ function f() { return 1; } }"));
print(eval("42; { function g() {} }"));
```

| | `eval("{ function f() { return 1; } }")` | `eval("42; { function g() {} }")` |
|---|---|---|
| literal §B.3.2 (`Return ~unused~`) | `~unused~` (type error in `PerformEval`) | `~unused~` (overwrites `42`) |
| V8, SpiderMonkey, JavaScriptCore | `undefined` | `42` |
| formal model (`--web-browser`, test262 reading) | `undefined` | `42` |

## Proposed wording

Change `Return ~unused~.` to `Return ~empty~.` at the end of the replacement steps in `FunctionDeclarationInstantiation`,
`GlobalDeclarationInstantiation`, and `EvalDeclarationInstantiation`.

## test262

`annexB/language/eval-code/direct/` and `annexB/language/statements/block/` evaluate block-scoped `FunctionDeclaration`s
inside `eval` and require `*undefined*` or the preceding statement's value.
