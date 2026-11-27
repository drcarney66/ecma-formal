# 63. Annex B.3.2 type errors (`Early Errors for _func_`, `Contains` on Parse Nodes), §B.3.3 synthetic blocks, and §B.1.1 comment ambiguity

- **Location:** §10.2.11 FunctionDeclarationInstantiation (`#sec-functiondeclarationinstantiation`), §16.1.7
  GlobalDeclarationInstantiation (`#sec-globaldeclarationinstantiation`), and §19.2.1.3 EvalDeclarationInstantiation
  (`#sec-evaldeclarationinstantiation`); §B.3.3 FunctionDeclarations in IfStatement Statement Clauses
  (`#sec-functiondeclarations-in-ifstatement-statement-clauses`); §B.1.1 HTML-like Comments (`#sec-html-like-comments`).
- **Kind:** type errors in normative Annex B steps, undefined synthetic AST nodes, and a lexical trivia ambiguity.
- **Model erratum:** `AnnexBReplacingAndB33`, baked-in SpecTec reading test262 (`@ph-annexb-replacing` and `@ph-contains`
  in `spec/spectec/clauses/Helpers.spectec`, `asIfSource` in `lean/Ecma/Ops/Parse.lean`, `LinEarly.linTree` in
  `lean/Ecma/Lower/LinEarly.lean`, and `TriviaElem` in `spec/spectec/prose/04-derives.spectec`).
- **Upstream:** Checked 2026-11-19: none found (searched for "Early Errors for _func_" and "synthetic |BlockStatement|").

## Text

§10.2.11 (`FunctionDeclarationInstantiation`):

> If replacing the |FunctionDeclaration| _funcDecl_ with a |VariableStatement| that has _funcName_ as a |BindingIdentifier| would not produce any Early Errors for _func_ and _paramNames_ does not contain _funcName_, then

§B.3.3:

> This production only applies when parsing non-strict code. Source text matched by this production is processed as if each matching occurrence of |FunctionDeclaration[?Yield, ?Await, ~Default]| was the sole |StatementListItem| of a |BlockStatement| occupying that position in the source text.

§B.1.1:

> MultiLineComment ::
>   `/*` FirstCommentLine? LineTerminator MultiLineCommentChars? `*/` HTMLCloseComment?

## Problem

1. **Type errors in §B.3.2's hoisting condition.** `FunctionDeclarationInstantiation` tests *"Early Errors for _func_"*,
   where `_func_` is a **Function Object** rather than the Parse Node `_code_`; and all three B.3.2 clauses write
   *"_code_ Contains _x_ is *true*"* where `_x_` is a **Parse Node** (`|Block|`, `|CaseClause|`, or `|DefaultClause|`),
   whereas §8.5.1 `Contains` only accepts a grammar symbol! SpecTec's `@ph-annexb-replacing` splices `"var " + _F_ + ";"`
   into the root parse's source text and reparses under `$GoalSymbolOf`, while `Nodes.instanceOf` widens `Contains` to
   test Parse Node identity.
2. **Undefined synthetic `|BlockStatement|` in §B.3.3.** §5.1.2 defines Parse Nodes only as parse-tree nodes of source
   text, leaving §B.3.3's *"synthetic |BlockStatement|"* without AST parentage or SDO rows. SpecTec splices `{` and `}`
   around child `FunctionDeclaration` spans (`asIfSource`) and redirects early errors (including inside reparsed covers
   via `LinEarly.linTree`) and SDOs through `$CoveredBy(|IfStatement|, node)`.
3. **Ambiguous `MultiLineComment` in §B.1.1.** Because §B.1.1 *extends* §12.4's `MultiLineComment` and makes
   `HTMLCloseComment?` optional, every multi-line comment with a newline and no `-->` (`/*a\nb*/`) has two lexical
   derivations; SpecTec existentially quantifies trivia trees in `Scans` so `ParseLaws.complete` holds.

## Examples

```js
function g(x) {
  { function f() { return 1; } }
  let y = 0;
  { function y() { return 2; } }
  if (true) function h() { return 3; }
  return [typeof f, y, typeof h].join(",");
}
print(g(0));
```

| | `g(0)` on a web-browser host |
|---|---|
| literal §B.3.2 / §B.3.3 | undefined (`Early Errors` on Function Object `_func_`, `Contains` on Parse Node `_x_`, undefined synthetic `BlockStatement`) |
| V8, SpiderMonkey, JavaScriptCore | `"function,0,function"` |
| formal model (`--web-browser`, test262 reading) | `"function,0,function"` |

## Proposed wording

In `FunctionDeclarationInstantiation` replace `_func_` with `_code_` (and state outer lexical-binding collision directly
instead of AST replacement + `Contains` on a Parse Node); in §B.3.3 give explicit Early Error and SDO rules for the four
`IfStatement` productions; and in §B.1.1 remove `?` from `HTMLCloseComment?` on the extended `MultiLineComment` rule.

## test262

`annexB/language/function-code/` and `annexB/language/statements/if/` test §B.3.2 block hoisting and §B.3.3 `if`
functions across function, global, and `eval` scopes.
