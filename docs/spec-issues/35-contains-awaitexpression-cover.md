# 35. Contains never finds an |AwaitExpression|: `async function f(x = await 1) {}` has no early error

- **Location:** §8.5.1 Static Semantics: Contains (`#sec-static-semantics-contains`), the default definition, step
  1.a, and its rows; §13.5 Unary Operators (`#sec-unary-operators`), UnaryExpression's grammar and Supplemental
  Syntax; the six rules "… Contains |AwaitExpression| is *true*" of §15.3.1 (ArrowFunction), §15.6.1
  (AsyncGeneratorMethod, AsyncGeneratorDeclaration/Expression), §15.8.1 (AsyncMethod,
  AsyncFunctionDeclaration/Expression) and §15.9.1 (AsyncArrowFunction).
- **Kind:** missing case (no Contains row for a cover); six early errors never apply.
- **Model erratum:** `ContainsAwaitCover`, default reading test262; its readings: literal, test262, proposed. The
  test262 and proposed readings count `UnaryExpression : CoverAwaitExpressionAndAwaitUsingDeclarationHead` (and not
  the cover of an |AwaitUsingDeclaration|) as an |AwaitExpression|.
- **Upstream:** Checked 2026-11-19: none found (searched for "CoverAwaitExpressionAndAwaitUsingDeclarationHead", no
  hits). The cover came with PR #3000 (merged 2026-06, commit f792966f2), which replaced UnaryExpression's `[+Await]
  AwaitExpression[?Yield]` by it; issue #917 (closed, 2018-03), "await in parameters", predates it.

## Text

An `await` expression parses as the cover:

> UnaryExpression[Yield, Await] : … `[+Await]` CoverAwaitExpressionAndAwaitUsingDeclarationHead[?Yield]
>
> CoverAwaitExpressionAndAwaitUsingDeclarationHead[Yield] : `await` UnaryExpression[?Yield, +Await]

and |AwaitExpression| is only its refined interpretation (Supplemental Syntax):

> When processing an instance of the production UnaryExpression : CoverAwaitExpressionAndAwaitUsingDeclarationHead
> the interpretation of |CoverAwaitExpressionAndAwaitUsingDeclarationHead| is refined using the following grammar:
> AwaitExpression[Yield] : `await` UnaryExpression[?Yield, +Await]

Contains has no row for that production, so the default definition applies:

> 1. For each child node _child_ of this Parse Node, do
>    a. If _child_ is an instance of _symbol_, return *true*.
>    b. If _child_ is an instance of a nonterminal, then
>       i. Let _contained_ be the result of _child_ Contains _symbol_.
>       ii. If _contained_ is *true*, return *true*.
> 2. Return *false*.

The rules (one of each form):

> It is a Syntax Error if |ArrowParameters| Contains |AwaitExpression| is *true*.
>
> It is a Syntax Error if |FormalParameters| Contains |AwaitExpression| is *true*.
>
> It is a Syntax Error if |CoverCallExpressionAndAsyncArrowHead| Contains |AwaitExpression| is *true*.

## Problem

No parse tree has an |AwaitExpression| node: the parse produces the cover, and no rule makes it "cover" an
|AwaitExpression| except when the production is "processed", as Evaluation does ("Let _expr_ be the
|AwaitExpression| that is covered by …"). Step 1.a compares each child with _symbol_; the child of
`UnaryExpression : CoverAwaitExpressionAndAwaitUsingDeclarationHead` is a
|CoverAwaitExpressionAndAwaitUsingDeclarationHead|. So "X Contains |AwaitExpression|" is *false* for every X and
the six rules never apply: read literally, `async function f(x = await 1) {}` is a function whose parameter
initializer awaits.

The other covers have Contains rows that look through them (`ArrowParameters :
CoverParenthesizedExpressionAndArrowParameterList`, ``AsyncArrowFunction : CoverCallExpressionAndAsyncArrowHead
`=>` AsyncConciseBody``). Were |AwaitExpression| itself a right-hand side of UnaryExpression, step 1.a would find
it. |YieldExpression| has no cover, and the "Contains |YieldExpression|" rules work.

The row is for the UnaryExpression production only: under ``AwaitUsingDeclaration :
CoverAwaitExpressionAndAwaitUsingDeclarationHead BindingList `;` `` the cover is an |AwaitUsingDeclarationHead|.
(Note a companion gap in §15.9.1: `AsyncArrowFunction`'s early error checks unrefined
`|CoverCallExpressionAndAsyncArrowHead| Contains |AwaitExpression|`, whereas in `[~Await]` contexts `async (x = await + 1) => x`
parses `await + 1` as binary `+` inside `CoverCallExpressionAndAsyncArrowHead` and only becomes an `AwaitExpression`
inside the refined `|AsyncArrowHead|`.)

## Examples

[examples/35-contains-awaitexpression-cover.js](examples/35-contains-awaitexpression-cover.js) (outputs:
[RESULTS.md](examples/RESULTS.md#35-contains-awaitexpression-coverjs)) evaluates each source as a Script (indirect
eval) or with the AsyncFunction constructor and prints the error's constructor or `no error`:

| source | literal text (and the model's literal reading) | V8, SpiderMonkey | JavaScriptCore | formal model, test262 and proposed readings |
|---|---|---|---|---|
| `async function f(x = await 1) {}` | no error | SyntaxError | SyntaxError | SyntaxError |
| `(async function* (x = await 1) {})` | no error | SyntaxError | SyntaxError | SyntaxError |
| `({ async m(x = await 1) {} })` | no error | SyntaxError | SyntaxError | SyntaxError |
| `({ async *m(x = await 1) {} })` | no error | SyntaxError | SyntaxError | SyntaxError |
| `async function g() { async (x = await 1) => 0; }` | no error | SyntaxError | SyntaxError | SyntaxError |
| `AsyncFunction('x = await 1', '')` | no error | SyntaxError | SyntaxError | SyntaxError |
| `async function h() { await 1; }` | no error | no error | no error | no error |
| `async function k(x = function () { var await; }) {}` | no error | no error | SyntaxError | no error |
| `(async function () { class C { static { } } })` | no error | no error | no error | no error |

JavaScriptCore's SyntaxError for `k` is its own deviation (the `await` in the nested FunctionExpression is an
identifier, and Contains does not look into a function), not this defect.

## Proposed wording

A Contains row beside the other covers' rows:

```diff
--- a/spec.html
+++ b/spec.html
@@ -9550,6 +9550,12 @@
       <emu-alg>
         1. Let _formals_ be the |ArrowFormalParameters| that is covered by |CoverParenthesizedExpressionAndArrowParameterList|.
         1. Return _formals_ Contains _symbol_.
+      </emu-alg>
+      <emu-grammar>UnaryExpression : CoverAwaitExpressionAndAwaitUsingDeclarationHead</emu-grammar>
+      <emu-alg>
+        1. If _symbol_ is |AwaitExpression|, return *true*.
+        1. Let _expr_ be the |AwaitExpression| that is covered by |CoverAwaitExpressionAndAwaitUsingDeclarationHead|.
+        1. Return _expr_ Contains _symbol_.
       </emu-alg>
       <emu-grammar>
         AsyncArrowFunction : `async` AsyncArrowBindingIdentifier `=>` AsyncConciseBody
```

## test262

`built-ins/AsyncGeneratorFunction/instance-await-expr-in-param.js`,
`language/expressions/async-generator/early-errors-expression-formals-contains-await-expr.js`,
`language/expressions/async-arrow-function/await-as-param-nested-arrow-body-position.js` and the other `await`
parameter tests require the SyntaxErrors. They fail under the literal text and pass under the proposed wording.
