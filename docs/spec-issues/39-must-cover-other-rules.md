# 39. Early error rules read "the |n| that is covered by" a cover that covers nothing

- **Location:** §5.1.5 The Syntactic Grammar (`#sec-syntactic-grammar`), the definition of "must cover", its item 4;
  with the early errors of §15.3.1 ArrowFunction (`#sec-arrow-function-definitions-static-semantics-early-errors`)
  and §15.9.1 AsyncArrowFunction (`#sec-async-arrow-function-definitions-static-semantics-early-errors`), and the
  covered-node steps of §8.5.1 Contains (`#sec-static-semantics-contains`), §8.2.1 BoundNames
  (`#sec-static-semantics-boundnames`) and §15.1.3 IsSimpleParameterList (`#sec-static-semantics-issimpleparameterlist`).
- **Kind:** undefined value (a rule's condition names a Parse Node that does not exist); every reading gives the same
  verdict, a SyntaxError.
- **Model erratum:** none, because no program's result depends on it: the failed "must cover" rule already makes the
  program an early SyntaxError, and ParseText leaves the number and order of the errors implementation-defined. The
  model applies a node's rules only when the nodes it contains have none, and a node's own "must cover" rules before
  its others, which gives the proposed wording's results.
- **Upstream:** Checked 2026-11-19: none found for this case (searched for "must cover" and "CoverInitializedName").
  Issue #2421 (closed, 2026-07), "Early Error rules and covering grammars", asked which early error rules apply to a
  cover; PR #3227 (merged 2026-07, commit 020735388), "Editorial: Don't check a cover for early errors", answered it
  with item 1. PR #3223 (open, 2023-11), "Editorial: Separate cover grammar text into a subsection with autolink
  targets", moves the definition into a new subsection, Cover Productions, with its items as they are.

## Text

§5.1.5 defines "_p_ must cover an _n_" by a list of four items (item 3 with two sub-items), quoted here in order:

> No early error rules are applied to _p_ or any of its descendants.
>
> The sequence of tokens originally matched by _p_ is parsed again using _n_ as the goal symbol. …
>
> If the sequence of tokens can be parsed as a single instance of _n_, with no tokens left over, then:
>
> We refer to that instance of _n_ (a Parse Node, unique for a given _p_) as “the _n_ that is covered by _p_”.
>
> Early error rules are applied to the _n_ that is covered by _p_ and to its descendants, …
>
> Otherwise (if the parse fails), it is an early Syntax Error.

The rule is one of a production above _p_, beside rules that look through _p_:

> ArrowFunction : ArrowParameters `=>` ConciseBody
> - It is a Syntax Error if |ArrowParameters| Contains |YieldExpression| is *true*.
> - …
>
> ArrowParameters : CoverParenthesizedExpressionAndArrowParameterList
> - |CoverParenthesizedExpressionAndArrowParameterList| must cover an |ArrowFormalParameters|.
>
> AsyncArrowFunction : CoverCallExpressionAndAsyncArrowHead `=>` AsyncConciseBody
> - |CoverCallExpressionAndAsyncArrowHead| must cover an |AsyncArrowHead|.
> - It is a Syntax Error if any element of the BoundNames of |CoverCallExpressionAndAsyncArrowHead| also occurs in
>   the LexicallyDeclaredNames of |AsyncConciseBody|.

Contains, BoundNames and IsSimpleParameterList at these covers begin with "Let _formals_ be the
|ArrowFormalParameters| that is covered by |CoverParenthesizedExpressionAndArrowParameterList|." or "Let _head_ be
the |AsyncArrowHead| that is covered by |CoverCallExpressionAndAsyncArrowHead|." The rules of §16.1.1 that a
Script's |StatementList| not Contain `super` or |NewTarget| reach every arrow function of the Script the same way.

## Problem

When the reparse of item 2 fails there is no "_n_ that is covered by _p_", so the conditions above refer to nothing,
and their steps have no result. Item 1 stops rules from applying to _p_ and below it, not to the productions above
it. §5.2.5 asks an implementation to "validate all of the early error rules of the productions used to parse" the
source, and §11.1.6 ParseText, step 2, to "analyse the parse result for any early error conditions"; neither says that a rule
whose condition cannot be evaluated is skipped, nor in what order the rules are evaluated. The verdict is not in
doubt, since item 4 is itself an early error, but a reader evaluating the rules as written meets an undefined step
before reaching it.

## Examples

[examples/39-must-cover-other-rules.js](examples/39-must-cover-other-rules.js) (outputs:
[RESULTS.md](examples/RESULTS.md#39-must-cover-other-rulesjs)) evaluates each source with indirect eval and prints
the error's constructor:

| source | literal text | V8, SpiderMonkey, JavaScriptCore | formal model |
|---|---|---|---|
| `([...x = []]) => {};` | no result (Contains through the cover) | SyntaxError | SyntaxError |
| `([...x, y]) => {};` | no result | SyntaxError | SyntaxError |
| `(a, ...b,) => {};` | SyntaxError (no parse: not a cover case) | SyntaxError | SyntaxError |
| `async (...x = []) => {};` | no result (BoundNames through the cover) | SyntaxError | SyntaxError |
| `async\n(foo) => {};` | no result | SyntaxError | SyntaxError |
| `(x) => {};` | no error | no error | no error |

## Proposed wording

```diff
--- a/spec.html
+++ b/spec.html
@@ -408,7 +408,7 @@
             <li>Early error rules are applied to the _n_ that is covered by _p_ and to its descendants, as modified by further cases of “must cover”.</li>
           </ol>
         </li>
-        <li>Otherwise (if the parse fails), it is an early Syntax Error.</li>
+        <li>Otherwise (if the parse fails), it is an early Syntax Error, and an early error rule whose evaluation needs the _n_ that is covered by _p_ is not applied.</li>
       </ol>
     </emu-clause>
 
```

## test262

The SyntaxErrors are required by `language/expressions/arrow-function/dstr/{,dflt-}ary-ptrn-rest-{init,not-final}-*.js`,
`language/expressions/async-arrow-function/{dflt-params-rest,early-errors-arrow-formals-lineterminator,rest-params-trailing-comma-early-error}.js`
and their siblings in the other function forms; every reading that reaches item 4 passes them.
