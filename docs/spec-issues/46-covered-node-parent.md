# 46. A covered Parse Node is outside the tree that covers it

- **Location:** §5.1.5 The Syntactic Grammar (`#sec-syntactic-grammar`), the definition of "must cover", items 2–3;
  with §15.10.1 Static Semantics: IsInTailPosition (`#sec-isintailposition`), steps 2–3, §15.10.2 Static Semantics:
  HasCallInTailPosition (`#sec-static-semantics-hascallintailposition`), its row for `PrimaryExpression :
  CoverParenthesizedExpressionAndArrowParameterList`, and §13.2.9.2 and §13.3.6.1 Runtime Semantics: Evaluation
  (`#sec-grouping-operator-runtime-semantics-evaluation`, `#sec-function-calls-runtime-semantics-evaluation`).
- **Kind:** missing case (the tree relations "contained within", "most closely contains" and "the parent of" are
  not defined for a covered node).
- **Model erratum:** `CoveredNodeParent`, default reading test262; its readings: literal, test262, proposed. The
  test262 and proposed readings put the covered node in the cover's place in the tree, as the proposed wording says;
  the readings are switched in the model's parser.
- **Upstream:** Checked 2026-11-19: none found (searched for "must cover" and "IsInTailPosition"). PR #3223 (open,
  2023-11) moves the definition into a new subsection, Cover Productions, with items 2–3 as they are (it makes
  "covered by" the defined term).

## Text

§5.1.5, "_p_ must cover an _n_", items 2 and 3:

> The sequence of tokens originally matched by _p_ is parsed again using _n_ as the goal symbol. …

> If the sequence of tokens can be parsed as a single instance of _n_, with no tokens left over, then:
>
> We refer to that instance of _n_ (a Parse Node, unique for a given _p_) as "the _n_ that is covered by _p_".

IsInTailPosition:

> 2. If _call_ is not contained within a |FunctionBody|, a |ConciseBody|, or an |AsyncConciseBody|, return *false*.
> 3. Let _body_ be the |FunctionBody|, |ConciseBody|, or |AsyncConciseBody| that most closely contains _call_.

The evaluation of `PrimaryExpression : CoverParenthesizedExpressionAndArrowParameterList`:

> 1. Let _expr_ be the |ParenthesizedExpression| that is covered by |CoverParenthesizedExpressionAndArrowParameterList|.
> 2. Return ? Evaluation of _expr_.

and of `CallExpression : CoverCallExpressionAndAsyncArrowHead`:

> 7. Let _thisCall_ be this |CallExpression|.
> 8. Let _tailCall_ be IsInTailPosition(_thisCall_).

## Problem

Item 2 parses the tokens again with _n_ as the goal symbol, so the covered _n_ is the root of a parse tree of its
own: nothing makes it a child of _p_'s parent. Evaluation runs on the covered node and its descendants, and a query
that walks up the tree from one of them stops at _n_.

In a strict function, `return (f(n - 1));` evaluates the |ParenthesizedExpression| covered by the cover, and the
call's |CallExpression| lies in that separate tree. It is contained within no |FunctionBody|, so IsInTailPosition
returns *false* at step 2 and the call is not a tail call, while `return f(n - 1);` is one. HasCallInTailPosition's
row for the cover recurses into the covered node, which is pointless unless a call there can be in
tail position: the intent is that the parentheses change nothing. Every "contained within", "most closely
contains" and "the parent of" that starts inside a covered node has the same gap.

## Examples

[examples/46-covered-node-tail-call.js](examples/46-covered-node-tail-call.js) (outputs:
[RESULTS.md](examples/RESULTS.md#46-covered-node-tail-calljs)), a strict Script:

```js
"use strict";
function plain(n) { if (n === 0) return "done"; return plain(n - 1); }
function paren(n) { if (n === 0) return "done"; return (paren(n - 1)); }
for (var [name, fn] of [["plain", plain], ["paren", paren]]) {
  try { print(name + ": " + fn(100000)); }
  catch (e) { print(name + ": " + e.constructor.name); }
}
```

| | `plain(100000)` | `paren(100000)` |
|---|---|---|
| literal text | a tail call: `done` | not a tail call: 100000 frames (an engine may run out of stack) |
| JavaScriptCore (proper tail calls) | `done` | `done` |
| V8, SpiderMonkey (no proper tail calls) | `RangeError` / `InternalError` | `RangeError` / `InternalError` |
| formal model, test262 reading (the default) | no result in 120 s | no result in 120 s |
| formal model, literal reading | `stop` (see below) | `stop` |

JavaScriptCore is the only engine of the three with proper tail calls, and it treats both as tail calls. SpecTec bakes in
the test262 reading (`State.covers` in `lean/Ecma/Ops/Parse.lean` and `Model.ParentLaws` in
`spec/spectec/prose/05-model-laws.spectec` splice each covered node's parent to the covering node's parent); it does not
finish 100000 calls within RESULTS.md's 120 s limit, while with 200 calls (`tests/run/erratum_covered_node_parent.js`) it
succeeds in constant stack space.

## Proposed wording

A proposed new item of the definition:

```diff
--- a/spec.html
+++ b/spec.html
@@ -405,6 +405,7 @@
         <li>If the sequence of tokens can be parsed as a single instance of _n_, with no tokens left over, then:
           <ol>
             <li>We refer to that instance of _n_ (a Parse Node, unique for a given _p_) as “the _n_ that is <dfn>covered</dfn> by _p_”.</li>
+            <li>The _n_ that is covered by _p_ takes the place of _p_ in the parse tree: its parent is the parent of _p_, and it and every Parse Node it contains are contained within each Parse Node that contains _p_.</li>
             <li>Early error rules are applied to the _n_ that is covered by _p_ and to its descendants, as modified by further cases of “must cover”.</li>
           </ol>
         </li>
```

## test262

`language/expressions/tco-pos.js` (flags onlyStrict, feature tail-call-optimization) calls
`(function f(n) { … return (f(n - 1)); }($MAX_ITERATIONS))` and requires it to finish: under the literal text the
parenthesized call is not a tail call and the test needs `$MAX_ITERATIONS` frames.
