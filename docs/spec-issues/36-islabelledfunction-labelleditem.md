# 36. IsLabelledFunction tests a |Statement| node for being a |LabelledStatement|: always *false*

- **Location:** §14.13.2 Static Semantics: IsLabelledFunction (`#sec-islabelledfunction`), steps 1–2, with its callers
  in §14.6.1 (`if`, `#sec-if-statement-static-semantics-early-errors`), §14.7.2.1, §14.7.3.1, §14.7.4.1 and §14.7.5.1
  (the iteration statements) and §14.11.1 (`with`), §14.13.1's early error for `LabelledItem : FunctionDeclaration`
  (`#sec-labelled-statements-static-semantics-early-errors`), §5.1.2 Parsing (`#sec-parsing`) and §5.2.3
  Syntax-Directed Operations (`#sec-algorithm-conventions-syntax-directed-operations`), its chain-production rule.
- **Kind:** notation (the steps name a child the node does not have); observable on hosts with §B.3.1 Labelled
  Function Declarations, in non-strict code.
- **Model erratum:** `UnitChainChild`, default reading test262; its readings: literal, test262, proposed. The model
  reads "_n_ is a |X|" through the chain of unit productions, so its literal reading passes step 1 and stops at step 2,
  where _n_'s production has no |LabelledItem|; the test262 and proposed readings take "the |X| of _n_" from the first
  node of _n_'s chain of unit productions whose production has one.
- **Upstream:** Checked 2026-11-19: none found (searched for "IsLabelledFunction", whose one hit is a Temporal pull
  request). Issue #1811 (closed, 2019-12), "Chain production definition", is about the term.

## Text

> Static Semantics: IsLabelledFunction ( _stmt_: a |Statement| Parse Node, ): a Boolean
>
> 1. If _stmt_ is not a |LabelledStatement|, return *false*.
> 2. Let _item_ be the |LabelledItem| of _stmt_.
> 3. If _item_ is `LabelledItem : FunctionDeclaration`, return *true*.
> 4. Let _subStmt_ be the |Statement| of _item_.
> 5. Return IsLabelledFunction(_subStmt_).

A caller (§14.6.1; the others have the same form):

> It is a Syntax Error if IsLabelledFunction(the first |Statement|) is *true*.
>
> It is only necessary to apply this rule if the extension specified in … is implemented.

(the reference is to §B.3.1). §14.13.1:

> LabelledItem : FunctionDeclaration
> - It is a Syntax Error if any source text is matched by this production, unless that source text is non-strict
>   code and the host is a web browser or otherwise supports …

(the reference is to §B.3.1 Labelled Function Declarations).

§5.1.2: "When a Parse Node is an instance of a nonterminal, it is also an instance of some production that has
that nonterminal as its left-hand side. Moreover, it has zero or more children, one for each symbol on the
production's right-hand side".

## Problem

Every caller passes a |Statement| node. For a labelled statement that node is an instance of `Statement :
LabelledStatement`: it is not an instance of |LabelledStatement|, and its only child is the |LabelledStatement|
node, so its |LabelledItem| is a grandchild. Read by §5.1.2, step 1 returns *false* for every argument and step 2
names no child. §5.2.3's implicit definitions for chain productions do not help: they cover syntax-directed
operations, and IsLabelledFunction is an abstract operation that inspects a node. Step 4's _subStmt_ is again a
|Statement| node, so the recursion has the same gap.

Without §B.3.1 this is invisible: §14.13.1 rejects every labelled function declaration, inside an `if` or not.
With §B.3.1 (web browsers, non-strict code), `l: function h() {}` is allowed and the IsLabelledFunction rules are
what reject `if (1) l: function f() {}`; read literally they never apply, and the `if` body is a labelled
function declaration.

## Examples

[examples/36-islabelledfunction-labelleditem.js](examples/36-islabelledfunction-labelleditem.js) (outputs:
[RESULTS.md](examples/RESULTS.md#36-islabelledfunction-labelleditemjs)), each source parsed as a non-strict Script:

```js
var sources = ["if (1) l: function f() {}", "while (0) l: function f() {}",
               "if (0) ; else a: b: function g() {}", "while (0) l: m: x;", "l: function h() {}"];
for (var s of sources) {
  try { (0, eval)(s); print(s + ": no error"); }
  catch (e) { print(s + ": " + e.constructor.name); }
}
```

| | `if (1) l: function f() {}` | `while (0) l: function f() {}` | `if (0) ; else a: b: function g() {}` | `while (0) l: m: x;` | `l: function h() {}` |
|---|---|---|---|---|---|
| literal text, host with §B.3.1 | no error | no error | no error | no error | no error |
| V8, SpiderMonkey, JavaScriptCore | SyntaxError | SyntaxError | SyntaxError | no error | no error |
| formal model, web-browser host (`ecma-run --web-browser`), test262 and proposed readings | SyntaxError | SyntaxError | SyntaxError | no error | no error |
| formal model, its default host (no §B.3.1), test262 and proposed readings | SyntaxError | SyntaxError | SyntaxError | no error | SyntaxError |

The engines implement §B.3.1 and agree with the intended reading, as does the model on its web-browser host, where
§14.13.1 does not reject `l: function h() {}` and the first three SyntaxErrors come from IsLabelledFunction. The
model's default host does not implement §B.3.1, so there the SyntaxErrors come from §14.13.1 and witness nothing
about IsLabelledFunction. On either host the model's literal reading stops at IsLabelledFunction step 2 on the first
source.

## Proposed wording

```diff
--- a/spec.html
+++ b/spec.html
@@ -23309,8 +23309,9 @@
       <dl class="header">
       </dl>
       <emu-alg>
-        1. If _stmt_ is not a |LabelledStatement|, return *false*.
-        1. Let _item_ be the |LabelledItem| of _stmt_.
+        1. If _stmt_ is not an instance of the production <emu-grammar>Statement : LabelledStatement</emu-grammar>, return *false*.
+        1. Let _labelled_ be the |LabelledStatement| of _stmt_.
+        1. Let _item_ be the |LabelledItem| of _labelled_.
         1. If _item_ is <emu-grammar>LabelledItem : FunctionDeclaration</emu-grammar>, return *true*.
         1. Let _subStmt_ be the |Statement| of _item_.
         1. Return IsLabelledFunction(_subStmt_).
```

The other repair is a general rule in §5.1.2 that "_n_ is a |X|" and "the |X| of _n_" see through chain
productions, which other algorithms may already assume; the model reads all "the |X| of _n_" sites that way.

## test262

`language/statements/{if,while,do-while,for,for-in,for-of,with}/labelled-fn-stmt*.js` (18 files) require the
SyntaxError. The `info` of four of them (the three `if` tests and `with/labelled-fn-stmt.js`) notes that in the
absence of the Annex B extension (B.3.2 in their numbering, §B.3.1 today) the labelled function declaration itself is
the error, so on a host without §B.3.1 they pass under the literal text too; on a host with it they need the
proposed wording.
