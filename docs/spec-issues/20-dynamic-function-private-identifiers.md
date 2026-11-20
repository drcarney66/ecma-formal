# 20. `new Function("o", "return o.#f")`: no check of private names in dynamic functions

- **Location:** §20.2.1.1.1 CreateDynamicFunction (`#sec-createdynamicfunction`), steps 18–29; §6.2.5.9
  MakePrivateReference (`#sec-makeprivatereference`), step 2.
- **Kind:** missing step (an early error that no goal of CreateDynamicFunction applies), and a failing Assert.
- **Model erratum:** `CreateDynamicFunctionPrivateIdentifiers`, default reading proposed; its readings: literal,
  test262, proposed (the proposed reading is the Proposed wording; the test262 reading checks the body only).
- **Upstream:** Checked 2026-11-19: none found (searched for "CreateDynamicFunction" with private, no hits, and
  "AllPrivateIdentifiersValid"). PR #1668 (merged 2021-05), which brought private names into the specification, has no
  check of them in CreateDynamicFunction. Issue #3080 (closed, 2023-05), "MakePrivateReference and
  ResolvePrivateIdentifier assert that outer private environment can't be null", asked why MakePrivateReference
  asserts a non-null PrivateEnvironment; the answer there points to AllPrivateIdentifiersValid's early errors, which
  are rules of Scripts, Modules and direct eval.

## Text

AllPrivateIdentifiersValid is applied in three places:

> §16.1.1 (ScriptBody): It is a Syntax Error if AllPrivateIdentifiersValid of |StatementList| with argument « » is
> *false* unless the source text containing |ScriptBody| is eval code that is being processed by a direct eval.
>
> §16.2.1.1 (ModuleBody): It is a Syntax Error if AllPrivateIdentifiersValid of |ModuleItemList| with argument « » is
> *false*.
>
> §19.2.1.4 EvalDeclarationInstantiation: If AllPrivateIdentifiersValid of _body_ with argument _privateIdentifiers_ is
> *false*, throw a *SyntaxError* exception.

CreateDynamicFunction parses with other goals and has no such step:

> 18. Let _params_ be ParseText(_joinedParamsString_, _paramGrammar_).
> 19. If _params_ is a List of errors, throw a *SyntaxError* exception.
> 20. Let _body_ be ParseText(_bodyParseString_, _bodyGrammar_).
> 21. If _body_ is a List of errors, throw a *SyntaxError* exception.
> …
> 24. Let _expr_ be ParseText(_sourceText_, _exprGrammar_).
> 25. If _expr_ is a List of errors, throw a *SyntaxError* exception.
> …
> 28. Let _privateEnv_ be *null*.
> 29. Let _func_ be OrdinaryFunctionCreate(_funcProto_, _sourceText_, _params_, _body_, ~non-lexical-this~,
>     _envRecord_, _privateEnv_).

MakePrivateReference:

> 1. Let _privateEnv_ be the running execution context's PrivateEnvironment.
> 2. Assert: _privateEnv_ is not *null*.

## Problem

The goals of steps 18, 20 and 24 are FormalParameters, FunctionBody and FunctionExpression (or their generator and
async forms). None of their early errors applies AllPrivateIdentifiersValid, so a body or a parameter list that uses
`o.#f` outside any class parses without error, and step 29 creates a function whose [[PrivateEnvironment]] is *null*.
Calling it evaluates `o.#f`, whose MakePrivateReference finds that *null* PrivateEnvironment: the Assert of step 2
fails. The parameters reach it too, through an initializer (`new Function("a = {}.#g", "")`, called with no argument).

## Examples

[examples/20-dynamic-function-private-identifiers.js](examples/20-dynamic-function-private-identifiers.js) (outputs:
[RESULTS.md](examples/RESULTS.md#20-dynamic-function-private-identifiersjs)):

```js
try { new Function("o", "return o.#f"); print("body: no error"); }
catch (e) { print("body: " + e.constructor.name); }
try { new Function("a = {}.#g", ""); print("params: no error"); }
catch (e) { print("params: " + e.constructor.name); }
try { eval("(function (o) { return o.#f; })"); print("eval: no error"); }
catch (e) { print("eval: " + e.constructor.name); }
```

| | body | params | eval |
|---|---|---|---|
| literal text | `no error` (a call fails MakePrivateReference's Assert) | `no error` (likewise) | `SyntaxError` |
| V8, SpiderMonkey, JavaScriptCore | `SyntaxError` | `SyntaxError` | `SyntaxError` |
| formal model, proposed reading (the default) | `SyntaxError` | `SyntaxError` | `SyntaxError` |
| formal model, test262 reading | `SyntaxError` | `no error` | `SyntaxError` |
| formal model, literal reading | `no error` | `no error` | `SyntaxError` |

The model's default reading is the proposed wording, which checks both, as the engines do; its test262 reading
checks the body only, which is what test262 tests. Where a function is created, calling it
(`new Function("o", "return o.#f")({})` under the literal reading, `new Function("a = {}.#g", "")()` under the
literal and test262 readings) stops the model with `stop: sortError sec-resolve-private-identifier#0 1`: the
*null* PrivateEnvironment of MakePrivateReference's step 2 is passed on to ResolvePrivateIdentifier
(`#sec-resolve-private-identifier`), whose parameter is a PrivateEnvironment Record.

## Proposed wording

```diff
--- a/spec.html
+++ b/spec.html
@@ -31525,6 +31525,8 @@
             1. NOTE: If this step is reached, _sourceText_ must have the syntax of _exprGrammar_ (although the reverse implication does not hold). The purpose of the next two steps is to enforce any Early Error rules which apply to _exprGrammar_ directly.
             1. Let _expr_ be ParseText(_sourceText_, _exprGrammar_).
             1. If _expr_ is a List of errors, throw a *SyntaxError* exception.
+            1. If AllPrivateIdentifiersValid of _body_ with argument « » is *false*, throw a *SyntaxError* exception.
+            1. If AllPrivateIdentifiersValid of _params_ with argument « » is *false*, throw a *SyntaxError* exception.
             1. Let _funcProto_ be ? GetPrototypeFromConstructor(_newTarget_, _fallbackProto_).
             1. Let _envRecord_ be _currentRealm_.[[GlobalEnv]].
             1. Let _privateEnv_ be *null*.
```

## test262

`built-ins/Function/private-identifiers-not-empty.js` requires a *SyntaxError* for `new Function("o.#f")`; its `info`
quotes the class fields proposal's steps of CreateDynamicFunction:

<!-- quote: test262, built-ins/Function/private-identifiers-not-empty.js, its info -->
> 30. If AllPrivateIdentifiersValid of body with the argument privateIdentifiers is false, throw a SyntaxError exception.
> 31. If AllPrivateIdentifiersValid of parameters with the argument privateIdentifiers is false, throw a SyntaxError exception.

Under the literal text it fails. `staging/sm/PrivateName/lexical-presence.js` also requires a *SyntaxError* from
`Function(str)` for bodies. No test covers the parameters.
