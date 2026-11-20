# 03. A built-in async function's promise fulfils with *undefined*

- **Location:** §10.3.3 BuiltinCallOrConstruct (`#sec-builtincallorconstruct`), step 10.b.iii, with §27.10.5.2
  AsyncBlockStart (`#sec-asyncblockstart`), steps 1.f–1.g.
- **Kind:** contradiction (the literal result is not what the algorithm of an async built-in returns).
- **Model erratum:** `BuiltinReturnCompletion`, default reading test262; its readings: literal, test262, proposed.
  The test262 and proposed readings are the same: step 10.b.iii turns a normal completion into a return completion
  (Proposed wording).
- **Upstream:** Checked 2026-11-19: PR #4074 (open, 2026-11), "Normative: Fix async built-in functions resolving to
  undefined", reports this (with `Array.fromAsync([1, 2, 3])`) and proposes a fix; no issue was found (searched for
  "BuiltinCallOrConstruct"). Step 10, the built-in async path, came with PR #2942 (merged 2025-12, commit 7029ed1b2).

## Text

BuiltinCallOrConstruct, for _func_.[[Async]] *true*:

> 10.b. Let _resultsClosure_ be a new Abstract Closure with no parameters that captures … and performs the following
>   steps when called:
>   i. Let _result_ be the Completion Record that is the result of evaluating _func_ …
>   iii. Return Completion(_result_).
> 10.c. Perform AsyncFunctionStart(_promiseCapability_, _resultsClosure_).

AsyncBlockStart:

> 1.f. If _result_ is a normal completion, then
>    i. Perform ! Call(_promiseCapability_.[[Resolve]], *undefined*, « *undefined* »).
> 1.g. Else if _result_ is a return completion, then
>    i. Perform ! Call(_promiseCapability_.[[Resolve]], *undefined*, « _result_.[[Value]] »).

and §5.2.4.4 Implicit Normal Completion: in a built-in function, "Return _v_" returns NormalCompletion(_v_).

## Problem

Array.fromAsync ends with "Return _array_" (§23.1.2.2, steps 8.d.vii.2 and 9.i of its closure), a normal
completion. Step 10.b.iii returns it unchanged, AsyncBlockStart receives a normal completion, and step 1.f resolves
the promise with *undefined*. So every built-in async function's promise fulfils with *undefined*, whatever its
algorithm returns. For an ECMAScript async function, `return v` evaluates to a return completion, which is why step
1.g exists; the built-in path has nothing that makes one.

The specification's two built-in async functions are Array.fromAsync and AsyncDisposableStack.prototype.disposeAsync.
disposeAsync returns *undefined*, so only Array.fromAsync shows the defect, on every call.

## Examples

[examples/03-builtin-async-return-value.js](examples/03-builtin-async-return-value.js) (outputs:
[RESULTS.md](examples/RESULTS.md#03-builtin-async-return-valuejs)):

```js
Array.fromAsync([1, 2]).then(function (v) {
  print("fromAsync fulfils with " + JSON.stringify(v));
});
```

| | output |
|---|---|
| literal text | `fromAsync fulfils with undefined` |
| V8, SpiderMonkey, JavaScriptCore | `fromAsync fulfils with [1,2]` |
| formal model, literal reading | `fromAsync fulfils with undefined` |
| formal model, test262 reading (default) and proposed reading | `fromAsync fulfils with [1,2]` |

## Proposed wording

```diff
--- a/spec.html
+++ b/spec.html
@@ -14122,6 +14122,7 @@
           1. Let _resultsClosure_ be a new Abstract Closure with no parameters that captures _func_, _thisArg_, _argList_, and _newTarget_ and performs the following steps when called:
             1. Let _result_ be the Completion Record that is <emu-meta effects="user-code">the result of evaluating</emu-meta> _func_ in a manner that conforms to the specification of _func_. If _thisArg_ is ~uninitialized~, the *this* value is uninitialized; else _thisArg_ provides the *this* value. _argList_ provides the named parameters. _newTarget_ provides the NewTarget value.
             1. NOTE: If _func_ is defined in this document, “the specification of _func_” is the behaviour specified for it via algorithm steps or other means.
+            1. If _result_ is a normal completion, return ReturnCompletion(_result_.[[Value]]).
             1. Return Completion(_result_).
           1. Perform AsyncFunctionStart(_promiseCapability_, _resultsClosure_).
           1. Remove _calleeContext_ from the execution context stack and restore _callerContext_ as the running execution context.
```

## test262

The Array.fromAsync tests that read the fulfilment value require the array, e.g.
`built-ins/Array/fromAsync/asyncitems-array-add.js` and `built-ins/Array/fromAsync/asyncitems-arraylike-holes.js`
(each awaits the promise and compares the result with `assert.compareArray`). They fail under the literal text.
