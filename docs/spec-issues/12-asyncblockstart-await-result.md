# 12. AsyncBlockStart asserts ~unused~, but Await resumes it with ~empty~

- **Location:** §27.10.5.2 AsyncBlockStart (`#sec-asyncblockstart`), steps 3–4, against §27.10.5.3 Await (`#await`),
  step 8, and §9.4.8 RunCallerContext (`#sec-runcallercontext`), step 4; §9.4.7 RunSuspendedContext
  (`#sec-runsuspendedcontext`), its return type.
- **Kind:** failing Assert (in every async function that awaits).
- **Model erratum:** `AsyncBlockStartAwaitResult`, default reading test262; its readings: literal, test262, proposed
  (the test262 and proposed readings are one: the Assert of Proposed wording); the literal reading stops at
  AsyncBlockStart step 4.
- **Upstream:** Checked 2026-11-19: issue #3435 (open, 2024-10), "editorial: mismatch between `Await`
  transfer-of-control and `AsyncBlockStart`", reports it, against the text before RunCallerContext; it has no
  comments. RunCallerContext came with PR #3846 (merged 2026-06, commit 45a667175). PR #4018 (closed without merging,
  2026-10), "Editorial: align async block assertions with Await suspension", proposed letting the Assert accept
  ~empty~. PR #3604 (open, 2025-05) rewords step 1.d only.

## Text

AsyncBlockStart:

> 1. Let _closure_ be a new Abstract Closure with no parameters that captures _promiseCapability_ and _asyncBody_
>    and performs the following steps when called:
>    …
>    j. Resume _callerContext_, passing NormalCompletion(~unused~).
> 2. Set the code evaluation state of _asyncContext_ such that …
> 3. Let _result_ be ! RunSuspendedContext(_asyncContext_, NormalCompletion(~empty~)).
> 4. Assert: _result_ is ~unused~.
> 5. NOTE: The possible sources of _result_ values are Await or, if the async function doesn't await anything, step
>    … above.

Await:

> 8. Return ? RunCallerContext(~empty~).

RunCallerContext (_value_: an ECMAScript language value or ~empty~):

> 4. Resume _callerContext_, passing NormalCompletion(_value_).

Step 5's "step … above" is step 1.j. RunSuspendedContext returns "either a normal completion containing either an
ECMAScript language value or ~unused~, or an abrupt completion".

## Problem

The first `await` in an async function body runs Await step 8, which resumes the caller context with
NormalCompletion(~empty~). That caller is AsyncBlockStart step 3, so _result_ is ~empty~ and step 4's Assert fails.
Every async function or module body that awaits before it returns reaches it. The same ~empty~ is also outside
RunSuspendedContext's return type, here and in §27.9.3.6 AsyncGeneratorResume step 4 (an async generator that
awaits).

The two sides can be made to agree in two ways. Await could pass ~unused~, but RunCallerContext's _value_ parameter
is "an ECMAScript language value or ~empty~", and Await is its only caller that passes a value that is not a language
value, so that parameter would change too. Or AsyncBlockStart could accept ~empty~, which needs only its Assert and
RunSuspendedContext's return type, which an async generator's `await` also reaches (AsyncGeneratorResume step 4).
The proposed wording below is the second; the model's test262 reading runs under its Assert.

## Examples

[examples/12-asyncblockstart-await-result.js](examples/12-asyncblockstart-await-result.js) (outputs:
[RESULTS.md](examples/RESULTS.md#12-asyncblockstart-await-resultjs)):

```js
async function f() { await 1; return 2; }
f().then(function (v) { print("f fulfilled with " + v); });
```

| | output |
|---|---|
| literal text | the Assert of AsyncBlockStart step 4 fails at `await 1` |
| V8, SpiderMonkey, JavaScriptCore | `f fulfilled with 2` |
| formal model (literal reading) | stops at AsyncBlockStart step 4 (`stop: erratum AsyncBlockStartAwaitResult sec-asyncblockstart#0 4`) |
| formal model (test262 and proposed readings) | `f fulfilled with 2` |

## Proposed wording

```diff
--- a/spec.html
+++ b/spec.html
@@ -12098,7 +12098,7 @@
         RunSuspendedContext (
           _context_: an execution context,
           _completionRecord_: a Completion Record,
-        ): either a normal completion containing either an ECMAScript language value or ~unused~, or an abrupt completion
+        ): either a normal completion containing one of an ECMAScript language value, ~unused~, or ~empty~, or an abrupt completion
       </h1>
       <dl class="header">
         <dt>description</dt>
@@ -52418,8 +52418,8 @@
             1. Assert: This step is never reached.
           1. Set the code evaluation state of _asyncContext_ such that when evaluation is resumed for that execution context, _closure_ will be called with no arguments.
           1. Let _result_ be ! RunSuspendedContext(_asyncContext_, NormalCompletion(~empty~)).
-          1. Assert: _result_ is ~unused~.
-          1. NOTE: The possible sources of _result_ values are Await or, if the async function doesn't await anything, step <emu-xref href="#step-asyncblockstart-return-undefined"></emu-xref> above.
+          1. Assert: _result_ is either ~unused~ or ~empty~.
+          1. NOTE: The possible sources of _result_ values are Await, which passes ~empty~, or, if the async function doesn't await anything, step <emu-xref href="#step-asyncblockstart-return-undefined"></emu-xref> above, which passes ~unused~.
           1. Return ~unused~.
         </emu-alg>
       </emu-clause>
```

## test262

Every test of an async function that awaits reaches the Assert; an Assert has no observable effect, so none fails.
