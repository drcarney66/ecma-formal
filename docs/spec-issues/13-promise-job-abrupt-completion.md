# 13. NewPromiseReactionJob returns the throw completion of a resolving function

- **Location:** §9.5 Jobs and Host Operations to Enqueue Jobs (`#sec-jobs`), the list of requirements, against
  §27.5.2.1 NewPromiseReactionJob (`#sec-newpromisereactionjob`), steps 1.h.i and 1.i.
- **Kind:** contradiction (a Job against §9.5's requirement on Jobs).
- **Model erratum:** `PromiseJobAbruptCompletion`, default reading literal; its readings: literal, proposed (the
  proposed reading is the proposed wording below, with a host operation, HostReportErrors, in place of "any
  host-defined steps for reporting the error"); the literal reading stops at §9.5's requirement when the Job returns
  an abrupt completion.
- **Upstream:** Checked 2026-11-19: none found (searched for "NewPromiseReactionJob"). PR #2772 (open, a draft,
  2022-05), "Remove Job from Promise Resolve Functions", is about the resolving functions' own Job.

## Text

§9.5, of the host operations that enqueue Jobs:

> Their implementations must conform to the following requirements: …
> - The Abstract Closure must return a normal completion, implementing its own handling of errors.

NewPromiseReactionJob:

> 1.h. If _handlerResult_ is an abrupt completion, then
>      i. Return ? Call(_promiseCapability_.[[Reject]], *undefined*, « _handlerResult_.[[Value]] »).
> 1.i. Return ? Call(_promiseCapability_.[[Resolve]], *undefined*, « _handlerResult_.[[Value]] »).

## Problem

_promiseCapability_ is the capability of the promise that `then` derived, made by NewPromiseCapability(_C_) for the
species constructor _C_ of the original promise, which the program chooses. Its executor may hand
GetCapabilitiesExecutor resolving functions that throw. Step 1.i (or 1.h.i) then returns a throw completion, and the
Job breaks §9.5's requirement. §9.5 says nothing of what follows: the hosts' steps that run Jobs are not told of the
completion. The other Jobs handle their errors as §9.5 asks: §9.9.4.1 HostEnqueueFinalizationRegistryCleanupJob's
_cleanupJob_ (step 2: "If _cleanupResult_ is an abrupt completion, perform any host-defined steps for reporting the
error"), and NewPromiseResolveThenableJob, whose resolving functions are the built-in ones that do not throw.

## Examples

[examples/13-promise-job-abrupt-completion.js](examples/13-promise-job-abrupt-completion.js) (outputs:
[RESULTS.md](examples/RESULTS.md#13-promise-job-abrupt-completionjs)); its `q.then()` lines are the case of
[47](47-promise-job-null-realm-code.md):

```js
function Bad(executor) {
  executor(function (v) { print("resolve(" + v + ") called; it throws"); throw new Error("boom"); },
           function () {});
}
Bad[Symbol.species] = Bad;
var p = Promise.resolve(1);
p.constructor = Bad;
p.then(function (v) { print("handler " + v); return v; });
var q = Promise.resolve(2);
q.constructor = Bad;
q.then();   // no handler: the Job's realm is null
Promise.resolve(3).then(function () { print("a later Job runs"); });
```

| | output |
|---|---|
| literal text | `handler 1`, `resolve(1) called; it throws`, then the Job returns a throw completion, which §9.5 forbids |
| V8 (Node.js) | `handler 1`, `resolve(1) called; it throws`, `resolve(2) called; it throws`, `a later Job runs`; exit status 0, nothing reported |
| SpiderMonkey (js140) | the same lines, each throw reported on stderr (`Error: boom`); exit status 3 |
| JavaScriptCore (Bun) | the same lines, each throw reported (`error: boom`); exit status 1 |
| formal model (literal reading) | stops at the Job's completion, `stop: erratum PromiseJobAbruptCompletion sec-jobs -`; exit status 3 (a run that stops reports only the stop) |
| formal model (proposed reading) | runs to completion: `handler 1`, `resolve(1) called; it throws`, `resolve(2) called; it throws`, `a later Job runs`; exit status 0 |

All three engines run every later Job. Their hosts disagree on what follows the throw: Node.js ignores it; the
SpiderMonkey shell and Bun report each one, go on, and end with a non-zero exit status. The text gives them nothing
to agree on.

## Proposed wording

Proposed: let the Job handle the error itself, as HostEnqueueFinalizationRegistryCleanupJob's Job does:

```diff
--- a/spec.html
+++ b/spec.html
@@ -50686,8 +50686,11 @@
               1. Return ~empty~.
             1. Assert: _promiseCapability_ is a PromiseCapability Record.
             1. If _handlerResult_ is an abrupt completion, then
-              1. Return ? Call(_promiseCapability_.[[Reject]], *undefined*, « _handlerResult_.[[Value]] »).
-            1. Return ? Call(_promiseCapability_.[[Resolve]], *undefined*, « _handlerResult_.[[Value]] »).
+              1. Let _settleResult_ be Completion(Call(_promiseCapability_.[[Reject]], *undefined*, « _handlerResult_.[[Value]] »)).
+            1. Else,
+              1. Let _settleResult_ be Completion(Call(_promiseCapability_.[[Resolve]], *undefined*, « _handlerResult_.[[Value]] »)).
+            1. If _settleResult_ is an abrupt completion, perform any host-defined steps for reporting the error.
+            1. Return ~empty~.
           1. Let _handlerRealm_ be *null*.
           1. If _reaction_.[[Handler]] is not ~empty~, then
             1. Let _getHandlerRealmResult_ be Completion(GetFunctionRealm(_reaction_.[[Handler]].[[Callback]])).
```

The alternative, also proposed, is to drop the requirement for promise Jobs and say that the host reports an abrupt
Job result. Either way the host decides where the error goes, which is also what a *null*-realm Job needs (see
[47](47-promise-job-null-realm-code.md)).

## test262

No test makes a reaction Job's resolving function throw: the
`built-ins/Promise/{all,allKeyed,allSettled,allSettledKeyed,any}/capability-resolve-throws-*.js` tests make the
combinator's own capability throw, not the capability of a promise that `then` derived. A test could not observe the
difference anyway: what the host does with the completion is host-defined either way.
