# 13. NewPromiseReactionJob can return a throw completion, and *null*-realm promise Jobs run user code without a specified agent or realm

- **Location:** §9.5 Jobs and Host Operations to Enqueue Jobs (`#sec-jobs`), the list of requirements; §9.5.5
  HostEnqueuePromiseJob (`#sec-hostenqueuepromisejob`), its requirements and note; against §27.5.2.1
  NewPromiseReactionJob (`#sec-newpromisereactionjob`), steps 1.h.i, 1.i and 2–3.
- **Kind:** contradiction (a Job against §9.5's normal-completion requirement, and a *null*-realm Job running user
  species resolving functions against §9.5.5's note and missing target-agent / realm preparation).
- **Model erratum:** `PromiseJobAbruptCompletion`, baked-in SpecTec reading literal for the abrupt-completion check
  (`checked_jobs [@sec-newpromisereactionjob]`, stopping at `sec-jobs -` when a promise Job returns an abrupt
  completion), paired with two non-literal host-layer choices for *null*-realm promise Jobs: `jobAgentOf` and
  `Host.mayRun` (`spec/spectec/prose/14-host-laws-basic.spectec`, `16-host-laws-jobs.spectec`) assign a *null*-realm
  Job to the surrounding agent with per-agent FIFO ordering, and `Engine.Host.prepareJobOn` (`lean/Engine/Host/Strategy.lean`)
  pushes an execution context for the agent's realm even when `_realm_` is *null* so user species resolving functions or
  callable Proxies have a running execution context and current Realm Record.
- **Upstream:** Checked 2026-11-19: none found (searched for "NewPromiseReactionJob" and "HostEnqueuePromiseJob"). PR #2772 (open, a draft,
  2022-05), "Remove Job from Promise Resolve Functions", is about the resolving functions' own Job; issue #2222 (open,
  2020-11), "Promise.prototype.finally should use onFinally's realm for newly creating functions", is about `finally`'s
  functions; PR #1597 (merged 2020-03, commit c59502090) and PR #1984 (merged 2020-08, commit a59a820d3) introduced the
  *null* realm for handler-less reactions and §9.5.5's note.

## Text

§9.5, of the host operations that enqueue Jobs:

> Their implementations must conform to the following requirements: …
> - The Abstract Closure must return a normal completion, implementing its own handling of errors.

NewPromiseReactionJob:

> 1.h. If _handlerResult_ is an abrupt completion, then
>      i. Return ? Call(_promiseCapability_.[[Reject]], *undefined*, « _handlerResult_.[[Value]] »).
> 1.i. Return ? Call(_promiseCapability_.[[Resolve]], *undefined*, « _handlerResult_.[[Value]] »).
> 2. Let _handlerRealm_ be *null*.
> 3. If _reaction_.[[Handler]] is not ~empty~, then …

HostEnqueuePromiseJob (`#sec-hostenqueuepromisejob`) and its note:

> If _realm_ is not *null*, each time _job_ is invoked the implementation must perform implementation-defined steps
> such that execution is prepared to evaluate ECMAScript code at the time of _job_'s invocation.

> … If the handler is *undefined*, _realm_ is *null*. … When the _realm_ is *null*, no user ECMAScript code will
> be evaluated and no new ECMAScript objects (e.g. Error objects) will be created.

## Problem

_promiseCapability_ is the capability of the promise that `then` derived, made by NewPromiseCapability(_C_) for the
species constructor _C_ of the original promise, which the program chooses. Its executor may hand
GetCapabilitiesExecutor resolving functions that are user ECMAScript functions or Proxies, and that throw:

1. **Abrupt Job completion.** Step 1.i (or 1.h.i) returns a throw completion, breaking §9.5's requirement that every
   Job Abstract Closure return a normal completion. Unlike `HostEnqueueFinalizationRegistryCleanupJob` (which catches
   abrupt completions and reports them via host-defined steps), `NewPromiseReactionJob` propagates `?` directly.
2. **User code, realm preparation, and agent ownership when `_realm_` is `*null*`.** When a reaction has no handler
   (`q.then()`), steps 2–3 leave `_handlerRealm_` equal to `*null*`, yet step 1.i still calls `_promiseCapability_.[[Resolve]]`
   — running user code and creating objects (e.g. a callable Proxy's `_argArray_` in the current realm), directly
   contradicting `HostEnqueuePromiseJob`'s note (`test262`'s `deferred-is-resolved-value.js` requires running that
   species resolve function). Moreover, `HostEnqueuePromiseJob` omits execution-context preparation when `_realm_` is
   `*null*` and never specifies which agent owns a `*null*`-realm Job or whether FIFO ordering is per-agent.

## Examples

[examples/13-promise-job-abrupt-completion.js](examples/13-promise-job-abrupt-completion.js) (outputs:
[RESULTS.md](examples/RESULTS.md#13-promise-job-abrupt-completionjs)):

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
| formal model (literal reading) | stops at the Job's completion, `stop: assertFailed sec-jobs -`; exit status 3 |
| formal model (proposed reading) | runs to completion: `handler 1`, `resolve(1) called; it throws`, `resolve(2) called; it throws`, `a later Job runs`; exit status 0 |

All three engines run every later Job. Their hosts disagree on what follows the throw: Node.js ignores it; the
SpiderMonkey shell and Bun report each one, go on, and end with a non-zero exit status.

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
Job result; and in §9.5.5 `HostEnqueuePromiseJob`, specify that a `*null*`-realm Job runs in the surrounding agent
(with per-agent FIFO order) and update the note to acknowledge user species resolving functions.

## test262

No test makes a reaction Job's resolving function throw: the
`built-ins/Promise/{all,allKeyed,allSettled,allSettledKeyed,any}/capability-resolve-throws-*.js` tests make the
combinator's own capability throw, not the capability of a promise that `then` derived. A test could not observe the
difference anyway: what the host does with the completion is host-defined either way.
