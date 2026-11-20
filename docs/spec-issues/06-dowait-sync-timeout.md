# 06. A synchronous Atomics.wait that times out returns *"ok"*

- **Location:** §25.4.3.14 DoWait (`#sec-dowait`), steps 26–31, with §25.4.3.11 SuspendThisAgent
  (`#sec-suspendthisagent`), steps 7–9, and §25.4.3.8 AddWaiter (`#sec-addwaiter`), step 2.
- **Kind:** contradiction, and a later failing Assert.
- **Model erratum:** `DoWaitSyncTimeout`, default reading test262; its readings: literal, test262, proposed. The
  test262 and proposed readings add, after step 28.a, the steps of Proposed wording (the proposed reading with its
  NOTE).
- **Upstream:** Checked 2026-11-19: none found (searched for "DoWait"). Issue #3328 (open, 2024-05), "Typo in step 7
  of the SuspendThisAgent abstract operation", is about another error in SuspendThisAgent step 7.

## Text

DoWait:

> 26. Let _waiterRecord_ be a new Waiter Record { [[AgentSignifier]]: _thisAgent_, [[PromiseCapability]]:
>     _promiseCapability_, [[TimeoutTime]]: _timeoutTime_, [[Result]]: *"ok"* }.
> 27. Perform AddWaiter(_waiterList_, _waiterRecord_).
> 28. If _mode_ is ~sync~, then
>     a. Perform SuspendThisAgent(_waiterList_, _waiterRecord_).
> …
> 30. Perform LeaveCriticalSection(_waiterList_).
> 31. If _mode_ is ~sync~, return _waiterRecord_.[[Result]].

SuspendThisAgent:

> 7. Perform LeaveCriticalSection(_waiterList_) and suspend the surrounding agent until the time is
>    _waiterRecord_.[[TimeoutTime]], … The surrounding agent can only wake from suspension due to a timeout or due to
>    another agent calling NotifyWaiter …
> 8. Perform EnterCriticalSection(_waiterList_).
> 9. Return ~unused~.

## Problem

For a ~sync~ wait, [[Result]] is written only at step 26, as *"ok"*. The other places that produce *"timed-out"* are
for ~async~ waits (DoWait step 20.d and EnqueueAtomicsWaitAsyncTimeoutJob step 1.b.iii). SuspendThisAgent neither removes the
waiter nor changes its [[Result]]; only Atomics.notify's RemoveWaiters removes a waiter. So a synchronous wait that
times out:

1. returns *"ok"* at step 31, although Atomics.wait is described as "returning a String differentiating those cases"
   (notified or timed out, §25.4.15), and a Waiter Record's [[Result]], *"ok"* or *"timed-out"*, is "The return
   value of the call" (§25.4.1);
2. leaves its Waiter Record in the WaiterList. A second Atomics.wait by the same agent on the same location then
   fails AddWaiter's step 2, "Assert: There is no Waiter Record in _waiterList_.[[Waiters]] whose
   [[PromiseCapability]] field is _waiterRecord_.[[PromiseCapability]] and whose [[AgentSignifier]] field is
   _waiterRecord_.[[AgentSignifier]]", and a later Atomics.notify counts the stale record and wakes an agent that is
   not suspended.

## Examples

[examples/06-dowait-sync-timeout.js](examples/06-dowait-sync-timeout.js) (outputs:
[RESULTS.md](examples/RESULTS.md#06-dowait-sync-timeoutjs)):

```js
var ia = new Int32Array(new SharedArrayBuffer(4));
print(Atomics.wait(ia, 0, 0, 0));
print(Atomics.wait(ia, 0, 0, 1));
print(Atomics.notify(ia, 0));
```

| | output |
|---|---|
| literal text | `ok`, then the second wait fails AddWaiter step 2's Assert (`stops="sec-addwaiter@2"`) |
| V8, SpiderMonkey, JavaScriptCore | `timed-out`, `timed-out`, `0` |
| formal model, `ecma-run --can-block`, literal reading | stops at AddWaiter step 2's Assert (`stop: erratum DoWaitSyncTimeout sec-addwaiter 2`) |
| formal model, `ecma-run --can-block`, test262 reading (default) and proposed reading | `timed-out`, `timed-out`, `0` |

The engines' main threads can block (the Node.js and Bun hosts and the SpiderMonkey shell allow it). The model's
host agent can block only under `--can-block`: without it, DoWait step 12 throws a *TypeError* before any wait
(`throw: TypeError`, under every reading).

## Proposed wording

Proposed: do what EnqueueAtomicsWaitAsyncTimeoutJob steps 1.b.iii–iv do for an asynchronous waiter:

```diff
--- a/spec.html
+++ b/spec.html
@@ -47157,6 +47157,10 @@
           1. Perform AddWaiter(_waiterList_, _waiterRecord_).
           1. If _mode_ is ~sync~, then
             1. Perform SuspendThisAgent(_waiterList_, _waiterRecord_).
+            1. If _waiterList_.[[Waiters]] contains _waiterRecord_, then
+              1. NOTE: The agent woke because of the timeout: NotifyWaiter is performed only on a Waiter Record that RemoveWaiters has removed.
+              1. Set _waiterRecord_.[[Result]] to *"timed-out"*.
+              1. Perform RemoveWaiter(_waiterList_, _waiterRecord_).
           1. Else if _timeoutTime_ is finite, then
             1. Perform EnqueueAtomicsWaitAsyncTimeoutJob(_waiterList_, _waiterRecord_).
           1. Perform LeaveCriticalSection(_waiterList_).
```

## test262

`built-ins/Atomics/wait/false-for-timeout.js` (three timed-out waits on one location, each *"timed-out"*) and
`built-ins/Atomics/wait/negative-timeout.js` require *"timed-out"*. Both fail under the literal text.
