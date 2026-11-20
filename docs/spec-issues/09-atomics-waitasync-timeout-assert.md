# 09. EnqueueAtomicsWaitAsyncTimeoutJob passes a negative delay, and its Assert can fail

- **Location:** §25.4.3.15 EnqueueAtomicsWaitAsyncTimeoutJob (`#sec-enqueueatomicswaitasynctimeoutjob`), steps 4 and
  1.b.ii; §25.4.3.14 DoWait (`#sec-dowait`), steps 22–24; §9.5.6 HostEnqueueTimeoutJob (`#sec-hostenqueuetimeoutjob`).
- **Kind:** a call outside its parameter type (a negative delay), and a failing Assert.
- **Model errata:** `AtomicsWaitAsyncTimeoutNegativeDelay` and `AtomicsWaitAsyncTimeoutAssert`, each default
  reading literal; the readings of each: literal, proposed. Under the literal readings a run stops at step 4 when the
  delay is negative and at step 1.b.ii when the Assert fails; the proposed readings are
  the Proposed wording below: step 4's delay clamped at *+0*𝔽, and the Assert stated for an integral clock.
- **Upstream:** Checked 2026-11-19: none found (searched for "EnqueueAtomicsWaitAsyncTimeoutJob", whose one hit
  renames aliases, and "HostEnqueueTimeoutJob"). The operation came with PR #3049 (merged 2023-06, commit 3330e231b),
  "Normative: Add Atomics.waitAsync".

## Text

DoWait:

> 22. Let _now_ be the time value (UTC) identifying the current time.
> 23. Let _additionalTimeout_ be an implementation-defined non-negative mathematical value.
> 24. Let _timeoutTime_ be ℝ(_now_) + _realTimeout_ + _additionalTimeout_.

EnqueueAtomicsWaitAsyncTimeoutJob:

> 1. Let _timeoutJob_ be a new Job Abstract Closure with no parameters that captures _waiterList_ and _waiterRecord_
>    and performs the following steps when called:
>    …
>    b. If _waiterList_.[[Waiters]] contains _waiterRecord_, then
>       i. Let _timeOfJobExecution_ be the time value (UTC) identifying the current time.
>       ii. Assert: ℝ(_timeOfJobExecution_) ≥ _waiterRecord_.[[TimeoutTime]] (ignoring potential non-monotonicity
>           of time values).
> 2. Let _now_ be the time value (UTC) identifying the current time.
> 3. Let _currentRealm_ be the current Realm Record.
> 4. Perform HostEnqueueTimeoutJob(_timeoutJob_, _currentRealm_, 𝔽(_waiterRecord_.[[TimeoutTime]]) - _now_).

HostEnqueueTimeoutJob takes "_milliseconds_: a non-negative finite Number" and schedules the Job "to be performed
after at least _milliseconds_ milliseconds". A finite time value is "an integral Number representing an instant in
time to millisecond precision" (§21.4.1.1); _realTimeout_ is any non-negative real (DoWait step 11: "max(ℝ(_timeoutNumber_), 0)").

## Problem

1. **A negative delay.** Step 2 reads the clock again, after DoWait step 22's reading from which [[TimeoutTime]] was
   computed. If the clock has advanced by more than _realTimeout_ + _additionalTimeout_ in between, step 4's argument
   is negative, outside HostEnqueueTimeoutJob's parameter type. A fractional timeout makes this ordinary: with
   _additionalTimeout_ = 0, `Atomics.waitAsync(ia, 0, 0, 0.5)` read at _now_ = 1000 has [[TimeoutTime]] 1000.5, and
   if the clock reads 1001 at step 2 the delay is -0.5.
2. **The Assert.** [[TimeoutTime]] is an exact real, but the Job only waits for a Number of milliseconds, and its
   clock reads integral time values. `Atomics.waitAsync(ia, 0, 0, 0.7)` at _now_ = 1000, with _additionalTimeout_ =
   0, has [[TimeoutTime]] 1000.7 and a delay of 0.7 ms; a host whose clock still reads 1000 when the Job runs makes
   1000 ≥ 1000.7 false. 𝔽 also rounds: a timeout of 1e-20 ms gives 𝔽(1000 + 10⁻²⁰) - 1000 = *+0*𝔽, so the Job may
   run at once, below [[TimeoutTime]]; above 2⁵³ 𝔽 may round [[TimeoutTime]] down. The Assert holds only for some
   implementation-defined choices (for example an _additionalTimeout_ that makes _timeoutTime_ an integer below
   2⁵³); an Assert should hold in every conforming execution.

## Examples

[examples/09-atomics-waitasync-timeout-assert.js](examples/09-atomics-waitasync-timeout-assert.js) (outputs:
[RESULTS.md](examples/RESULTS.md#09-atomics-waitasync-timeout-assertjs)):

```js
var ia = new Int32Array(new SharedArrayBuffer(8));
var t0 = Date.now();
var r = Atomics.waitAsync(ia, 0, 0, 0.7);
print(r.async);
r.value.then(function (v) { print(v + ", elapsed ≥ 0: " + (Date.now() - t0 >= 0)); });
if (typeof setTimeout === "function") setTimeout(function () {}, 50);
```

| | output |
|---|---|
| literal text | `true`, then (on a millisecond clock that has not ticked) the Assert of 1.b.ii fails |
| V8, SpiderMonkey (with `-P atomics_wait_async=true`), JavaScriptCore | `true`, `timed-out, elapsed ≥ 0: true` |
| formal model (literal reading) | `true`, `timed-out, elapsed ≥ 0: true` |

Both failures depend on the clock and on implementation-defined choices, so no engine output shows which choice
keeps the text true; the derivation above is the text's. Without `-P atomics_wait_async=true`, `Atomics.waitAsync`
is not a function in the SpiderMonkey 140 shell. The model's test hosts take the Job only once their clock has
reached the Job's due time (§9.5.6's "after at least"), so the literal reading neither stops at step 4 nor reaches a
false Assert here. The Assert is checked, and a run whose host reads a time below [[TimeoutTime]] stops at 1.b.ii,
but that stop is untested end to end. The rounding case above needs a clock that reads the same time at step 2 as
at DoWait step 22; every test host's clock (the default and `--host-seed`) advances at each reading, and timeouts
of 0.7, 10⁻²⁰ and 1 + 10⁻¹⁴ ms time out normally on the default host and seeds 1–3: no host option gives a lawful
run that fails the Assert. A run that failed the Assert on a host that takes the Job early would show that host
breaking §9.5.6's "after at least", not this defect.

## Proposed wording

Clamp the delay at zero, and state the Assert for what step 4 and an integral clock guarantee: the Job runs at
least _delay_ after _now_, so its time value is at least 𝔽([[TimeoutTime]]) rounded down.

```diff
--- a/spec.html
+++ b/spec.html
@@ -47184,7 +47184,7 @@
             1. Perform EnterCriticalSection(_waiterList_).
             1. If _waiterList_.[[Waiters]] contains _waiterRecord_, then
               1. Let _timeOfJobExecution_ be the time value (UTC) identifying the current time.
-              1. Assert: ℝ(_timeOfJobExecution_) ≥ _waiterRecord_.[[TimeoutTime]] (ignoring potential non-monotonicity of time values).
+              1. Assert: _timeOfJobExecution_ ≥ 𝔽(_waiterRecord_.[[TimeoutTime]]) rounded down to an integral Number (ignoring potential non-monotonicity of time values).
               1. Set _waiterRecord_.[[Result]] to *"timed-out"*.
               1. Perform RemoveWaiter(_waiterList_, _waiterRecord_).
               1. Perform NotifyWaiter(_waiterList_, _waiterRecord_).
@@ -47192,7 +47192,9 @@
             1. Return ~unused~.
           1. Let _now_ be the time value (UTC) identifying the current time.
           1. Let _currentRealm_ be the current Realm Record.
-          1. Perform HostEnqueueTimeoutJob(_timeoutJob_, _currentRealm_, 𝔽(_waiterRecord_.[[TimeoutTime]]) - _now_).
+          1. Let _delay_ be 𝔽(_waiterRecord_.[[TimeoutTime]]) - _now_.
+          1. If _delay_ &lt; *+0*<sub>𝔽</sub>, set _delay_ to *+0*<sub>𝔽</sub>.
+          1. Perform HostEnqueueTimeoutJob(_timeoutJob_, _currentRealm_, _delay_).
           1. Return ~unused~.
         </emu-alg>
       </emu-clause>
```

The clamp is applied to the text's own difference, 𝔽([[TimeoutTime]]) - _now_, so that _now_ + _delay_ is
𝔽([[TimeoutTime]]) whenever the delay is positive. Clamping the exact difference instead,
𝔽(max([[TimeoutTime]] - ℝ(_now_), 0)), is not enough for the new Assert: with _now_ = 1000 and [[TimeoutTime]]
= 1001 - 10⁻¹⁴, 𝔽([[TimeoutTime]]) is 1001 but the delay 𝔽(1 - 10⁻¹⁴) is below 1, so a Job may run while the
clock still reads 1000.

An alternative to the new Assert is to round _timeoutTime_ up in DoWait step 24, to the smallest integral Number
≥ ℝ(_now_) + _realTimeout_ + _additionalTimeout_ (or +∞ if there is none), which keeps the Assert as it is.

## test262

No test checks when the timeout Job runs against [[TimeoutTime]], or uses a fractional timeout with a clock read
twice.
