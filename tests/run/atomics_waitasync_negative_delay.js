// EnqueueAtomicsWaitAsyncTimeoutJob step 4 passes 𝔽([[TimeoutTime]]) − now to
// HostEnqueueTimeoutJob, whose milliseconds is "a non-negative finite Number";
// now is read at step 2, after DoWait step 22's reading. On a host whose clock
// advances 5 ms at each reading (`--elapsed 5`, Host.elapsed), DoWait reads 5,
// [[TimeoutTime]] is 6 (5.5 rounded up, Erratum AtomicsWaitAsyncTimeoutAssert)
// and step 2 reads 10: the difference is -4. No test262 test controls the time
// between the readings, so the defect is kept literal (Erratum
// AtomicsWaitAsyncTimeoutNegativeDelay,
// docs/spec-issues/09-atomics-waitasync-timeout-assert.md) and the run stops. Engines clamp the delay at zero.
// needs: --elapsed
// Not run: ecma-run has no option for a clock that advances between DoWait
// step 22's reading and step 2's. Its clocks, the fixed one and the seeded one
// (`--host-seed N`), are functions of the host's log (Ecma/Host/Strategy.lean,
// `clockOf`; Engine/Host/Opts.lean, `seededTime`), and no host call comes
// between the two readings: they are equal, so the difference is never negative.
// The expected line is the form ecma-run prints for an erratum's stop
// (`stop: erratum <Name> <site>`, Engine/Cli/Run.lean), not yet seen on a run.
// args: --elapsed 5
// expect: stop: sortError sec-enqueueatomicswaitasynctimeoutjob#0 4
var ia = new Int32Array(new SharedArrayBuffer(16));
Atomics.waitAsync(ia, 0, 0, 0.5).value.then(function (v) { print(v); });
