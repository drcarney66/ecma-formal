// $262.agent: an agent waits on shared memory (Atomics.wait, SuspendThisAgent)
// until main notifies it; main first sleeps until the agent is waiting
// (waitUntil's pattern), and monotonicNow does not go back.
// args: --can-block
// expect: normal: undefined
// print: 1
// print: ok true
$262.agent.start(`
  $262.agent.receiveBroadcast(function (sab) {
    var ia = new Int32Array(sab);
    Atomics.add(ia, 1, 1);
    $262.agent.report(Atomics.wait(ia, 0, 0, 10000));
    $262.agent.leaving();
  });
`);
var ia = new Int32Array(new SharedArrayBuffer(8));
$262.agent.broadcast(ia.buffer);
var t0 = $262.agent.monotonicNow();
while (Atomics.load(ia, 1) !== 1) $262.agent.sleep(1);
$262.agent.sleep(10);
print(Atomics.notify(ia, 0));
var r;
while ((r = $262.agent.getReport()) === null) $262.agent.sleep(1);
print(r + " " + ($262.agent.monotonicNow() >= t0));
