// $262.agent (test262's INTERPRETING.md): an agent started by main receives
// main's broadcast, writes to the shared memory with Atomics and reports; main
// reads its report with getReport, interleaving until the agent has reported,
// and sees its write. The agent's $262 has the agent-side members only.
// args: --can-block
// expect: normal: undefined
// print: function undefined
// print: 1 function
// print: 7 42
// print: null
$262.agent.start(`
  $262.agent.receiveBroadcast(function (sab, n) {
    var ia = new Int32Array(sab);
    Atomics.store(ia, 0, 42);
    $262.agent.report(typeof $262.agent.report + " " + typeof $262.agent.start);
    $262.agent.report(n);
    $262.agent.leaving();
  });
`);
var ia = new Int32Array(new SharedArrayBuffer(8));
$262.agent.broadcast(ia.buffer, 7);
var r;
while ((r = $262.agent.getReport()) === null) $262.agent.sleep(1);
print(r);
print($262.agent.receiveBroadcast === undefined ? "1 " + typeof $262.agent.broadcast : "0");
while ((r = $262.agent.getReport()) === null) $262.agent.sleep(1);
print(r + " " + Atomics.load(ia, 0));
print($262.agent.getReport());
