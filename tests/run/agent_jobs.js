// $262.agent: an agent's own jobs run in its job loop (a promise job, a promise job of realm null, a timeout
// job, a waitAsync promise's job once main notifies it), and main's timeout job runs while the agent waits for
// messages.
// args: --can-block
// expect: normal: undefined
// print: sync
// print: promise
// print: null realm
// print: timeout
// print: notified 1
// print: async ok
// print: main timeout
$262.agent.start(`
  $262.agent.receiveBroadcast(function (sab) {
    var ia = new Int32Array(sab);
    Promise.resolve().then(function () { $262.agent.report("promise"); });
    Promise.resolve().then().then(function () { $262.agent.report("null realm"); });
    setTimeout(function () { $262.agent.report("timeout"); }, 5);
    Atomics.waitAsync(ia, 0, 0).value.then(function (v) { $262.agent.report("async " + v); });
    $262.agent.report("sync");
  });
`);
var ia = new Int32Array(new SharedArrayBuffer(16));
$262.agent.broadcast(ia.buffer);
function take() {
  var r;
  while ((r = $262.agent.getReport()) === null) $262.agent.sleep(1);
  print(r);
}
take(); take(); take(); take();
print("notified " + Atomics.notify(ia, 0));
take();
setTimeout(function () { print("main timeout"); }, 20);
