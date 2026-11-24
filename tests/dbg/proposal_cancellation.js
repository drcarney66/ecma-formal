const ac = new AbortController();
const events = [];
{
  using _scoped = ac.signal.addAbortCallback(() => events.push("disposed-listener"));
}
ac.signal.addAbortCallback(() => events.push("aborted:" + ac.signal.reason));
const sab = new SharedArrayBuffer(4);
const wait = Atomics.waitAsync(new Int32Array(sab), 0, 0, { signal: ac.signal });
ac.abort("timeout");
wait.value.catch((reason) => {
  events.push("waitAsync:" + reason);
  print(events.join(", "));
});
void 0;
