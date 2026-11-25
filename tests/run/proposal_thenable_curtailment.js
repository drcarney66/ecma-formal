// expect: normal: [object #N]
// print: 1,3,2,4,42,rejected:boom,self-typeerror

async function main() {
  const events = [];

  // 1. Thenable resolution via PerformPromiseResolution + PerformPromiseResolveThenable
  const thenable = {
    then(resolve) {
      events.push(2);
      resolve(42);
    }
  };
  events.push(1);
  const p = Promise.resolve(thenable);
  events.push(3);
  Promise.resolve().then(() => events.push(4));
  const v = await p;
  events.push(v);

  // 2. Throwing `.then` getter rejects cleanly
  const badGetter = Object.defineProperty({}, "then", {
    get() { throw "boom"; }
  });
  try {
    await Promise.resolve(badGetter);
  } catch (e) {
    events.push("rejected:" + e);
  }

  // 3. Self-resolution rejects with TypeError
  let resolveSelf;
  const selfP = new Promise((r) => { resolveSelf = r; });
  resolveSelf(selfP);
  try {
    await selfP;
  } catch (e) {
    if (e instanceof TypeError) events.push("self-typeerror");
  }

  print(events.join(","));
}
main();
