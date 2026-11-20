// expect: normal: undefined
// print: 1v1,2v2,closed|10,21,32
// Async code on the frame machine (DESIGN §7), past what async_frames.js
// covers: a `for await` whose `break` closes the async iterator
// (AsyncIteratorClose) and whose binding is a pattern, and Array.fromAsync
// over an async iterable with an async mapper.
var log = [];
function source() {
  var i = 0;
  return { [Symbol.asyncIterator]() { return this; },
    next() { i++; return Promise.resolve({ value: [i, "v" + i], done: i > 3 }); },
    return() { log.push("closed"); return Promise.resolve({ done: true }); } };
}
async function firstTwo() {
  var r = [];
  for await (var [n, s = "never"] of source()) { r.push(n + s); if (n == 2) break; }
  return r.join() + "," + log.join();
}
async function* gen() { yield 1; yield 2; yield 3; }
Promise.all([firstTwo(), Array.fromAsync(gen(), async function (x, k) { return x * 10 + k; })])
  .then(function (r) { print(r.join("|")); }, function (e) { print("rejected " + e); });
void 0;
