// expect: normal: "0"
// print: 0,1,2,3,4
// print: b,c,a,d
// Promise jobs run in FIFO order after the Script (§9.5, §27.5.2); resolving
// with a promise takes two more jobs (NewPromiseResolveThenableJob, then the
// reaction that resolves).
var log = [];
Promise.resolve().then(function () { log.push(1); }).then(function () { log.push(3); });
Promise.resolve().then(function () { log.push(2); }).then(function () { log.push(4); print(log.join(",")); });
var order = [];
var p = Promise.resolve(1);
new Promise(function (r) { r(p); }).then(function () { order.push("a"); });
p.then(function () { order.push("b"); }).then(function () { order.push("c"); })
  .then(function () { order.push("d"); print(order.join(",")); });
log.push(0);
log.join(",")
