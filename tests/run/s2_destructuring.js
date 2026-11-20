// Destructuring (§8.6.2–3, §14.3.3, §13.15.5): object and array binding and
// assignment patterns, holes, defaults, rest elements and properties, nested
// patterns, IteratorClose, for-of heads, and object spread (CopyDataProperties).
// expect: normal: "1|5|4,5|1|3|w,v|7|8|30|5||3|4|1|true|3,7,30|a,b,c"
var log = [];
var [a, , b = 5, ...c] = [1, 2, undefined, 4, 5];
var {x, y: {z = 3} = {}, ...rest} = {x: 1, w: 2, v: 3};
let [[p], {q}] = [[7], {q: 8}];
function f([m, n] = [9, 10], {o} = {o: 11}) { return m + n + o; }
var k, l, mm;
[k, l = function(){}] = [1];
({k, l: mm, ...rest2} = {k: 2, l: 3, extra: 4});
var iterClosed = false;
var it = { [Symbol.iterator]() { return { next() { return {done: false, value: 1}; }, return() { iterClosed = true; return {}; } }; } };
var [first] = it;
for (var [u, v] of [[1, 2], [3, 4]]) log.push(u + v);
for ([k, l] of [[5, 6]]) log.push(k * l);
var obj = {...{a: 1, b: 2}, c: 3};
[a, b, c.join(), x, z, Object.keys(rest).join(), p, q, f(), k, l.name, mm, rest2.extra, first, iterClosed, log.join(), Object.keys(obj).join()].join("|")
