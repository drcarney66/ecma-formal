// for-of over Arrays (§14.7.5, §23.1.5): values in order, holes read as undefined,
// entries/keys iterators, and IteratorClose calls "return" on break but not
// after the iterator is done.
// expect: normal: "6|a,undefined|0:x,1:y|0,1|closed:1"
var sum = 0;
for (var v of [1, 2, 3]) sum += v;
var holes = [];
for (const h of ["a", , ]) holes.push(String(h));
var ents = [];
for (var e of ["x", "y"].entries()) ents.push(e[0] + ":" + e[1]);
var ks = [];
for (let k of ["p", "q"].keys()) ks.push(k);
var closed = 0;
var it = [1, 2, 3][Symbol.iterator]();
it.return = function () { closed++; return {}; };
for (var w of it) break;
var it2 = [1][Symbol.iterator]();
it2.return = function () { closed += 10; return {}; };
for (var w2 of it2) ;
sum + "|" + holes.join() + "|" + ents.join() + "|" + ks.join() + "|closed:" + closed
