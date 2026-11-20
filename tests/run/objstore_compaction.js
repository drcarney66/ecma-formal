// 1,000 creates and deletes on one object (tombstones, then compaction): the
// keys left are in creation order.
// expect: normal: "6|p0,p1,p2,q995,q997,q999|true"
var o = { p0: 0, p1: 1, p2: 2 };
for (var i = 0; i < 1000; i++) {
  o['q' + i] = i;
  if (i % 2 === 0 || i < 995) delete o['q' + i];
}
var ks = Object.keys(o);
ks.length + '|' + ks.join() + '|' + (o.q997 === 997 && !('q996' in o))
