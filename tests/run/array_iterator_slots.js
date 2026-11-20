// expect: normal: "true;a;true;"
// Slots are read and Set one field at a time (refactor R16, DESIGN §16.3).
// %ArrayIteratorPrototype%.next: the "length" getter (step 9.a) re-enters
// next() on the same iterator, whose step 10.a Sets [[IteratedArrayLike]] to
// undefined. The outer call's step 11 Sets only [[ArrayLikeNextIndex]], so the
// iterator stays done (the last value is undefined, which join writes as ""); a
// write-back of the slots read at step 3 restored
// [[IteratedArrayLike]] and the next call produced "b".
var obj = { 0: 'a', 1: 'b', 2: 'c' };
var it = Array.prototype.values.call(obj);
var n = 0;
var log = [];
Object.defineProperty(obj, 'length', {
  get() {
    n++;
    var mine = n;
    if (mine === 1) log.push(it.next().done);
    return mine === 2 ? 0 : 3;
  }
});
var r = it.next();
log.push(r.value);
var r2 = it.next();
log.push(r2.done, r2.value);
log.join(';')
