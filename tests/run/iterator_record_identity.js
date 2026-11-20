// expect: normal: "caught d;return y"
// print: rejected p
// print: no return
// An Iterator Record has identity (refactor R2, DESIGN §16.2): the [[Done]]
// that IteratorStepValue Sets before a throw is the one its callers read.
// Destructuring from an iterator whose next() throws does not call return()
// (BindingInitialization step 3); Promise.all over such an iterator rejects
// without calling return() (step 8.a); Iterator.zip's closure Removes an
// exhausted iterator from the List openIters that [[UnderlyingIterators]]
// also holds, so return() closes only the remaining one.
var log = [];
function mk(name, n, throwAt) {
  var i = 0;
  return {
    [Symbol.iterator]() { return this; },
    next() {
      if (i === throwAt) { i++; throw new Error(name); }
      return i < n ? { value: name + i++, done: false } : { value: undefined, done: true };
    },
    return() { log.push('return ' + name); return {}; }
  };
}
try { var [a, b] = mk('d', 5, 1); } catch (e) { log.push('caught ' + e.message); }
var closed = false;
var p = mk('p', 5, 0);
p.return = function () { closed = true; return {}; };
Promise.all(p).catch(function (e) { print('rejected ' + e.message); print(closed ? 'return' : 'no return'); });
var z = Iterator.zip([mk('x', 1), mk('y', 3)], { mode: 'longest' });
z.next(); z.next(); z.return();
log.join(';')
