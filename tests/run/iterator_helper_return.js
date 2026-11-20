// expect: normal: "closed:1,done:true"
// %IteratorHelperPrototype%.return closes the underlying iterator (§27.1.2.1.2).
var closed = 0;
var base = { next: function () { return { value: 1, done: false }; },
             return: function () { closed++; return {}; } };
var helper = Iterator.from(base).map(function (x) { return x; });
helper.next();
var r = helper.return();
"closed:" + closed + ",done:" + r.done
