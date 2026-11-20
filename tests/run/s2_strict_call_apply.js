// S2 end to end: Function.prototype.call and apply pass the this value and arguments.
// expect: normal: 66
"use strict"; function f(a, b) { return this.k + a + b; } f.call({k: 1}, 2, 3) + f.apply({k: 10}, [20, 30])
