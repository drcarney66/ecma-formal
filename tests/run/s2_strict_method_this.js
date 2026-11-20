// S2 end to end: methods and getters of an object literal see the object as this.
// expect: normal: 12
"use strict"; var o = { n: 4, m() { return this.n; }, get v() { return this.n * 2; } }; o.m() + o.v
