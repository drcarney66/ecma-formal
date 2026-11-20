// S2 end to end: Object.keys returns an Array in property order.
// expect: normal: "a,b"
Object.keys({a: 1, b: 2}).join()
