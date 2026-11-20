// `__proto__: v` sets [[Prototype]] (§13.2.5.6 step 7); x is read through it.
// expect: normal: 3
({__proto__: {x: 3}}).x
