// A computed ["__proto__"] defines an own property instead (§13.2.5.6 step 4).
// expect: normal: 3
({["__proto__"]: {x: 3}}).__proto__.x
