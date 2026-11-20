// Loose and strict equality: 1 == "1", 1 !== "1", null == undefined, NaN != NaN.
// expect: normal: true
1 == "1" && 1 !== "1" && null == void 0 && +"x" != +"x"
