// S2 end to end: Array.prototype.push and join on an array literal.
// expect: normal: "1-2-33"
var a = [1, 2]; a.push(3); a.join("-") + a.length
