// A Proxy for a function has [[Call]] and [[Construct]] (ProxyCreate step 5):
// the apply and construct traps get the arguments as an Array; typeof,
// Array.isArray and Function.prototype.toString see through it.
// expect: normal: "function|6|C:5|true|false|true"
function C(x) { this.x = x; }
var p = new Proxy(C, {
  apply: function (t, self, args) { return args[0] + args[1] + args[2]; },
  construct: function (t, args, nt) { return { x: "C:" + args[0] }; }
});
var arr = new Proxy([], {});
typeof p + "|" + p(1, 2, 3) + "|" + new p(5).x + "|" + Array.isArray(arr) + "|" +
  Array.isArray(p) + "|" + (typeof Function.prototype.toString.call(p) === "string")
