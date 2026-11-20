function f(n) {
  if (n === 0) {
    return [1].map(function (x) {
      return o.v + x;
    })[0];
  }
  return f(n - 1);
}
var o = {};
Object.defineProperty(o, "v", { get: function () {
  return 41;
} });
var r = f(2);
function* g() {
  var a = yield 1;
  yield a + 1;
}
var it = g();
it.next();
var s = it.next(r).value;
var e = eval("s + 1");
var m = [5].values().map(function (x) {
  debugger;
  return x + 1;
}).next().value;
