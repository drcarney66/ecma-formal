function f(x) {
  var y = x + 1;
  return y;
}
var r = f(1);
r = f(r);
r = f(r) + 1;
