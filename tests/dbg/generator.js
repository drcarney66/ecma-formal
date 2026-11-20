function* g() {
  var a = 1;
  yield a;
  a = a + 1;
  yield a;
}
var it = g();
var x = it.next().value;
x = x + it.next().value;
