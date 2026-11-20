async function h() {
  var a = 1;
  await a;
  a = a + 1;
  return a;
}
var p = h();
p.then(function (v) { print(v); });
var z = 3;
