var o = {b: 1, a: 2, 1: 3}; var ks = []; for (var k in o) ks.push(k); print(ks.join());
print([3,1,2].sort().join(), "abc".toUpperCase(), /a(b+)c/.exec("xabbbc")[1], JSON.stringify({x:[1,"y",null]}));
function* g() { yield 1; yield 2; } print([...g()].join());
class A { #p = 1; get p() { return this.#p; } } print(new A().p);
label: for (var i = 0; i < 3; i++) { for (;;) { continue label; } } print(i);
try { null.x } catch (e) { print(e instanceof TypeError) }
Promise.resolve(7).then(v => print("then", v));
print(eval("1+1"), new Function("a", "return a*2")(21), "\u{1F600}".length, [1,2,3].includes(2));
