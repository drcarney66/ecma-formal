// Classes (§15.7): methods, accessors, static members, fields, private names,
// static blocks, derived classes with super, default constructors, class
// expressions and their names, and extending a built-in constructor.
// expect: normal: "3,4,6,B>A.m,5,true,true,function,A,2,true|3,true,false|1,2,5,10,2|1,2,B>A.m|F,,class Z { }|true,true"
class A {
  constructor(x) { this.x = x; }
  get double() { return this.x * 2; }
  static make(v) { return new A(v); }
  m() { return "A.m"; }
}
class B extends A {
  constructor(x, y) { super(x); this.y = y; }
  m() { return "B>" + super.m(); }
}
var b = new B(3, 4);
var r1 = [b.x, b.y, b.double, b.m(), A.make(5).x, b instanceof A, Object.getPrototypeOf(B) === A, typeof A, A.name, B.length];
try { A(); } catch (e) { r1.push(e instanceof TypeError); }
class C { #p = 1; static #s = 2; #m() { return this.#p; } get p() { return this.#m() + C.#s; } static has(o) { return #p in o; } }
var r2 = [new C().p, C.has(new C()), C.has({})];
class D { x = 1; y = this.x + 1; static z = 5; static { D.w = D.z * 2; } f = () => this.y; }
var d = new D();
var r3 = [d.x, d.y, D.z, D.w, d.f()];
class E extends B {}
var e = new E(1, 2);
var r4 = [e.x, e.y, e.m()];
var F = class { static n() { return F.name; } };
var r5 = [F.n(), (class {}).name, String(class Z { })];
class MyArray extends Array {}
var ma = new MyArray();
ma.push(1);
var r6 = [ma instanceof Array, Array.isArray(ma)];
[r1, r2, r3, r4, r5, r6].map(function (x) { return x.join(); }).join("|")
