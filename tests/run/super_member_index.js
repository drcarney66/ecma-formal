// A computed super property (§13.3.7.1, `super[Expression]`): read, called
// and assigned, in methods of a derived class.
// expect: normal: "A.m!,7,8,true"
class A {
  m() { return "A.m"; }
  get g() { return 7; }
}
class B extends A {
  m() { var k = "m"; return super[k]() + "!"; }
  h() { return super["g"]; }
  s() { super["x"] = 8; return this.x; }
}
var b = new B();
[b.m(), b.h(), b.s(), Object.prototype.hasOwnProperty.call(b, "x")].join(",");
