// expect: normal: "ok"
// ConstructorMethod and NonConstructorElements (§15.7.3, §15.7.5) are computed
// in Lean from ClassBody's ClassElementList: a non-static method whose PropName
// is "constructor" (an IdentifierName or a StringLiteral) is the constructor; a
// computed ['constructor'] or a static one is an ordinary element.
class A { 'constructor'() { this.a = 1; } m() { return 2; } }
class B { ['constructor']() { return 3; } }
class C { static constructor() { return 4; } constructor() { this.c = 5; } }
class D { m() {} ; ; }
var b = new B();
var results = [
  new A().a === 1 && new A().m() === 2,
  A.prototype.constructor === A,
  Object.getOwnPropertyNames(A.prototype).join() === "constructor,m",
  b.constructor === B.prototype.constructor && Object.getPrototypeOf(b) === B.prototype,
  B.prototype.hasOwnProperty("constructor") && B.prototype.constructor() === 3,
  C.constructor() === 4 && new C().c === 5,
  Object.getOwnPropertyNames(D.prototype).join() === "constructor,m",
  A.toString() === "class A { 'constructor'() { this.a = 1; } m() { return 2; } }",
];
results.every(function (r) { return r; }) ? "ok" : "fail " + results.indexOf(false)
