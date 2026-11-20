// expect: normal: "ok"
// The Evaluation of a RegularExpressionLiteral calls RegExpCreate on its
// BodyText and FlagText, whose ParsePattern parses the pattern at run time
// (the frontend's parse for the early errors is not in the AST): each
// evaluation makes a new object with its own lastIndex, and the flags select
// the grammar (UnicodeMode for u and v).
function f() { return /a(?<n>b)?/g; }
var r1 = f(), r2 = f();
r1.lastIndex = 3;
var results = [
  r1 !== r2,
  r2.lastIndex === 0,
  r1.source === "a(?<n>b)?" && r1.flags === "g",
  /\u{1F600}/u.test("\u{1F600}"),
  /^.$/u.test("\u{1F600}") && !/^.$/.test("\u{1F600}"),
  /[\p{L}--[a-z]]/v.test("A") && !/[\p{L}--[a-z]]/v.test("a"),
  "xaby".replace(/a(?<n>b)/, "$<n>") === "xby",
  Object.getPrototypeOf(/x/) === RegExp.prototype,
];
results.every(function (r) { return r; }) ? "ok" : "fail " + results.indexOf(false)
