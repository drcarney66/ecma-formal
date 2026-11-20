// CompileToCharSet, UnicodePropertyValueExpression :: LoneUnicodePropertyNameOrValue, step 2 calls
// UnicodeMatchPropertyValue(General_Category, s) before testing s; for a binary property name s its
// Assert (step 2) fails.
if (typeof print === "undefined") globalThis.print = console.log;
var cases = [
  ["/\\p{Lu}/u.test('A')", () => /\p{Lu}/u.test("A")],
  ["/\\p{ASCII}/u.test('a')", () => /\p{ASCII}/u.test("a")],
  ["/\\p{Hex}/u.test('f')", () => /\p{Hex}/u.test("f")],
  ["/\\p{Any}/u.test('\\u{10FFFF}')", () => /\p{Any}/u.test("\u{10FFFF}")],
];
for (var [src, run] of cases) {
  try { print(src + ": " + run()); } catch (e) { print(src + ": " + e.constructor.name); }
}
