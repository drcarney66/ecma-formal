// expect: normal: undefined
// print: 1 == dict: TypeError
// print: dict == false: TypeError
// IsLooselyEqual steps 9-10, "return ? IsLooselyEqual(! ToNumber(x), y)" (tc39/ecma262
// PR #4067, 8a3e4aae): with y an Object whose ToPrimitive throws (no valueOf or toString),
// the inner call's throw completion propagates. (`x == false` is IsLooselyEqual(false, x).)
var dict = Object.create(null);
try { print(String(1 == dict)); } catch (e) { print("1 == dict: " + e.constructor.name); }
try { print(String(dict == false)); } catch (e) { print("dict == false: " + e.constructor.name); }
