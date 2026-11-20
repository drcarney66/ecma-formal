// Identifier early errors: "the StringValue of IdentifierName is the StringValue of any ReservedWord except
// for yield or await", and StringValue has no row for ReservedWord. Each source is parsed as a Script.
if (typeof print === "undefined") globalThis.print = console.log;
var sources = ["var \\u0069f = 1;", "var i\\u0066 = 1;", "var \\u{63}lass = 1;", "var \\u0079ield = 1;",
               "var \\u0061wait = 1;", "var \\u0069g = 1;"];
for (var s of sources) {
  try { (0, eval)(s); print(s + ": no error"); }
  catch (e) { print(s + ": " + e.constructor.name); }
}
