// The ObjectLiteral `__proto__` early error asks for the PropName of every PropertyDefinition, and PropName
// has no row for CoverInitializedName. Each source is parsed as a Script (indirect eval).
if (typeof print === "undefined") globalThis.print = console.log;
var sources = ["({a = 1});", "({__proto__: 1, __proto__ = 2});", "({a = 1} = {});"];
for (var s of sources) {
  try { (0, eval)(s); print(JSON.stringify(s) + ": no error"); }
  catch (e) { print(JSON.stringify(s) + ": " + e.constructor.name); }
}
