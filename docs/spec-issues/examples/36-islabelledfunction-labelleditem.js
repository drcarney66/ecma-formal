// IsLabelledFunction(stmt) takes a Statement node; step 1 asks whether it "is a LabelledStatement" and step 2
// takes its LabelledItem, a grandchild. Each source is parsed as a Script (indirect eval).
if (typeof print === "undefined") globalThis.print = console.log;
var sources = ["if (1) l: function f() {}", "while (0) l: function f() {}",
               "if (0) ; else a: b: function g() {}", "while (0) l: m: x;", "l: function h() {}"];
for (var s of sources) {
  try { (0, eval)(s); print(s + ": no error"); }
  catch (e) { print(s + ": " + e.constructor.name); }
}
