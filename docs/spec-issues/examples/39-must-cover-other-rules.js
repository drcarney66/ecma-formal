// Each source has a cover that does not cover what an early error rule says it must; the
// other rules of the same and enclosing productions read static semantics through the cover.
if (typeof print === "undefined") globalThis.print = console.log;
var sources = [
  "([...x = []]) => {};",
  "([...x, y]) => {};",
  "(a, ...b,) => {};",
  "async (...x = []) => {};",
  "async\n(foo) => {};",
  "(x) => {};",
];
for (var s of sources) {
  try {
    (0, eval)(s);
    print(JSON.stringify(s) + ": no error");
  } catch (e) {
    print(JSON.stringify(s) + ": " + e.constructor.name);
  }
}
