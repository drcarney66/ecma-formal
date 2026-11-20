// Without Annex B (not a web-browser host) the function stays in its Block.
// expect: normal: "undefined"
function g() {
  { function f() { return 2; } }
  return typeof f;
}
g()
