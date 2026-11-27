// expect: normal: "SyntaxError,SyntaxError,3"
let out = [];
for (const s of ["for (let a\n a < 1; a++) {}", "let a;\na\n[\n] = [];"]) {
  try { (0, eval)(s); out.push("ok"); } catch (e) { out.push(e.name); }
}
let a = 0, b = 1, c = 2;
a = b
+c;
out.push(a);
out.join(",");
