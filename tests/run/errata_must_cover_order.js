// expect: normal: "SyntaxError,SyntaxError,SyntaxError,ok"
let out = [];
for (const s of ["([...x = []]) => {};", "async (...x = []) => {};", "async\n(foo) => {};", "(x) => {};"]) {
  try { (0, eval)(s); out.push("ok"); } catch (e) { out.push(e.name); }
}
out.join(",");
