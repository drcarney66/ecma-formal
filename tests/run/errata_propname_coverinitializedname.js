// expect: normal: "SyntaxError,SyntaxError,ok"
let out = [];
for (const s of ["({a = 1});", "({__proto__: 1, __proto__ = 2});", "({a = 1} = {});"]) {
  try { (0, eval)(s); out.push("ok"); } catch (e) { out.push(e.name); }
}
out.join(",");
