const c1 = Composite({ y: 4, x: 1, 10: "ten", 2: "two" });
const c2 = Composite({ 2: "two", x: 1, 10: "ten", y: 4 });
const visited = new Set([c1]);
print([
  "interned=" + (c1 === c2),
  "keys=" + Object.keys(c1).join(","),
  "inSet=" + visited.has(Composite({ x: 1, y: 4, 2: "two", 10: "ten" }))
].join(" | "));
