const imm = JSON.parse('{"x":[1,{"y":2}],"__proto__":{"safe":true}}', { freeze: true });
const nullOnly = JSON.parse('{"mutable":1}', { nullPrototypeObjects: true });
nullOnly.mutable = 2;
print([
  "frozen=" + Object.isFrozen(imm.x[1]),
  "proto=" + Object.getPrototypeOf(imm),
  "ownProto=" + imm.__proto__.safe,
  "nullMutable=" + nullOnly.mutable
].join(", "));
