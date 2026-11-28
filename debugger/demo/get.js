let proto = { z: 5 };
let point = { x: 3, __proto__: proto };
let a = point.x;
let b = point.z;
a + b;
