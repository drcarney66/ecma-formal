// BigInt objects (§21.2): ToPrimitive of Object(1n) calls BigInt.prototype.valueOf,
// so mixing it with a Number throws; BigInt() converts and asIntN wraps.
// expect: normal: "TypeError,true,ff,-1,10"
"use strict";
var e;
try { Object(1n) + 1; } catch (x) { e = x; }
[e.constructor.name, Object(2n) == 2n, (255n).toString(16), BigInt.asIntN(8, 255n), BigInt(10)].join()
