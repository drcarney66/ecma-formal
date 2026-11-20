// Proxy.revocable (§28.2.2.1): after revoke(), every internal method of the
// Proxy throws (ValidateNonRevokedProxy, §10.5.14); revoking again does nothing.
// expect: normal: "1|0|undefined|TypeError|TypeError|true"
var r = Proxy.revocable({ x: 1 }, {});
var before = r.proxy.x;
var len = r.revoke.length;
var result = r.revoke();
var e1, e2;
try { r.proxy.x; } catch (e) { e1 = e.constructor.name; }
try { Array.isArray(r.proxy); } catch (e) { e2 = e.constructor.name; }
r.revoke();
before + "|" + len + "|" + result + "|" + e1 + "|" + e2 + "|" + (Object.getPrototypeOf(r) === Object.prototype)
