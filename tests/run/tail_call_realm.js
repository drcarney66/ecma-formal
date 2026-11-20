// expect: normal: "TypeError;true;200"
// Tail calls (refactor R8, DESIGN §16.5). F's `return proxy()` is in tail
// position (strict, ECMA-262 §15.10.1): EvaluateCall step 6 performs
// PrepareForTailCall, and the running execution context is still F's, in the
// other realm, when the revoked Proxy's [[Call]] throws its TypeError (test262
// built-ins/Proxy/revocable/tco-fn-realm.js). A strict tail-recursive loop of
// 200 calls completes; every context it pushes is removed by identity.
// The other realm's code is a string, not a template literal: the spec's TV of a
// template is exponential in its length.
"use strict";
var other = $262.createRealm();
var F = other.evalScript(
  '"use strict";\n' +
  '(function() {\n' +
  '  var proxyObj = Proxy.revocable(function() {}, {});\n' +
  '  var proxy = proxyObj.proxy;\n' +
  '  proxyObj.revoke();\n' +
  '  return proxy();\n' +
  '})\n'
);
var out = [];
try { F(); } catch (e) { out.push(e.constructor.name, e instanceof other.global.TypeError && !(e instanceof TypeError)); }
function count(n, acc) { return n === 0 ? acc : count(n - 1, acc + 1); }
out.push(count(200, 0));
out.join(';')
