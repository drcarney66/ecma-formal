// args: --web-browser
// expect: normal: "false,undefined,true,true,true,true,false,null,skipped,true,object:function"
// §B.3.6 on a web-browser host (refactor R21): the test262 host's
// $262.IsHTMLDDA is a built-in function created with « [[IsHTMLDDA]] ».
// ToBoolean step 3 makes it falsy (`!`, `if`, `?:`, `&&`, `||`, `&&=`, the
// loop tests), typeof step 12 gives "undefined", IsLooselyEqual step 4 makes
// it == null and == undefined, and IsStrictlyEqual is unchanged. A
// $262.createRealm() realm has its own.
var d = $262.IsHTMLDDA;
var r = [];
r.push(!!d);
r.push(typeof d);
r.push(d == null);
r.push(d == undefined);
r.push(undefined == d && null == d);
r.push(d !== undefined && d !== null);
r.push(d ? true : false);
r.push(String(d()));
var s = "skipped";
if (d) s = "taken";
while (d) { s = "loop"; break; }
r.push(s);
var x = d; x &&= 1;
r.push(x === d && (d || true) === true && (d && 1) === d);
var other = $262.createRealm().global.$262.IsHTMLDDA;
r.push((!other && typeof other === "undefined" && other == null ? "object" : "wrong") + ":" +
  Object.prototype.toString.call(other).slice(8, -1).toLowerCase());
r.join();
