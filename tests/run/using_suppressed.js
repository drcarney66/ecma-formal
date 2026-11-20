// A dispose method that throws after the block threw makes a SuppressedError
// whose "error" is the new exception and "suppressed" the old one (§7.5.5).
// expect: normal: "SuppressedError:dispose:body"
var r;
try {
  using x = { [Symbol.dispose]() { throw "dispose"; } };
  throw "body";
} catch (e) {
  r = e.name + ":" + e.error + ":" + e.suppressed;
}
r
