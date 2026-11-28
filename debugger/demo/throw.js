function check(n) {
  if (n < 0) throw new RangeError("negative");
  return n;
}
let msg;
try {
  check(-1);
} catch (e) {
  msg = e.message;
}
msg;
