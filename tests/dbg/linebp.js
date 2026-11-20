function f(x) {
  var y = x + 1;
  return y;
}
var s = 0;
for (var i = 0; i < 2; i++) {
  s = s + i;
}

s = f(s) + f(1);
var a = 1; var b = 2;
// Line breakpoints, set at the entry before the parse (pending, then each `breakpoint` event):
// line 5; the blank line 9, moved to 10; line 2 in f, hit by both calls; the loop body's line 7,
// hit on each iteration; line 11 at column 12, the second statement; breakpointLocations of 5-7.
