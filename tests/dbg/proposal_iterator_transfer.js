let cleanedUp = 0;
function* items() {
  try {
    yield "first";
    yield "second";
  } finally {
    cleanedUp++;
  }
}
const orig = items();
const a = orig.next().value;
const moved = orig.transfer();
const origDone = orig.next().done;
const b = moved.next().value;
moved.return();
print("a=" + a + ", origDone=" + origDone + ", b=" + b + ", finallyRuns=" + cleanedUp);
