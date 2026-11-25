// expect: normal: [object #N]
// print: sync-ok
// print: async-ok

function assertEq(actual, expected, msg) {
  if (!Object.is(actual, expected)) {
    throw new Error((msg || "mismatch") + ": got " + String(actual) + ", expected " + String(expected));
  }
}

// 1. Generator transfer: preserves prototype, closes original WITHOUT running finally, cleanup moves to transferred
let finallyCount = 0;
function* gen() {
  try {
    yield "a";
    yield "b";
  } finally {
    finallyCount++;
  }
}

const g = gen();
assertEq(g.next().value, "a", "first yield");
const t = g.transfer();
assertEq(Object.getPrototypeOf(t), Object.getPrototypeOf(g), "same prototype");
assertEq(finallyCount, 0, "transfer does not run finally");
assertEq(g.next().done, true, "original next() is done");
assertEq(g.return("ignored").done, true, "original return() is done");
assertEq(finallyCount, 0, "original return() does not run finally");

const stepB = t.next();
assertEq(stepB.value, "b", "transferred continues at b");
assertEq(stepB.done, false, "transferred not done yet");
t.return("stop");
assertEq(finallyCount, 1, "transferred return() runs finally");

// 2. Active generator throws TypeError on self-transfer
function* selfTransfer() {
  selfIter.transfer();
}
const selfIter = selfTransfer();
let activeThrew = false;
try {
  selfIter.next();
} catch (e) {
  activeThrew = e instanceof TypeError;
}
assertEq(activeThrew, true, "active generator throws TypeError");

// 3. Array, String, Map, Set, RegExp iterators & Iterator helpers
const arrIt = [10, 20, 30].values();
assertEq(arrIt.next().value, 10, "arr 10");
const arrT = arrIt.transfer();
assertEq(arrIt.next().done, true, "arr original closed");
assertEq(arrT.next().value, 20, "arr transferred 20");

const baseGen = gen();
const upper = baseGen.map((s) => s.toUpperCase());
const upperT = upper.transfer();
assertEq(upper.next().done, true, "helper original closed");
assertEq(upperT.next().value, "A", "helper transferred A");
assertEq(baseGen.next().value, "b", "underlying generator not transferred");

print("sync-ok");

// 4. AsyncGenerator transfer & pending-request rejection
async function testAsync() {
  async function* agen() {
    yield 1;
    yield 2;
  }
  const ag = agen();
  const pending = ag.next();
  let pendingThrew = false;
  try {
    ag.transfer();
  } catch (e) {
    pendingThrew = e instanceof TypeError;
  }
  assertEq(pendingThrew, true, "pending request throws TypeError");
  const r1 = await pending;
  assertEq(r1.value, 1, "r1 === 1");

  const agT = ag.transfer();
  const oldDone = await ag.next();
  assertEq(oldDone.done, true, "old async gen closed");
  const r2 = await agT.next();
  assertEq(r2.value, 2, "transferred async gen yields 2");
  print("async-ok");
}
testAsync();
