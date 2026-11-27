// expect: normal: true
let a
/x/.test("x");

let r1 = false;
let b
r1 = /x/.test("x");

function f() {
  return
  /y/.test("y");
}

let r2 = (f() === undefined);

let r3 = false;
do {
  r3 = true
} while (false) /z/.test("z");

let r4 = `${function() { let c = 1
  return c
}()}` === "1";

r1 && r2 && r3 && r4;
