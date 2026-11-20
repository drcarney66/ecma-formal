// AsyncBlockStart step 4 "Assert: result is unused" against Await step 8
// "Return ? RunCallerContext(empty)": every async function that awaits.
if (typeof print === "undefined") globalThis.print = console.log;
async function f() { await 1; return 2; }
f().then(function (v) { print("f fulfilled with " + v); });
