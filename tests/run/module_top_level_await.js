// module: yes
// expect: normal: undefined
// print: before
// print: 3 after
// A Module whose body contains `await` has [[HasTLA]] true: ExecuteModule
// runs it with AsyncBlockStart (§16.2.1.7.3.2 step 4.b), so the body suspends
// at each Await and the rest of it runs from the promise jobs.
print("before");
var a = await Promise.resolve(1);
var b = await 2;
print((a + b) + " after");
