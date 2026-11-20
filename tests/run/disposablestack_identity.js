// expect: normal: "a,true,true|b,a|true"
// A DisposableStack's [[DisposableResourceStack]] is a List with identity and
// its slots are read and Set at the steps that read and Set them (refactor
// R4, finding F4). use()'s argument disposableStack.[[DisposableResourceStack]]
// is the List before the getter of Symbol.dispose runs:
// - a getter that disposes the stack leaves it disposed (use() writes back
//   nothing), and the resource it returns is appended to the disposed List,
//   so it is never disposed;
// - a getter that moves the stack: the resource is appended to the moved
//   List, which the new stack disposes, last in first out.
var log = [];
var stack = new DisposableStack();
stack.use({ [Symbol.dispose]() { log.push('a'); } });
stack.use({ get [Symbol.dispose]() {
  stack.dispose();
  log.push(String(stack.disposed));
  return function () { log.push('b'); };
} });
log.push(String(stack.disposed));
stack.dispose();
var log2 = [];
var s2 = new DisposableStack();
var moved;
s2.use({ [Symbol.dispose]() { log2.push('a'); } });
s2.use({ get [Symbol.dispose]() {
  moved = s2.move();
  return function () { log2.push('b'); };
} });
moved.dispose();
log.join() + '|' + log2.join() + '|' + s2.disposed
