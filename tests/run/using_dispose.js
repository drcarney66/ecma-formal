// `using` declarations (§14.3.1) dispose their resources in reverse order when
// the Block ends (DisposeResources, §7.5.5); DisposableStack.prototype.use too.
// expect: normal: "b,a,s"
var log = [];
function res(n) { return { [Symbol.dispose]() { log.push(n); } }; }
{
  using a = res("a"), b = res("b");
}
var stack = new DisposableStack();
stack.use(res("s"));
stack.dispose();
log.join()
