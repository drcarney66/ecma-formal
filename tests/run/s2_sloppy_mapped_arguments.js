// A sloppy function with a simple parameter list gets a mapped arguments object
// (§10.4.4.7): arguments[i] and the parameter are one binding until the mapping is
// removed (delete, or a define with writable false); extra arguments are not mapped.
// expect: normal: "2,3,1,true,5,5,8,x,y"
function f(a, b) {
  arguments[0] = 2; var r = [a];
  b = 3; r.push(arguments[1]);
  r.push(arguments.length === 3 ? 1 : 0, arguments.callee === f);
  delete arguments[0]; a = 5; r.push(a); arguments[0] = 7;
  Object.defineProperty(arguments, "1", { value: 5, writable: false }); r.push(b);
  b = 8; r.push(b, arguments[2]); arguments[2] = "y"; r.push(arguments[2]);
  return r;
}
f(1, 2, "x").join()
