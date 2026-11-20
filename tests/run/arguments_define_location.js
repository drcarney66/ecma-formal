// expect: normal: "2,false,1,3,3,true"
// Own properties are locations (refactor R17, DESIGN §16.14).
// ValidateAndApplyPropertyDescriptor writes the stored property: a descriptor
// with no fields writes nothing (step 4), and {enumerable: false} Sets only
// [[Enumerable]] (step 6.c.i). While index 0 is mapped, arguments[0] reads the
// parameter binding; {writable: false} copies the binding into the stored
// [[Value]] (§10.4.4.2 step 4.a) and removes the mapping.
function f(a) {
  a = 2;
  Object.defineProperty(arguments, '0', {});
  Object.defineProperty(arguments, '0', { enumerable: false });
  var r = [arguments[0], Object.keys(arguments).indexOf('0') >= 0];
  var frozen = Object.freeze({ x: 1 });
  r.push(Reflect.defineProperty(frozen, 'x', { value: 1 }) ? frozen.x : 'no');
  a = 3;
  Object.defineProperty(arguments, '0', { writable: false });
  a = 4;
  r.push(arguments[0], Object.getOwnPropertyDescriptor(arguments, '0').value,
    Object.getOwnPropertyDescriptor(arguments, '0').configurable);
  return r.join(',');
}
f(1)
