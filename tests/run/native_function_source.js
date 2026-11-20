// Function.prototype.toString step 3 (refactor R18): the NativeFunction of a
// built-in whose [[InitialName]] is a String has that name as its
// PropertyName; step 4 (a bound function) has none of its own.
// expect: normal: undefined
// print: function max() { [native code] }
// print: function get size() { [native code] }
// print: function () { [native code] }
print(Math.max.toString());
print(Object.getOwnPropertyDescriptor(Map.prototype, 'size').get.toString());
print(Function.prototype.toString.call(function f() {}.bind(null)));
