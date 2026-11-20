// Destructuring patterns (§13.15.5, §14.3.3) with elisions, trailing commas,
// rest elements, nested patterns and shorthand properties, an Initializer or
// a computed key suspending.
// sections: sec-runtime-semantics-destructuringassignmentevaluation sec-runtime-semantics-iteratordestructuringassignmentevaluation sec-runtime-semantics-keyeddestructuringassignmentevaluation sec-runtime-semantics-propertydestructuringassignmentevaluation sec-runtime-semantics-restdestructuringassignmentevaluation sec-runtime-semantics-bindinginitialization sec-runtime-semantics-iteratorbindinginitialization sec-destructuring-binding-patterns-runtime-semantics-propertybindinginitialization sec-runtime-semantics-keyedbindinginitialization
function plain() {
  Math.max();
  var a, b, c, o = {};
  [a, , b = void 1, ...c] = [1, 2];
  [a, , ] = [1];
  [, ...[a]] = [1, 2];
  [[a = void 2], { b }] = [[], {}];
  ({ a = void 3, b: [c] = [void 4], [void "k"]: o.k, ...o.r } = {});
  var [d, , e = void 5, ...f] = [1];
  var [g, , ] = [];
  let { h = void 6, i: { j } = { j: void 7 }, [void "k"]: k } = {};
  const [, ...[l]] = [1, 2];
  Math.min();
}
function* gen() {
  Math.max();
  var a, b, c, o = {};
  [a, , b = yield 1, ...c] = [1, 2];
  [a, , ] = [1];
  [, ...[a]] = [1, 2];
  [[a = yield 2], { b }] = [[], {}];
  ({ a = yield 3, b: [c] = [yield 4], [yield "k"]: o.k, ...o.r } = {});
  var [d, , e = yield 5, ...f] = [1];
  var [g, , ] = [];
  let { h = yield 6, i: { j } = { j: yield 7 }, [yield "k"]: k } = {};
  const [, ...[l]] = [1, 2];
  Math.min();
}
