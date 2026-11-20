// Assignments (§13.15.2): simple, compound and logical, to a name and to a
// property, and destructuring assignments (§13.15.5), suspending.
// sections: sec-assignment-operators-runtime-semantics-evaluation sec-runtime-semantics-destructuringassignmentevaluation sec-runtime-semantics-iteratordestructuringassignmentevaluation sec-runtime-semantics-keyeddestructuringassignmentevaluation sec-runtime-semantics-propertydestructuringassignmentevaluation sec-runtime-semantics-restdestructuringassignmentevaluation sec-property-accessors-runtime-semantics-evaluation sec-evaluate-property-access-with-expression-key
function plain() {
  Math.max();
  var x, o = {};
  x = void 1;
  x += void 2;
  x ||= void 3; x &&= void 4; x ??= void 5;
  o[void "p"] = 6;
  o.q = void 7;
  [x = void 8] = [];
  ({ a: x = void 9, ...o.r } = {});
  Math.min();
}
function* gen() {
  Math.max();
  var x, o = {};
  x = yield 1;
  x += yield 2;
  x ||= yield 3; x &&= yield 4; x ??= yield 5;
  o[yield "p"] = 6;
  o.q = yield 7;
  [x = yield 8] = [];
  ({ a: x = yield 9, ...o.r } = {});
  Math.min();
}
