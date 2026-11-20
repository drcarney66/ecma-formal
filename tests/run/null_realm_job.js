// A promise reaction Job with an empty handler has realm null (§27.2.2.1,
// NewPromiseReactionJob step 3), yet its step 1.i calls the capability's
// resolve function, here a callable Proxy whose [[Call]] creates argArray in
// the current realm (§10.5.12 step 7) and runs the apply trap. The host
// prepares a null-realm Job in the realm it created (its choice, §9.5;
// runJobs), so argArray is that realm's Array, not the other realm's
// where all this code lives. This pins the host's choice (an editorial
// report, docs/spec-issues/47); it does not test that Jobs run on an empty stack
// (audit F036), which no program observes.
// expect: normal: undefined
// print: false,true
// The other realm's code is a string, not a template literal: the spec's TV of a
// template is exponential in its length.
var other = $262.createRealm().global;
other.MainArrayProto = Array.prototype;
other.eval(
  'var resolveProxy = new Proxy(function(){}, { apply: function(t, thisArg, args) {\n' +
  '  print([Object.getPrototypeOf(args) === Array.prototype, Object.getPrototypeOf(args) === MainArrayProto].join());\n' +
  '}});\n' +
  'function FakePromise(executor) { executor(resolveProxy, function(){}); }\n' +
  'var p = Promise.resolve(1);\n' +
  'p.constructor = {}; p.constructor[Symbol.species] = FakePromise;\n' +
  'p.then(undefined);\n'
);
undefined;
