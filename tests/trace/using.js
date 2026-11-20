// `using` declarations (§14.3.1.2) and the disposal at the end of a block
// (§9.2.4), an Initializer suspending.
// sections: sec-let-and-const-declarations-runtime-semantics-evaluation sec-block-runtime-semantics-evaluation sec-adddisposableresource sec-createdisposableresource sec-getdisposemethod sec-disposeresources sec-bindingevaluation
function plain() {
  Math.max();
  {
    using a = void 0, b = { [Symbol.dispose]() {} };
    using c = null;
  }
  Math.min();
}
function* gen() {
  Math.max();
  {
    using a = yield 0, b = { [Symbol.dispose]() {} };
    using c = null;
  }
  Math.min();
}
