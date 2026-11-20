// GatherAvailableAncestors 1.a reads a.[[CycleRoot]] of a module a whose
// synchronous evaluation threw (Evaluate 9.a never sets [[CycleRoot]]).
// a.mjs imports b.mjs (top-level await) and then c.mjs (throws).
if (typeof print === "undefined") globalThis.print = console.log;
import("./a.mjs").then(
  function () { print("a fulfilled"); },
  function (e) { print("a rejected: " + e); })
  .then(function () { return import("./b.mjs"); })
  .then(function () { print("b fulfilled"); }, function (e) { print("b rejected: " + e); });
