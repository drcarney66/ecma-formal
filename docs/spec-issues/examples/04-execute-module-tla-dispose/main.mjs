// ExecuteModule 4.b: a module with top-level await never disposes the
// resources of its top-level `using` / `await using` declarations.
if (typeof print === "undefined") globalThis.print = console.log;
import("./m.mjs").then(function () { print("evaluation promise fulfilled"); },
                       function (e) { print("rejected: " + e); });
