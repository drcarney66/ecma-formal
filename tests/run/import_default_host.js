// args: --module-dir tests/run/modules
// expect: normal: undefined
// print: true true
// HostLoadImportedModule (§16.2.1.10) always performs FinishLoadingImportedModule
// (R23): a module the host cannot load rejects the import() promise with the
// throw completion the host's loader gives (here a new TypeError), and a
// request with an unsupported "type" attribute fails the same way.
var results = [];
import("./does-not-exist.mjs").catch(function (e) { results.push(e instanceof TypeError); })
  .then(function () { return import("./lib.mjs", { with: { type: "css" } }); })
  .catch(function (e) { results.push(e instanceof TypeError); })
  .then(function () { print(results.join(" ")); });
void 0;
