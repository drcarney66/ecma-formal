// needs: a module loader that survives a file it cannot read
// args: --module-dir tests/run/modules
// Not run: a defect of ecma-run's loader (2026-11-19). With the flat loader
// (--module-dir) the run dies before it starts: `uncaught exception: Tried to
// read file 'tests/run/modules/...' containing non UTF-8 data.`, exit 1.
// Engine/Host/Program.lean's moduleTable reads every file the program names
// as `./NAME` with IO.FS.readFile when the run begins, and the exception it
// throws escapes main. Before this header the case imported ./modules/NAME,
// which the flat loader serves no file for, so it passed without reading one.
// js-run's module loader (audit F334): a module file it cannot read (here a
// JSON module that is not UTF-8) fails the load with a TypeError, like a
// missing file, and the failure is cached by the resolved key like every
// other result, so the same request fails the same way each time
// (HostLoadImportedModule, §16.2.1.10). Before, the run stopped with
// `unsupported`.
// expect: normal: undefined
// print: TypeError,TypeError
var out = [];
import("./bad_utf8.json", { with: { type: "json" } }).catch(function (e) {
  out.push(e.name);
  return import("./bad_utf8.json", { with: { type: "json" } });
}).catch(function (e) { out.push(e.name); print(out.join()); });
void 0;
