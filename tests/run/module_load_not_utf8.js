// needs: a module loader that survives a file it cannot read
// args: --module-dir tests/run/modules
// Not run: a defect of ecma-run's loader (2026-11-19). With the flat loader
// (--module-dir) the run dies before it starts: `uncaught exception: Tried to
// read file 'tests/run/modules/...' containing non UTF-8 data.`, exit 1.
// Engine/Host/Program.lean's moduleTable reads every file the program names
// as `./NAME` with IO.FS.readFile when the run begins, and the exception it
// throws escapes main. Before this header the case imported ./modules/NAME,
// which the flat loader serves no file for, so it passed without reading one.
// A module file that is not UTF-8 text: js-run's loader (HostLoadImportedModule,
// §16.2.1.10) completes the load with a throw completion (a TypeError, as for a
// missing file), so the import() promise is rejected instead of the run
// stopping (`.notParsed`).
// expect: normal: undefined
// print: TypeError
// print: TypeError
import("./not_utf8.mjs").then(() => print("loaded"), e => print(e.constructor.name))
  .then(() => import("./not_utf8.json", { with: { type: "json" } }))
  .then(() => print("loaded"), e => print(e.constructor.name));
void 0;
