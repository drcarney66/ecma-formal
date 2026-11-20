module

public import Engine.Host.Bundle

@[expose] public section

/-!
# `ecma-bundle DIR`: a directory's modules as one d8 bundle

```
ecma-bundle DIR
```

prints the bundle (`Engine.Host.Bundle.write`) of `DIR`'s modules: `DIR/main.mjs` the
entrypoint, every other `.mjs` and `.json` file below `DIR` (not a dot file) a module named by its
path from `DIR`, in path order. A missing `main.mjs`, or modules `write` refuses, print `ecma-bundle:
<error>` on stderr, exit 2.
-/

namespace Engine.Cli.Bundle

open Engine.Host

/-- The `.mjs` and `.json` files below `dir` (`rel` its path from the root), by their paths from the root. -/
partial def files (dir : System.FilePath) (rel : String) : IO (List String) := do
  let mut out := []
  for e in ← dir.readDir do
    if e.fileName.startsWith "." then continue
    let r := if rel.isEmpty then e.fileName else rel ++ "/" ++ e.fileName
    if ← e.path.isDir then out := out ++ (← files e.path r)
    else if e.fileName.endsWith ".mjs" || e.fileName.endsWith ".json" then out := out ++ [r]
  return out

/-- The bundle of `dir`'s modules, `main.mjs` the entrypoint. -/
def bundleOf (dir : System.FilePath) : IO (Except String String) := do
  let names := ((← files dir "").toArray.qsort (fun a b => decide (a < b))).toList
  if !names.contains "main.mjs" then return .error s!"{dir}: no main.mjs"
  let read := fun (n : String) => do pure (n, ← IO.FS.readFile (dir / n))
  let mods ← (names.filter (· != "main.mjs")).mapM read
  return Bundle.write (← read "main.mjs") mods

/-- ecma-bundle: the bundle on stdout, exit 0; else exit 2. -/
def main (args : List String) : IO UInt32 := do
  let [dir] := args | IO.eprintln "usage: ecma-bundle DIR"; return 2
  match ← (bundleOf dir).toBaseIO with
  | .ok (.ok b) => IO.print b; return 0
  | .ok (.error e) => IO.eprintln s!"ecma-bundle: {e}"; return 2
  | .error e => IO.eprintln s!"ecma-bundle: {e}"; return 2

end Engine.Cli.Bundle

/-- `ecma-bundle`'s root. -/
def main (args : List String) : IO UInt32 := Engine.Cli.Bundle.main args
