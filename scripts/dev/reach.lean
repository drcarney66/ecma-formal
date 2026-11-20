import Lean
open Lean

/-!
The constants reachable from a set of roots, for the dead-code sweep.

usage: `lake env lean --run scripts/dev/reach.lean <tag> <item>...`, where an item is a module to import (its
`main`, if any, is a root) or `+Name`, a constant to root by name (a proved claim, a stated law). Every constant
of a `Gen` module is a root, and so is every instance of a derivable class (`Repr`, `BEq`, `DecidableEq`,
`Inhabited`, ...) and every coercion (elaboration unfolds a coercion, so no term names it). The traversal follows
each constant's type and value (a theorem's proof term too), an inductive's constructors, and `implemented_by`
implementations. `scripts/dev/reach_all.sh` runs it with the sweep's roots. Writes `<tag>.dead.tsv`,
`<tag>.live.tsv` (module, first line, last line, kind, name) and `<tag>.mods` (the project's modules imported).
-/

def projectMod (m : Name) : Bool :=
  let r := m.getRoot
  r == `Ecma || r == `Engine || r == `Debugger || r == `Unicode

unsafe def main (args : List String) : IO Unit := do
  enableInitializersExecution
  initSearchPath (← findSysroot)
  let tag := args.head!
  let items := args.tail!
  let mods := items.filter (!·.startsWith "+") |>.map String.toName
  let named := items.filter (·.startsWith "+") |>.map fun s => (s.drop 1).toString.toName
  let env ← importModules (mods.toArray.map fun m => { module := m, importAll := true }) {} (loadExts := true)
  let modOf (n : Name) : Option Name := (env.getModuleIdxFor? n).map fun i => env.header.moduleNames[i.toNat]!
  let inProject (n : Name) : Bool := match modOf n with | some m => projectMod m | none => false
  let mut todo : Array Name := #[`main]
  for n in named do
    unless env.contains n do throw (IO.userError s!"no constant {n}")
    todo := todo.push n
  -- kept by policy: the generated files; the instances of the derivable classes (derived or not); coercions,
  -- which elaboration unfolds, so that no term names them
  let derivable := [``Repr, ``BEq, ``DecidableEq, ``Inhabited, ``Nonempty, ``Hashable, ``Ord, ``ToString,
    ``Coe, ``CoeTail, ``CoeHead, ``CoeOut, ``CoeOTC, ``CoeHTCT, ``CoeFun, ``CoeSort, ``CoeDep]
  for (n, ci) in env.constants.toList do
    unless inProject n do continue
    if (modOf n).any (fun m => m.components.contains `Gen) then todo := todo.push n
    else if Meta.isInstanceCore env n then
      if let some c := ci.type.getForallBody.getAppFn.constName? then
        if derivable.contains c then todo := todo.push n
  let mut seen : NameSet := {}
  while !todo.isEmpty do
    let n := todo.back!
    todo := todo.pop
    if seen.contains n then continue
    seen := seen.insert n
    let some ci := env.find? n | continue
    let mut used := ci.type.getUsedConstantsAsSet
    match ci with
    | .defnInfo d => used := used ++ d.value.getUsedConstantsAsSet
    | .thmInfo d => used := used ++ d.value.getUsedConstantsAsSet
    | .opaqueInfo d => used := used ++ d.value.getUsedConstantsAsSet
    | .inductInfo d => for c in d.ctors do todo := todo.push c
    | .ctorInfo d => todo := todo.push d.induct
    | .recInfo d => for c in d.all do todo := todo.push c
    | _ => pure ()
    for u in used do
      unless seen.contains u do todo := todo.push u
    for extra in [Compiler.mkUnsafeRecName n, n ++ `_unsafe_rec, n ++ `impl, n ++ `_impl] do
      if env.contains extra then todo := todo.push extra
    if let some i := Compiler.getImplementedBy? env n then todo := todo.push i
  let mut out : Array String := #[]
  let mut live : Array String := #[]
  for (n, ci) in env.constants.toList do
    unless inProject n do continue
    let some m := modOf n | continue
    let some (r : DeclarationRanges) := declRangeExt.find? (level := .server) env n | continue
    let kind := match ci with
      | .thmInfo _ => "thm" | .defnInfo _ => "def" | .inductInfo _ => "ind" | .opaqueInfo _ => "opq"
      | .ctorInfo _ => "ctor" | _ => "other"
    let line := s!"{m}\t{r.range.pos.line}\t{r.range.endPos.line}\t{kind}\t{n}"
    if seen.contains n then live := live.push line else out := out.push line
  IO.FS.writeFile s!"{tag}.dead.tsv" (String.intercalate "\n" out.toList ++ "\n")
  IO.FS.writeFile s!"{tag}.live.tsv" (String.intercalate "\n" live.toList ++ "\n")
  IO.FS.writeFile s!"{tag}.mods" (String.intercalate "\n" (env.header.moduleNames.toList.filter projectMod |>.map toString) ++ "\n")
  IO.println s!"roots {named.length} reachable {seen.size} dead {out.size} live {live.size}"
