import Engine.Model
open Engine Engine.Model Ecma
local notation "Node" => Engine.Model.Node

/-! Parent by the index (`parentBy`, what runs) against its definition (`parentBelow`, the search): at every node
of each file's parse, from the root and from every 97th node as a root; and at a node of another
parse. `lake env lean --run scripts/dev/parent_check.lean FILE.js…` -/

def same (a b : Option Node) : Bool := decide (a = b)

/-- The disagreements from the root `r` at the nodes `ns`. -/
def check (r : Node) (ns : Array Node) : Nat :=
  let ix := index r
  let h := r.height
  ns.foldl (fun bad n => if same (parentBy ix h r n) (parentBelow n h r) then bad else bad + 1) 0

def main (args : List String) : IO UInt32 := do
  let mut bad := 0
  let mut total := 0
  let mut other : Option Node := none
  for f in args do
    let src ← IO.FS.readFile f
    let cs : Array MathVal := (src.toList.map fun c => MathVal.int c.toNat).toArray
    let cx : ParseCx := { annexB := default, strict := false, json := false, module := false }
    match parse (fun _ => default) cx (total + 1) cs Grammar.NT.Script.ctorIdx [] with
    | some (some r) =>
      let ns := (descendants r).push r
      let ns := match other with
        | some o => ns.push o
        | none => ns
      let ds := descendants r
      let roots := #[r] ++ (Array.range (ds.size / 97)).filterMap fun i => ds[i * 97]?
      let b := roots.foldl (fun b q => b + check q ns) 0
      IO.println s!"{if b == 0 then "ok  " else "FAIL"} {f}: {ns.size} nodes from {roots.size} roots, {b} differ"
      bad := bad + b
      total := total + 1
      other := (descendants r)[ns.size / 2]?
    | _ => IO.println s!"skip {f}: no parse"
  return if bad == 0 then 0 else 1
