module

public import Ecma.Ops.Leaf

@[expose] public section

/-!
# Table columns and phrase arguments

A table's column by its heading, and a phrase meaning's arguments from a phrase's holes.
-/

namespace Ecma

variable {M : Model}

/-- The column headed `col` (a String) among a table's headings `hs`: a whole heading's, else
part `k` of a heading "A and B" (A `k = 0`, B `k = 1`), which names line `k` of its cells. -/
def colOfHeads (hs : List (Option String)) (col : Val M) : Option (Nat × Option Nat) :=
  match hs.findIdx? fun | some h => Val.same (.str (M.strLit h)) col | none => false with
  | some i => some (i, none)
  | none => hs.zipIdx.findSome? fun
    | (some h, i) => match h.splitOn " and " with
      | [a, b] => if Val.same (.str (M.strLit a)) col then some (i, some 0)
        else if Val.same (.str (M.strLit b)) col then some (i, some 1) else none
      | _ => none
    | (none, _) => none

/-- A Parse Node as a value; none, `.absent`. -/
def nodeVal {M : Model} : Option M.Node → Val M
  | some n => .node n
  | none => .absent

/-- An argument of a sort test: the subject value, or an enum constant. -/
def sortArg {M : Model} (v : Val M) : SortArg → Val M
  | .subject => v
  | .enum e => .enum e

end Ecma
