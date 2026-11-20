module

public import Ecma.Prims.Lists
public import Engine.Model

@[expose] public section

/-!
# List updates in place at Impl

Accelerated primitives for Append, Prepend, "Add e to S" and ReplaceElem: each takes the heap out of
the State, clears the List's slot, updates its elements and puts the cell back. Where the State is
unique the elements are then unique too, so the update does not copy them.

Accelerator debt: each accelerated primitive equals the machine's.
-/

namespace Engine.Accel.ListUpdate

open Ecma Ecma.Prims.Lists

abbrev F := Engine.Impl

/-- `s`'s heap, and `s` without it. -/
@[inline] def take (s : State F) : Array (Cell F) × State F := (s.heap, { s with heap := #[] })

/-- The List cell at `a` with `f` applied to its elements, its slot cleared while `f` runs; `false`
for another cell. -/
def modifyIn (a : Nat) (f : Array (Val F) → Array (Val F)) : Run F Bool := fun s =>
  let (h, s) := take s
  match h[a]? with
  | some (.list xs o) =>
    let h := h.setIfInBounds a (.list #[] o)
    .ok true { s with heap := h.setIfInBounds a (.list (f xs) o) }
  | some _ => .ok false { s with heap := h }
  | none => .stop .sortError

/-- Append x to the List at a. -/
def appendIn (x : Val F) (a : Nat) : Run F (Val F) := do
  if ← modifyIn a (·.push x) then return .enum Known.eUnused else Run.stop .sortError

/-- Prepend x to the List at a. -/
def prependIn (x : Val F) (a : Nat) : Run F (Val F) := do
  if ← modifyIn a (#[x] ++ ·) then return .enum Known.eUnused else Run.stop .sortError

/-- Add the CharSetElement sequence `sq` to the CharSet cell at `a`, clearing its slot while `csAdd` runs. -/
def addCsIn (a : Nat) (sq : F.Seq F.Math) : Run F (Val F) := fun s =>
  let (h, s) := take s
  match h[a]? with
  | some (.charSet cs) =>
    let h := h.setIfInBounds a (.charSet F.csEmpty)
    .ok (.enum Known.eUnused) { s with heap := h.setIfInBounds a (.charSet (F.csAdd cs sq)) }
  | _ => .stop .sortError

/-- Add e to the List or CharSet l unless it contains it. -/
def addIn (e l : Val F) : Run F (Val F) :=
  match l with
  | .ref a => do
    match ← readCell a with
    | .list xs _ =>
      if ← hasElem e xs then return .enum Known.eUnused
      discard <| modifyIn a (·.push e)
      return .enum Known.eUnused
    | .charSet _ =>
      let sq ← Prims.CharSets.elemSeq e
      addCsIn a sq
    | _ => Run.stop .sortError
  | _ => Run.stop .sortError

/-- Replace the first element of l that is old with new. -/
def replaceIn (l old new : Val F) : Run F (Val F) := do
  let (a, xs) ← listCell l
  let i ← optOr .assertFailed (indexOf old xs)
  let _ ← modifyIn a (F.seqSet · i new)
  return .enum Known.eUnused

/-- The accelerated primitives: a run from the arguments, or `none`. -/
def prim (q : PrimId) (xs : List (Val F)) : Option (Run F (Val F)) :=
  if q == Known.pAppend then match xs.map Val.used with
    | [x, .ref a] => some (appendIn x a)
    | _ => none
  else if q == Known.pPrepend then match xs.map Val.used with
    | [x, .ref a] => some (prependIn x a)
    | _ => none
  else if q == Known.pSetAdd then match xs.map Val.used with
    | [e, l] => some (addIn e l)
    | _ => none
  else if q == Known.pReplaceElem then match xs.map Val.used with
    | [l, old, new] => some (replaceIn l old new)
    | _ => none
  else none

end Engine.Accel.ListUpdate
