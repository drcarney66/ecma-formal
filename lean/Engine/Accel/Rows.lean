module

public import Ecma.Host.Jobs
public import Ecma.Machine.Code

@[expose] public section

/-!
# The accelerator table

Accelerators as data: a `Row` is a key in the spec's ids (`Key`), the entry at that key (`Entry`, the oracle's type
at its kind) and a `Mode` (equal to the machine's run, or related to it observationally). A `Table` is a list of rows;
`restrict m` keeps the rows of mode at most `m`. Lookups by kind (`Table.alg` …) take the first row whose key
matches and whose entry answers; `only k` and `algAt a` keep the rows a lookup of kind `k` or of algorithm `a` can
take, with the same answers. An algorithm's row serves both its calls and its steps at a Parse Node.
-/

namespace Engine.Accel

/-- The size (a List's elements, a loop's rounds, a walk's depth) past which a bounded shortcut declines to the
steps: over the 0x110000 code points and an index loop to 10^6. -/
def sizeLimit : Nat := 0x200000

end Engine.Accel

namespace Engine.Accel.Rows
open Ecma Ecma.Machine

variable {M : Model}

/-- An accelerator's key: an algorithm, an SDO, a primitive, or the `Repeat, while` loops (the entry matches
the loop's path, test, and lowered body). -/
inductive Key where
  | alg (a : AlgId)
  | sdo (s : SdoId)
  | prim (q : PrimId)
  | loop

/-- The entry's type at each key: the oracle's type at that kind, less the key. -/
def Entry (M : Model) : Key → Type
  | .alg _ => List (Val M) → Option (Run M (Option (Val M)))
  | .sdo _ => M.Node → List (Val M) → Option (Run M (Val M))
  | .prim _ => List (Val M) → Option (Run M (Val M))
  | .loop => List Nat → Op → Code → Option Nat → Array (Val M) → State M → Option (Run M (Nat × List (Slot × Val M)))

/-- What a row's entry is held to: equal to the machine's run, or related to it observationally. -/
inductive Mode where
  | exact
  | obs
  deriving DecidableEq

/-- One accelerator: its key, its entry and its mode. -/
structure Row (M : Model) where
  key : Key
  entry : Entry M key
  mode : Mode

/-- The accelerators, as rows. -/
abbrev Table (M : Model) := List (Row M)

/-- Two algorithm ids are the same, field by field. -/
def sameAlg (a b : AlgId) : Bool := a.clause == b.clause && a.idx == b.idx

namespace Row

/-- The row's answer for algorithm `a`'s arguments. -/
def alg (r : Row M) (a : AlgId) (vs : List (Val M)) : Option (Run M (Option (Val M))) :=
  match r with
  | ⟨.alg a', e, _⟩ => if sameAlg a' a then e vs else none
  | _ => none

/-- The row's answer for SDO `s` at a Parse Node. -/
def sdo (r : Row M) (s : SdoId) (nd : M.Node) (vs : List (Val M)) : Option (Run M (Val M)) :=
  match r with
  | ⟨.sdo s', e, _⟩ => if s' = s then e nd vs else none
  | _ => none

/-- The row's answer for primitive `q`. -/
def prim (r : Row M) (q : PrimId) (xs : List (Val M)) : Option (Run M (Val M)) :=
  match r with
  | ⟨.prim q', e, _⟩ => if q' = q then e xs else none
  | _ => none

/-- The row's skip of the loop at path `p` with test `t` and body `body`. -/
def loop (r : Row M) (p : List Nat) (t : Op) (body : Code) (l : Option Nat) (sl : Array (Val M)) (s : State M) :
    Option (Run M (Nat × List (Slot × Val M))) :=
  match r with
  | ⟨.loop, x, _⟩ => x p t body l sl s
  | _ => none

end Row

namespace Table

/-- The table's answer for algorithm `a`: the first row that answers. -/
def alg (tab : Table M) (a : AlgId) (vs : List (Val M)) : Option (Run M (Option (Val M))) :=
  tab.findSome? (·.alg a vs)

/-- The table's answer for SDO `s`. -/
def sdo (tab : Table M) (s : SdoId) (nd : M.Node) (vs : List (Val M)) : Option (Run M (Val M)) :=
  tab.findSome? (·.sdo s nd vs)

/-- The table's answer for primitive `q`. -/
def prim (tab : Table M) (q : PrimId) (xs : List (Val M)) : Option (Run M (Val M)) :=
  tab.findSome? (·.prim q xs)

/-- The table's skip of a loop. -/
def loop (tab : Table M) (p : List Nat) (t : Op) (body : Code) (l : Option Nat) (sl : Array (Val M)) (s : State M) :
    Option (Run M (Nat × List (Slot × Val M))) :=
  tab.findSome? (·.loop p t body l sl s)

end Table

end Engine.Accel.Rows
