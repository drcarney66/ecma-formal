module

public import Engine.Machine
public import Engine.Proofs.Pins.Eq
public import Lean.Elab.Command
public meta import Engine.Machine
public meta import Engine.Proofs.Pins.Eq
public meta import Lean.Elab.Command
public meta import Lean.Meta.Eval
public meta import Engine.Proofs.Pins.Gen.Quote

public section

/-!
# Pins: a unit of the program as a literal, and its equality test

`pin_alg_def isWriteCode ⟨2775, 0⟩` evaluates `Engine.P'.alg ⟨2775, 0⟩` at elaboration, defines
`def isWriteCode : Code := <the code, a constructor application>`, and defines
`def isWriteCode_ok : Bool := EqB.eqB (Engine.P'.alg ⟨2775, 0⟩) (some isWriteCode)`. The engine runs these checks
at runtime (`Engine.Pins`) and enables the accelerator table only when all pass, giving `Engine.Pins.pin` equations
without `native_decide`. `pin_prog_alg_def` is the same for `Engine.P.alg`, an `Ecma.Alg`.

A module that defines a pin imports this one, and `public meta import Engine.Machine` (elaboration evaluates `pin_lit%`).
-/

namespace Engine.Pins
open Lean Elab Term Meta

/-- A type whose values `pin_lit%` writes: the type, and the literal of an `Option` of it that is `some`. -/
meta def pinned (α : Type) [ToExpr α] : Expr × (Expr → TermElabM Expr) :=
  (toTypeExpr α, fun e => do
    let v ← unsafe evalExpr (Option α) (toTypeExpr (Option α)) e
    match v with
    | some v => return toExpr v
    | none => throwError "pin: {e} is none")

/-- The types `pin_lit%` writes. -/
meta def pinnedTypes : List (Expr × (Expr → TermElabM Expr)) :=
  [pinned Ecma.Machine.Code, pinned Ecma.Alg, pinned Ecma.SdoRow, pinned (List Nat × Ecma.Machine.Code),
   pinned (Nat × Ecma.Machine.Code), pinned (List Ecma.Machine.RowCode)]

/-- `pin_lit% e`: where `e : Option T` evaluates to `some v`, the literal of `v`. -/
syntax (name := pinLit) "pin_lit% " term : term

@[term_elab pinLit] meta def elabPinLit : TermElab := fun stx _ => do
  let e ← elabTerm stx[1] none
  synthesizeSyntheticMVarsNoPostponing
  let e ← instantiateMVars e
  let ty ← inferType e
  for (t, lit) in pinnedTypes do
    if ← isDefEq ty (mkApp (mkConst ``Option [Level.zero]) t) then return ← lit e
  throwError "pin: no literal of a value of type {ty}"

/-- `pin_def x : T := e`: `def x : T`, the literal of the value in `e : Option T`, and `def x_ok : Bool`,
the equality test `EqB.eqB e (some x)`. -/
syntax "pin_def " ident " : " term " := " term : command

macro_rules
  | `(pin_def $x:ident : $t:term := $e:term) =>
    let ok := mkIdentFrom x (x.getId.appendAfter "_ok")
    `(def $x : $t := pin_lit% $e
      def $ok : Bool := EqB.eqB $e (some $x))

/-- `pin_alg_def x a`: `def x : Code`, algorithm `a`'s code, and `def x_ok : Bool`. -/
macro "pin_alg_def " x:ident a:term:max : command => `(pin_def $x : Ecma.Machine.Code := Engine.P'.alg $a)

/-- `pin_prog_alg_def x a`: `def x : Alg`, algorithm `a`, and `def x_ok : Bool`. -/
macro "pin_prog_alg_def " x:ident a:term:max : command => `(pin_def $x : Ecma.Alg := Engine.P.alg $a)

end Engine.Pins
