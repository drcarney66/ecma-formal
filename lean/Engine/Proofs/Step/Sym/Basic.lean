module

public import Engine.Machine
public import Ecma.Machine.Run
public import Engine.Proofs.Step.Kinds
public import Engine.Pins

@[expose] public section

/-!
# Symbolic execution of the machine: runs, the stepping tactics, reads

* `Steps.next`, `Steps.trans` join runs; `Steps.valBool`, `Steps.codeIf`, `Steps.castFrom` restate a
  configuration whose condition has been computed.
* `mstep`: one transition of the specification's machine by computation (`rfl`), the configuration then put in
  normal form. `gstep` is `mstep` guarded: it fails at a sort's test and at an algorithm's call, where `rfl`
  would try to compute the program's tables. `gsteps` repeats it, `gsteps_to` up to the configuration aimed at,
  `gsteps_round` up to a loop's round's head.
* A transition that branches on a value not known is a lemma: `step_var` (a bound variable's read), `step_field`
  (a field's read), and those of `Sym/Loops`, `Sym/Prims`, `Sym/Sorts`, `Sym/Store`.
* `mdecide` decides a comparison of integers a condition has computed to.
-/

namespace Engine.Machine

open Ecma Ecma.Machine

/-! ## Runs -/

theorem Steps.next {X : Ctx F} {c c' d : Cfg F} (h : step X c = .inl c') (k : Steps X c' d) : Steps X c d :=
  .step h k

theorem Steps.trans {X : Ctx F} {c c' d : Cfg F} (h : Steps X c c') (k : Steps X c' d) : Steps X c d := by
  induction h with
  | refl => exact k
  | step h _ ih => exact .step h (ih k)

theorem Steps.castFrom {X : Ctx F} {c c' d : Cfg F} (h : c = c') (k : Steps X c' d) : Steps X c d := h ▸ k

/-- A condition's value, computed. -/
theorem Steps.valBool {X : Ctx F} {s : State F} {fr : List (Frame F)} {b : Bool} {d : Cfg F} (b' : Bool)
    (h : b = b') (k : Steps X ⟨s, fr, .val (.bool b')⟩ d) : Steps X ⟨s, fr, .val (.bool b)⟩ d := h ▸ k

/-- A branch's condition, computed. -/
theorem Steps.codeIf {X : Ctx F} {s : State F} {fr : List (Frame F)} {b : Bool} (b' : Bool) {t e : Code} {d : Cfg F}
    (h : b = b') (k : Steps X ⟨s, fr, .code (if b' = true then t else e)⟩ d) :
    Steps X ⟨s, fr, .code (if b = true then t else e)⟩ d := h ▸ k

/-! ## Values -/

theorem used_math (m : Model.MathVal) : (Val.math m : Val F).used = .math m := rfl

theorem used_used (v : Val F) : v.used.used = v.used := by
  cases v <;> rfl

theorem used_bound {v : Val F} (hv : v ≠ .unbound) : v.used ≠ .unbound := by
  cases v <;> simp [Val.used] at hv ⊢

theorem utf16_empty : Model.utf16 "" = #[] := by
  first | rfl | decide | simp [Model.utf16]

theorem numeral_dec (n : Nat) : (mathOf.numeral (M := F) (Numeral.dec n)) = Model.MathVal.int (n : Int) := rfl

theorem numeral_hex (n : Nat) (w : String) :
    (mathOf.numeral (M := F) (Numeral.hex n w)) = Model.MathVal.int (n : Int) := rfl

/-! ## The stepping tactics -/

/-- One transition by computation, the configuration then put in normal form. -/
macro "mstep" : tactic => `(tactic| (
  refine Steps.next (by rfl) ?_
  try dsimp only [Cfg.atPath, Cfg.push, Cfg.mapTop, Cfg.setSlot, Cfg.pop, Cfg.top, List.headD, List.tail,
    Frame.get]
  try simp only [List.setIfInBounds_toArray, List.set_cons_succ, List.set_cons_zero, Array.getD_eq_getD_getElem?,
    List.getElem?_toArray, List.getElem?_cons_succ, List.getElem?_cons_zero, Option.getD_some]))

/-- `mstep`, but not at a sort's test or an algorithm's call: there `rfl` would try to compute the program's tables
(maximum recursion depth, an error and not a failure). It fails there, so `repeat gstep` stops. -/
macro "gstep" : tactic => `(tactic| (
  fail_if_success (show Steps _ ⟨_, _, .invoke (.sort _ _)⟩ _)
  fail_if_success (show Steps _ ⟨_, _, .invoke (.alg _ _)⟩ _)
  mstep
  try simp only [used_math]))

/-- Transitions by computation, up to a sort's test, an algorithm's call or one that branches on a value not
known. -/
macro "gsteps" : tactic => `(tactic| repeat gstep)

/-- Transitions by computation up to the configuration aimed at. -/
macro "gsteps_to" : tactic => `(tactic| repeat (first | exact Steps.refl _ | gstep))

/-- Transitions by computation up to a loop's round's head. -/
macro "gsteps_round" : tactic => `(tactic| repeat (
  fail_if_success (show Steps _ ⟨_, _, .loop .round _⟩ _)
  gstep))

/-- A comparison of integers, decided. -/
macro "mdecide" : tactic =>
  `(tactic| (simp [numeral_dec, numeral_hex, Model.MathVal.lt, Model.MathVal.eq, Model.MathVal.add, Model.MathVal.neg,
      Model.MathVal.mul] <;> omega))


/-- A read of a bound variable. -/
theorem step_var (X : Ctx F) (s : State F) (f : Frame F) (fs : List (Frame F)) (x : Slot) (w : Val F)
    (hx : f.get x = w) (hw : w ≠ .unbound) :
    step X ⟨s, f :: fs, .op (.var x)⟩ = .inl ⟨s, f :: fs, .val w⟩ := by
  have h : step X ⟨s, f :: fs, .op (.var x)⟩ = leafV ⟨s, f :: fs, .op (.var x)⟩ (Val.read (f.get x)) := rfl
  rw [h, hx]
  cases w <;> first | rfl | contradiction

/-- The machine's transition at a read of a field whose operand's value is known. -/
theorem step_field (X : Ctx F) (s : State F) (a : AlgId) (nd : Option F.Node) (sl : Array (Val F)) (kd : Kind)
    (p : List Nat) (K : List (Kont F)) (ci : Option Nat) (fs : List (Frame F)) (f : FieldId) (v w : Val F)
    (h : readField v f s = .ok w s) :
    step X ⟨s, ⟨a, nd, sl, kd, p, .args (.leaf (.field f)) [] [] :: K, ci⟩ :: fs, .val v⟩ =
      .inl ⟨s, ⟨a, nd, sl, kd, p, K, ci⟩ :: fs, .val w⟩ := by
  have e : step X ⟨s, ⟨a, nd, sl, kd, p, .args (.leaf (.field f)) [] [] :: K, ci⟩ :: fs, .val v⟩ =
      leafV ⟨s, ⟨a, nd, sl, kd, p, K, ci⟩ :: fs, .val v⟩ (readField v f) := rfl
  rw [e]
  simp only [leafV, bindR, h]
  rfl

end Engine.Machine
