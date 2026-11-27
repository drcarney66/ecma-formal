module

public import Engine.Proofs.Step.Sym.Basic

@[expose] public section

/-!
# Symbolic execution: a loop's round's head

The transition at a round's head branches on the iterator's state: a lemma for the round that runs (`_lt`,
`_in`: the body, the variable bound) and one for the loop's end (`_end`), for `Repeat n times`
(`step_times_lt`, `step_times_end`), an ascending range (`step_range_in`, `step_range_end`) and `For each
element of` a List (`step_each_in`, `step_each_end`). Each is stated at any path and round counter, as a
loop's induction needs them. A `Repeat, while` round's head computes: `gsteps` to its condition's value,
then `Steps.valBool`.
-/

namespace Engine.Machine

open Ecma Ecma.Machine

/-- `Repeat n times`: the round's head while rounds are left. -/
theorem step_times_lt (X : Ctx F) (s : State F) (fr : List (Frame F)) (o : Op) (p : List Nat) (body : Code)
    (i n : Int) (r : Nat) (h : i < n) :
    step X ⟨s, fr, .loop .round ⟨none, .times o, p, body, .times (.int i) (.int n), r⟩⟩ =
      loopBody ⟨s, fr, .loop .round ⟨none, .times o, p, body, .times (.int i) (.int n), r⟩⟩
        ⟨none, .times o, p, body, .times (.int (i + 1)) (.int n), r⟩ := by
  have hl : Model.MathVal.lt (.int i) (.int n) = true := by simp [Model.MathVal.lt, h]
  simp [step, loopStep, iterNext, bindR, hl, Run.pure]
  rfl

/-- `Repeat n times`: the round's head with no round left. -/
theorem step_times_end (X : Ctx F) (s : State F) (fr : List (Frame F)) (o : Op) (p : List Nat) (body : Code)
    (i n : Int) (r : Nat) (h : ¬ i < n) :
    step X ⟨s, fr, .loop .round ⟨none, .times o, p, body, .times (.int i) (.int n), r⟩⟩ =
      loopEnd ⟨s, fr, .loop .round ⟨none, .times o, p, body, .times (.int i) (.int n), r⟩⟩
        ⟨none, .times o, p, body, .times (.int i) (.int n), r⟩ := by
  have hl : Model.MathVal.lt (.int i) (.int n) = false := by simp [Model.MathVal.lt, h]
  simp [step, loopStep, iterNext, bindR, hl, Run.pure]

/-- An ascending range's round's head while its variable is in the range: the variable bound, the body. -/
theorem step_range_in (X : Ctx F) (s : State F) (fr : List (Frame F)) (x : Slot) (o1 o2 : Op) (li hi : Bool)
    (p : List Nat) (body : Code) (i lo h : Int) (r : Nat) (h1 : ¬ i < lo) (h2 : ¬ h < i) :
    step X ⟨s, fr, .loop .round ⟨some x, .range o1 o2 li hi false, p, body, .range (.int i) (.int lo) (.int h) false, r⟩⟩ =
      loopBody ((⟨s, fr, .loop .round
          ⟨some x, .range o1 o2 li hi false, p, body, .range (.int i) (.int lo) (.int h) false, r⟩⟩ : Cfg F).setSlot x
          (.math (.int i)))
        ⟨some x, .range o1 o2 li hi false, p, body, .range (.int (i + 1)) (.int lo) (.int h) false, r⟩ := by
  have hl : Model.MathVal.lt (.int i) (.int lo) = false := by simp [Model.MathVal.lt, h1]
  have hh : Model.MathVal.lt (.int h) (.int i) = false := by simp [Model.MathVal.lt, h2]
  simp [step, loopStep, iterNext, bindR, hl, hh, Run.pure]
  rfl

/-- An ascending range's round's head with its variable past the range: the loop's end. -/
theorem step_range_end (X : Ctx F) (s : State F) (fr : List (Frame F)) (x : Option Slot) (o1 o2 : Op) (li hi : Bool)
    (p : List Nat) (body : Code) (i lo h : Int) (r : Nat) (h2 : h < i) :
    step X ⟨s, fr, .loop .round ⟨x, .range o1 o2 li hi false, p, body, .range (.int i) (.int lo) (.int h) false, r⟩⟩ =
      loopEnd ⟨s, fr, .loop .round ⟨x, .range o1 o2 li hi false, p, body, .range (.int i) (.int lo) (.int h) false, r⟩⟩
        ⟨x, .range o1 o2 li hi false, p, body, .range (.int i) (.int lo) (.int h) false, r⟩ := by
  have hh : Model.MathVal.lt (.int h) (.int i) = true := by simp [Model.MathVal.lt, h2]
  simp [step, loopStep, iterNext, bindR, hh, Run.pure]

/-- A `For each` round's head at an element of the List: the variable bound to it, the body. -/
theorem step_each_in (X : Ctx F) (s : State F) (fr : List (Frame F)) (x : Slot) (o1 : Op) (p : List Nat)
    (body : Code) (l : Nat) (xs : Array (Val F)) (o : Nat) (i : Nat) (r : Nat) (v : Val F)
    (hl : s.heap.get l = some (.list xs o)) (hv : xs[i]? = some v) :
    step X ⟨s, fr, .loop .round ⟨some x, .each o1 false, p, body, .each l (.int i) false, r⟩⟩ =
      loopBody ((⟨s, fr, .loop .round ⟨some x, .each o1 false, p, body, .each l (.int i) false, r⟩⟩ : Cfg F).setSlot x v)
        ⟨some x, .each o1 false, p, body, .each l (.int ((i + 1 : Nat) : Int)) false, r⟩ := by
  have hi : i < xs.size := by
    rcases Nat.lt_or_ge i xs.size with h' | h'
    · exact h'
    · simp [Array.getElem?_eq_none h'] at hv
  have hv' : xs[i] = v := by simpa [Array.getElem?_eq_getElem hi] using hv
  simp [step, loopStep, iterNext, bindR, readCell, hl, Model.MathVal.lt, Model.MathVal.idx, hv', hi, Run.pure,
    Model.MathVal.add, bind, Run.bind, Run.Res.bind, Nat.not_le.mpr hi]

/-- A `For each` round's head past the List's elements: the loop's end. -/
theorem step_each_end (X : Ctx F) (s : State F) (fr : List (Frame F)) (x : Option Slot) (o1 : Op) (p : List Nat)
    (body : Code) (l : Nat) (xs : Array (Val F)) (o : Nat) (i : Nat) (r : Nat)
    (hl : s.heap.get l = some (.list xs o)) (hi : ¬ i < xs.size) :
    step X ⟨s, fr, .loop .round ⟨x, .each o1 false, p, body, .each l (.int i) false, r⟩⟩ =
      loopEnd ⟨s, fr, .loop .round ⟨x, .each o1 false, p, body, .each l (.int i) false, r⟩⟩
        ⟨x, .each o1 false, p, body, .each l (.int i) false, r⟩ := by
  have hlt : Model.MathVal.lt (.int i) (.int xs.size) = false := by simp [Model.MathVal.lt, hi]
  simp [step, loopStep, iterNext, bindR, bind, Run.bind, readCell, hl, Run.Res.bind, hlt, Run.pure]

end Engine.Machine
