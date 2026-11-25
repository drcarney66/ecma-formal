module

public import Ecma.Implements
public import Engine.Machine

@[expose] public section

/-!
# Runs

`Ecma.Implements.run_sound`: every run of an implementation of the specification, from a configuration the
specification's machine reaches, is a run of that machine, or ends at the implementation's limit. By induction on
the run, with the configurations reached closed under the machine's transitions (`Reached.steps`).

`Engine.Machine.runT_runs`: a run the engine's loop returns is a run of the engine's transition (`stepE`): the
loop's observers are the identity to the logic (`stepObs_eq`), and the loop's partial correctness
(`runT.partial_correctness`, Lean's for a `partial_fixpoint`) gives the run.
-/

namespace Ecma

open Machine

variable {M : Model}

theorem Machine.Steps.append {X : Ctx M} {c c' c'' : Cfg M} (h : Steps X c c') (h' : Steps X c' c'') :
    Steps X c c'' := by
  induction h with
  | refl => exact h'
  | step hs _ ih => exact .step hs (ih h')

/-- The configurations reached are closed under the machine's transitions. -/
theorem Reached.steps {X : Ctx M} {c c' : Cfg M} (hc : Reached X c) (h : Steps X c c') : Reached X c' := by
  induction h with
  | refl => exact hc
  | step hs _ ih => exact ih (.step hc hs)

/-- **Every run of an implementation is the specification's**: from a configuration the specification's machine
reaches, a run of `I` that ends with `f` is a run of that machine that ends with `f`, or `I` gave up at a limit of
its own. -/
theorem Implements.run_sound {I : Implementation M} (hI : Implements I) {chk : Bool}
    {c : Cfg M} {f : Final M} (hc : Reached (I.spec chk) c) (h : I.Runs chk c f) :
    Runs (I.spec chk) c f ∨ f = .stop .implLimit := by
  induction h with
  | ends he =>
    have := hI.step chk _ hc
    rw [he] at this
    exact this
  | step hs _ ih =>
    have := hI.step chk _ hc
    rw [hs] at this
    rcases ih (hc.steps this) with ⟨c'', h1, h2⟩ | h
    · exact .inl ⟨c'', this.append h1, h2⟩
    · exact .inr h

end Ecma

namespace Engine.Machine

open Ecma Ecma.Machine

theorem traced_eq (units : Thunk Units) (c : Cfg F) (k : Unit → Out F) :
    traced units c k = k () := by
  unfold traced
  split
  · rfl
  · split <;> rfl

/-- The loop's transition, whatever it keeps, is the engine's. -/
theorem stepObs_eq (E : Setup) (units : Thunk Units) (ob : Obs) (c : Cfg F) : stepObs E units ob c = stepE E c := by
  unfold stepObs stepE
  cases E.full c
  · simp only [Bool.false_eq_true, ↓reduceIte, traced_eq, noteOut, noteStep, ite_self]
  · rfl

/-- A run the loop returns is a run of an implementation whose transition is the loop's set-up's. -/
theorem runT_runs (I : Implementation F) (chk : Bool) (E : Setup)
    (hI : ∀ c, I.step chk c = stepE E c) (units : Thunk Units) (ob : Obs) (c : Cfg F) (f : Final F)
    (h : runT E units ob c = some f) : I.Runs chk c f := by
  refine runT.partial_correctness E units ob (I.Runs chk) (fun _ ih c r h => ?_) c f h
  rw [stepObs_eq] at h
  split at h
  · exact .step (by rw [hI]; assumption) (ih _ _ h)
  · cases h
    exact .ends (by rw [hI]; assumption)

end Engine.Machine
