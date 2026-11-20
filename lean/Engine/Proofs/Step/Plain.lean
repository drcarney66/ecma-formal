module

public import Engine.Machine

@[expose] public section

/-!
# The engine's step without its shortcuts

`stepA_plain`: over the set-up with no shortcut (`plain E`), the engine's transition is the specification's
(`Ecma.Machine.step`), or the stop at a power too large to compute (an implementation limit).
-/

namespace Engine.Machine

open Ecma Ecma.Machine

theorem ite_limit (b : Bool) (x y : Out F) (h : x = y ∨ x = .inr (.stop .implLimit)) :
    (if b = true then .inr (.stop .implLimit) else x) = y ∨
      (if b = true then (.inr (.stop .implLimit) : Out F) else x) = .inr (.stop .implLimit) := by
  cases b
  · exact h
  · exact .inr rfl

theorem orParseLimit_eq (b : Unit → Bool) (x y : Out F) (h : x = y) :
    orParseLimit b x = y ∨ orParseLimit b x = .inr (.stop .implLimit) := by
  subst h
  cases x with
  | inl _ => exact .inl rfl
  | inr f =>
    cases f <;> first | exact .inl rfl | (dsimp only [orParseLimit]; split <;> first | exact .inr rfl | exact .inl rfl)

/-- Without shortcuts the engine's transition is the specification's, or the stop at a limit. -/
theorem stepA_plain (E : Setup) (c : Cfg F) :
    stepA (plain E) c = step E.X c ∨ stepA (plain E) c = .inr (.stop .implLimit) := by
  unfold stepA
  refine ite_limit _ _ _ ?_
  simp only [plain]
  repeat' split
  all_goals first
    | exact .inl rfl
    | exact orParseLimit_eq _ _ _ rfl
    | (obtain ⟨s, fr, ctl⟩ := c; simp_all; done)

end Engine.Machine
