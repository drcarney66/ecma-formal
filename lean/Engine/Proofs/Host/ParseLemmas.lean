module

public import Engine.Model.Parse

@[expose] public section

/-! # ParseText's parse at Impl at a non-numeric goal: the parser's tree, restamped -/

namespace Engine.Impl

open Engine.Model Ecma.Grammar
open Ecma (ProdId NtId ParamId ParseCx)

/-- At a non-numeric goal, a Parse Node `parse` gives is the parser's, restamped. -/
theorem parse_some {cx : ParseCx} {st : Nat} {src : Array MathVal} {goal : NtId}
    {args : List (ParamId × Bool)} {m : Node}
    (hg : (goal == NT.StringNumericLiteral.ctorIdx || goal == NT.StringIntegerLiteral.ctorIdx) = false)
    (h : parse cx st src goal args = some (some m)) :
    ∃ n, outcome 0 src goal args (grammarCx cx) cx.strict = .ok n ∧
      m = restamp st n := by
  unfold parse at h
  split at h
  · cases h
  rw [hg] at h
  simp only [Bool.false_eq_true, if_false] at h
  split at h
  · next n e => cases h; exact ⟨n, e, rfl⟩
  · cases h
  · cases h

end Engine.Impl
