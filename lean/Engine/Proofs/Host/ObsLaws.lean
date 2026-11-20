module

public import Ecma.Model.Laws

@[expose] public section

/-!
# Numerals under the model's laws

From `Model.Laws` (the spec's laws of mathematical values): 0 is a left identity, addition cancels, and the
numerals `M.ofNat n` are ordered, and distinct, as the natural numbers are.
-/

namespace Ecma

variable {M : Model} {α : Type}

namespace Model.Laws

variable (L : M.Laws)
include L

/-- 0 is a left identity. -/
theorem zero_add (a : M.Math) : M.add (M.ofNat 0) a = a := by rw [L.add_comm, L.add_zero]

/-- Addition cancels on the right. -/
theorem add_cancel {a b c : M.Math} (h : M.add a c = M.add b c) : a = b := by
  have h' := congrArg (fun x => M.add x (M.neg c)) h
  simpa only [L.add_assoc, L.add_neg, L.add_zero] using h'

/-- x · 0 = 0. -/
theorem mul_zero (a : M.Math) : M.mul a (M.ofNat 0) = M.ofNat 0 := by
  have h : M.add (M.mul a (M.ofNat 0)) (M.mul a (M.ofNat 0)) = M.add (M.ofNat 0) (M.mul a (M.ofNat 0)) := by
    rw [← L.mul_add, L.add_zero, zero_add L]
  exact add_cancel L h

/-- (-1) · (-1) = 1. -/
theorem neg_one_mul_neg_one : M.mul (M.neg (M.ofNat 1)) (M.neg (M.ofNat 1)) = M.ofNat 1 := by
  have h := L.mul_add (M.neg (M.ofNat 1)) (M.ofNat 1) (M.neg (M.ofNat 1))
  rw [L.add_neg, mul_zero L, L.mul_one] at h
  apply add_cancel L (c := M.neg (M.ofNat 1))
  rw [L.add_comm (M.mul _ _) (M.neg _), ← h, L.add_neg]

/-- 0 < 1. -/
theorem zero_lt_one : M.lt (M.ofNat 0) (M.ofNat 1) = true := by
  rcases L.lt_total (M.ofNat 0) (M.ofNat 1) with h | h | h
  · exact h
  · exact absurd h L.zero_ne_one
  · have h1 := L.add_lt_add _ _ (M.neg (M.ofNat 1)) h
    rw [L.add_neg, zero_add L] at h1
    have h2 := L.mul_pos _ _ h1 h1
    rw [neg_one_mul_neg_one L] at h2
    have h3 := L.lt_trans _ _ _ h h2
    rw [L.lt_irrefl] at h3
    cases h3

/-- x < x + 1. -/
theorem lt_add_one (a : M.Math) : M.lt a (M.add a (M.ofNat 1)) = true := by
  have h := L.add_lt_add _ _ a (zero_lt_one L)
  rwa [zero_add L, L.add_comm (M.ofNat 1)] at h

/-- Numerals are ordered as natural numbers. -/
theorem ofNat_lt_of_lt {m n : Nat} (h : m < n) : M.lt (M.ofNat m) (M.ofNat n) = true := by
  induction n with
  | zero => exact absurd h (Nat.not_lt_zero _)
  | succ n ih =>
    have hs : M.lt (M.ofNat n) (M.ofNat (n + 1)) = true := by rw [L.ofNat_add]; exact lt_add_one L _
    rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ h) with h | rfl
    · exact L.lt_trans _ _ _ (ih h) hs
    · exact hs

/-- Numerals are ordered exactly as natural numbers. -/
theorem ofNat_lt_iff {m n : Nat} : M.lt (M.ofNat m) (M.ofNat n) = true ↔ m < n := by
  refine ⟨fun h => ?_, ofNat_lt_of_lt L⟩
  rcases Nat.lt_or_ge m n with hmn | hmn
  · exact hmn
  · rcases Nat.lt_or_eq_of_le hmn with hnm | rfl
    · have h' := L.lt_trans _ _ _ h (ofNat_lt_of_lt L hnm)
      rw [L.lt_irrefl] at h'
      cases h'
    · rw [L.lt_irrefl] at h
      cases h

/-- Distinct naturals are distinct numerals. -/
theorem ofNat_inj {m n : Nat} (h : M.ofNat m = M.ofNat n) : m = n := by
  rcases Nat.lt_trichotomy m n with hmn | hmn | hmn
  · have h' := ofNat_lt_of_lt L hmn
    rw [h, L.lt_irrefl] at h'
    cases h'
  · exact hmn
  · have h' := ofNat_lt_of_lt L hmn
    rw [h, L.lt_irrefl] at h'
    cases h'

end Model.Laws

end Ecma
