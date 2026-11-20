module

public import Engine.Proofs.Binary64Round

@[expose] public section

/-!
# Binary64's operations meet the Number laws

Over ℚ, through `viewQ`: `neg`, `add`, `sub`, `mul`, `div`, `lt` and `eq` meet `Model.NumLaws`' view
laws, with `realQ` for `Model.realOf` and `ofRat` for "the Number value for x".
-/

namespace Engine.Binary64

theorem viewQ_qNaN : viewQ qNaN = .nan := by simp only [viewQ, show isNaN qNaN = true by decide, if_true]
theorem viewQ_posInfinity : viewQ posInfinity = .posInf := viewQ_inf false
theorem viewQ_negInfinity : viewQ negInfinity = .negInf := viewQ_inf true
theorem viewQ_posZero : viewQ posZero = .posZero := by
  simp only [viewQ, show isNaN posZero = false by decide, show isFinite posZero = true by decide,
    show isZero posZero = true by decide, show sign posZero = false by decide]; rfl
theorem viewQ_negZero : viewQ negZero = .negZero := by
  simp only [viewQ, show isNaN negZero = false by decide, show isFinite negZero = true by decide,
    show isZero negZero = true by decide, show sign negZero = true by decide]; rfl

theorem isNegZero_of {a : BitVec 64} (h : isZero a = false) : isNegZero a = false := by
  unfold isNegZero; cases h' : a == negZero
  · rfl
  · rw [beq_iff_eq] at h'; subst h'; exact absurd h (by decide)

/-- What a pattern's view fixes: NaN, one of four patterns, or a finite non-zero value with its sign. -/
theorem viewQ_cases (a : BitVec 64) :
    (viewQ a = .nan ∧ isNaN a = true) ∨ (viewQ a = .posInf ∧ a = posInfinity) ∨
      (viewQ a = .negInf ∧ a = negInfinity) ∨ (viewQ a = .posZero ∧ a = posZero) ∨
      (viewQ a = .negZero ∧ a = negZero) ∨
      (∃ m, viewQ a = .finite m ∧ isNaN a = false ∧ isInfinite a = false ∧ isFinite a = true ∧
        isZero a = false ∧ isNegZero a = false ∧ a ≠ posInfinity ∧ a ≠ negInfinity ∧ toRat a = m ∧ m ≠ 0 ∧
        sign a = decide (m < 0)) := by
  have hf := fraction_lt a; have he := biasedExponent_lt a
  by_cases h1 : isNaN a = true
  · exact .inl ⟨by simp [viewQ, h1], h1⟩
  have h1' : isNaN a = false := by simpa using h1
  by_cases h2 : isFinite a = false
  · have hfr : biasedExponent a = 2047 ∧ fraction a = 0 := by
      simp only [isNaN, isFinite, Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq, bne_eq_false_iff_eq] at h1 h2
      exact ⟨h2, by omega⟩
    cases hs : sign a
    · refine .inr (.inl ⟨by simp [viewQ, h1', h2, hs], eq_of_fields ?_ ?_ ?_⟩) <;>
        simp only [hs, hfr] <;> decide
    · refine .inr (.inr (.inl ⟨by simp [viewQ, h1', h2, hs], eq_of_fields ?_ ?_ ?_⟩)) <;>
        simp only [hs, hfr] <;> decide
  have h2' : isFinite a = true := by simpa using h2
  by_cases h3 : isZero a = true
  · have hfr : biasedExponent a = 0 ∧ fraction a = 0 := by
      simpa only [isZero, Bool.and_eq_true, beq_iff_eq] using h3
    cases hs : sign a
    · refine .inr (.inr (.inr (.inl ⟨by simp [viewQ, h1', h2', h3, hs], eq_of_fields ?_ ?_ ?_⟩))) <;>
        simp only [hs, hfr] <;> decide
    · refine .inr (.inr (.inr (.inr (.inl ⟨by simp [viewQ, h1', h2', h3, hs], eq_of_fields ?_ ?_ ?_⟩)))) <;>
        simp only [hs, hfr] <;> decide
  have h3' : isZero a = false := by simpa using h3
  obtain ⟨hform, hb⟩ := toRat_form h2' h3'
  have hpos : 0 < (mant a : Rat) * pow2 ((kexp a : Int) - 1074) :=
    Rat.mul_pos (Rat.natCast_pos.2 (by omega)) (pow2_pos _)
  refine .inr (.inr (.inr (.inr (.inr ⟨toRat a, by simp [viewQ, h1', h2', h3'], h1', ?_, h2', h3', isNegZero_of h3',
    fun h => by subst h; exact absurd h2' (by decide), fun h => by subst h; exact absurd h2' (by decide), rfl,
    (finiteQ_bounds (toRat_finiteQ h2' h3')).1, ?_⟩))))
  · simp only [isInfinite, isFinite, bne_iff_ne, ne_eq] at h2' ⊢; simp [h2']
  · rw [hform, formQ_eq, signed_mul_pos hpos]


/-- `Model.realOf` over ℚ. -/
def realQ : Ecma.NumView Rat → Option Rat
  | .finite m => some m
  | .posZero => some 0
  | .negZero => some 0
  | _ => none

/-- Negation's fields: the sign flips. -/
theorem neg_fields {a : BitVec 64} (h : isNaN a = false) :
    sign (neg a) = !sign a ∧ biasedExponent (neg a) = biasedExponent a ∧ fraction (neg a) = fraction a := by
  have ht : (neg a).toNat = (a.toNat + 2 ^ 63) % 2 ^ 64 := by
    simp only [neg, h, Bool.false_eq_true, if_false, BitVec.toNat_ofNat, Nat.mod_mod]
  have := a.isLt
  unfold sign biasedExponent fraction
  rw [BitVec.msb_eq_decide, BitVec.msb_eq_decide, ht]
  by_cases h1 : 2 ^ 63 ≤ a.toNat <;> simp [h1, Nat.shiftLeft_eq] <;> omega

/-- (c) negation flips the sign; NaN stays. -/
theorem neg_view (a : BitVec 64) : viewQ (neg a) = match viewQ a with
    | .nan => .nan | .posInf => .negInf | .negInf => .posInf
    | .posZero => .negZero | .negZero => .posZero | .finite m => .finite (-m) := by
  rcases viewQ_cases a with ⟨ha, hn⟩ | ⟨ha, rfl⟩ | ⟨ha, rfl⟩ | ⟨ha, rfl⟩ | ⟨ha, rfl⟩ |
      ⟨m, ha, hn, -, hfin, hz, -, -, -, hm, -, -⟩ <;> rw [ha]
  · simp only [neg, hn, if_true, viewQ_qNaN]
  · rw [show neg posInfinity = negInfinity by decide, viewQ_negInfinity]
  · rw [show neg negInfinity = posInfinity by decide, viewQ_posInfinity]
  · rw [show neg posZero = negZero by decide, viewQ_negZero]
  · rw [show neg negZero = posZero by decide, viewQ_posZero]
  · obtain ⟨hs, he, hf⟩ := neg_fields hn
    have hn' : isNaN (neg a) = false := by simp only [isNaN, he, hf]; exact hn
    have hfin' : isFinite (neg a) = true := by simp only [isFinite, he]; exact hfin
    have hz' : isZero (neg a) = false := by simp only [isZero, he, hf]; exact hz
    have ht : toRat (neg a) = -toRat a := by
      rw [toRat_of_finite hfin, toRat_of_finite hfin', neg_signed]
      simp only [mant, kexp, he, hf, hs]
    simp only [viewQ, hn', hfin', hz', ht, hm]; rfl


theorem toRat_posZero : toRat posZero = 0 := by decide
theorem toRat_negZero : toRat negZero = 0 := by decide
theorem viewQ_ofRat_zero : viewQ (ofRat 0) = .posZero := by rw [ofRat_zero, viewQ_posZero]

/-- An exact zero rounds to +0. -/
theorem ofRat_ite (s : Rat) : (if s = 0 then .posZero else viewQ (ofRat s)) = viewQ (ofRat s) := by
  split
  · rename_i h; rw [h, ofRat_zero, viewQ_posZero]
  · rfl

theorem viewQ_zero (s : Bool) : viewQ (zero s) = if s then .negZero else .posZero := by
  cases s <;> simp only [zero, if_true, if_false, Bool.false_eq_true, viewQ_posZero, viewQ_negZero]

theorem viewQ_infinity (s : Bool) : viewQ (infinity s) = if s then .negInf else .posInf := by
  cases s <;> simp only [infinity, if_true, if_false, Bool.false_eq_true, viewQ_posInfinity, viewQ_negInfinity]

theorem zero_divQ (y : Rat) : 0 / y = 0 := by rw [Rat.div_def, Rat.zero_mul]

theorem div_eq_zero {x y : Rat} : x / y = 0 ↔ x = 0 ∨ y = 0 := by
  by_cases hy : y = 0
  · subst hy; simp only [or_true, iff_true]; rw [Rat.div_def, Rat.inv_zero, Rat.mul_zero]
  refine ⟨fun h => .inl ?_, fun h => ?_⟩
  · have : x / y * y = x := by
      rw [Rat.div_def, Rat.mul_assoc, Rat.mul_comm _ y, Rat.mul_inv_cancel _ hy, Rat.mul_one]
    rw [← this, h, Rat.zero_mul]
  · rcases h with h | h
    · rw [h, zero_divQ]
    · exact absurd h hy

theorem sign_posInfinity : sign posInfinity = false := by decide
theorem sign_negInfinity : sign negInfinity = true := by decide
theorem sign_posZero : sign posZero = false := by decide
theorem sign_negZero : sign negZero = true := by decide

theorem beq_dec {α} [BEq α] [LawfulBEq α] [DecidableEq α] (x y : α) : (x == y) = decide (x = y) := by
  by_cases h : x = y <;> simp [h]

/-- Split two patterns by their views. -/
local macro "view_cases " a:ident b:ident : tactic => `(tactic|
  (rcases viewQ_cases $a with ⟨ha, hna⟩ | ⟨ha, rfl⟩ | ⟨ha, rfl⟩ | ⟨ha, rfl⟩ | ⟨ha, rfl⟩ |
      ⟨x, ha, hna, hia, hfa, hza, hnza, hpa, hma, hx, hx0, hsa⟩ <;>
    rcases viewQ_cases $b with ⟨hb, hnb⟩ | ⟨hb, rfl⟩ | ⟨hb, rfl⟩ | ⟨hb, rfl⟩ | ⟨hb, rfl⟩ |
      ⟨y, hb, hnb, hib, hfb, hzb, hnzb, hpb, hmb, hy, hy0, hsb⟩) <;>
    (try have := Ne.symm hpa) <;> (try have := Ne.symm hma) <;> (try have := Ne.symm hpb) <;>
    (try have := Ne.symm hmb))

/-- Evaluate an operation's case on its operands' views. -/
local macro "view_simp" : tactic => `(tactic|
  simp (config := {decide := true}) only [realQ, viewQ_qNaN, viewQ_posInfinity, viewQ_negInfinity,
    viewQ_negZero, viewQ_posZero, toRat_posZero, toRat_negZero, ofRat_zero, ofRat_ite, sign_posInfinity,
    sign_negInfinity, sign_posZero, sign_negZero, beq_dec, viewQ_zero, viewQ_infinity, Rat.mul_eq_zero,
    div_eq_zero, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Rat.zero_add, Rat.add_zero,
    Rat.zero_mul, Rat.mul_zero, zero_divQ, Bool.true_or, Bool.or_true, Bool.false_or, Bool.or_false, if_true,
    if_false, or_false, false_or, beq_self_eq_true, beq_iff_eq, decide_eq_true_eq, decide_eq_false_iff_not,
    not_false_eq_true, *])

set_option linter.unusedSimpArgs false in
/-- (c) addition: NumLaws.numAdd_view, finite sums rounded, an exact zero +0 unless both are −0. -/
theorem add_view (a b : BitVec 64) : viewQ (add a b) = match viewQ a, viewQ b with
    | .nan, _ => .nan | _, .nan => .nan
    | .posInf, .negInf => .nan | .negInf, .posInf => .nan
    | .posInf, _ => .posInf | .negInf, _ => .negInf
    | _, .posInf => .posInf | _, .negInf => .negInf
    | .negZero, .negZero => .negZero
    | va, vb => match realQ va, realQ vb with
      | some x, some y => if x + y = 0 then .posZero else viewQ (ofRat (x + y))
      | _, _ => .nan := by
  unfold add; view_cases a b <;> view_simp <;> done

set_option linter.unusedSimpArgs false in
/-- (c) multiplication: NumLaws.numMul_view, ∞ × 0 NaN, the signs' product, finite products rounded. -/
theorem mul_view (a b : BitVec 64) : viewQ (mul a b) = match viewQ a, viewQ b with
    | .nan, _ => .nan | _, .nan => .nan
    | .posInf, .posZero => .nan | .posInf, .negZero => .nan | .negInf, .posZero => .nan
    | .negInf, .negZero => .nan | .posZero, .posInf => .nan | .negZero, .posInf => .nan
    | .posZero, .negInf => .nan | .negZero, .negInf => .nan
    | va, vb =>
      let neg := (match va with | .negInf | .negZero => true | .finite m => decide (m < 0) | _ => false) !=
        (match vb with | .negInf | .negZero => true | .finite m => decide (m < 0) | _ => false)
      match realQ va, realQ vb with
      | some x, some y =>
        if x * y = 0 then (if neg then .negZero else .posZero)
        else viewQ (ofRat (x * y))
      | _, _ => if neg then .negInf else .posInf := by
  unfold mul; view_cases a b <;> view_simp <;> done

set_option linter.unusedSimpArgs false in
/-- (c) division: NumLaws.numDiv_view, ∞/∞ and 0/0 NaN, x/±0 a signed ∞, finite/∞ a signed 0. -/
theorem div_view (a b : BitVec 64) : viewQ (div a b) = match viewQ a, viewQ b with
    | .nan, _ => .nan | _, .nan => .nan
    | .posInf, .posInf => .nan | .posInf, .negInf => .nan | .negInf, .posInf => .nan
    | .negInf, .negInf => .nan
    | .posZero, .posZero => .nan | .posZero, .negZero => .nan | .negZero, .posZero => .nan
    | .negZero, .negZero => .nan
    | va, vb =>
      let neg := (match va with | .negInf | .negZero => true | .finite m => decide (m < 0) | _ => false) !=
        (match vb with | .negInf | .negZero => true | .finite m => decide (m < 0) | _ => false)
      match va, vb with
      | .posInf, _ | .negInf, _ => if neg then .negInf else .posInf
      | _, .posInf | _, .negInf => if neg then .negZero else .posZero
      | _, .posZero | _, .negZero => if neg then .negInf else .posInf
      | _, _ => match realQ va, realQ vb with
        | some x, some y =>
          if x / y = 0 then (if neg then .negZero else .posZero)
          else viewQ (ofRat (x / y))
        | _, _ => .nan := by
  unfold div; view_cases a b <;> view_simp <;> done

set_option linter.unusedSimpArgs false in
/-- (c) compareQuietLess: false with NaN; −0 is not less than +0. -/
theorem lt_view (a b : BitVec 64) : lt a b = match viewQ a, viewQ b with
    | .nan, _ => false | _, .nan => false
    | .negInf, .negInf => false | .negInf, _ => true
    | _, .negInf => false | .posInf, _ => false | _, .posInf => true
    | va, vb => match realQ va, realQ vb with
      | some x, some y => decide (x < y)
      | _, _ => false := by
  unfold lt; view_cases a b <;> view_simp <;> done

set_option linter.unusedSimpArgs false in
/-- (c) compareQuietEqual: false with NaN; +0 equals −0. -/
theorem eq_view (a b : BitVec 64) : eq a b = match viewQ a, viewQ b with
    | .nan, _ => false | _, .nan => false
    | .posInf, .posInf => true | .negInf, .negInf => true
    | va, vb => match realQ va, realQ vb with
      | some x, some y => decide (x = y)
      | _, _ => false := by
  unfold eq; view_cases a b <;> view_simp <;> done

end Engine.Binary64
