module

public import Engine.Model.Binary64

@[expose] public section

/-!
# Binary64's value set meets the Number laws

Over ℚ: the decoding of a finite non-zero pattern through `toRat` is a member of §6.1.6.1's value set
(`Model.finiteNum`, mirrored by `finiteQ`), every member has a pattern, and `toRat` is injective
there; with the candidates of "the Number value for x" and rounding to an integer. `Binary64Round`
gives `ofRat`, `Binary64Ops` the operations.
-/

namespace Engine.Binary64

/-! ## Powers of two -/

theorem natCast_two_pow (n : Nat) : ((2 ^ n : Nat) : Rat) = (2 : Rat) ^ n := by
  rw [Lean.Grind.Semiring.natCast_pow]; rfl

/-- `pow2` is the integer power of 2. -/
theorem pow2_eq (e : Int) : pow2 e = (2 : Rat) ^ e := by
  unfold pow2; split
  · rename_i h
    obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le h
    simp [Rat.zpow_natCast]
  · rename_i h
    obtain ⟨n, hn⟩ := Int.exists_eq_neg_ofNat (by omega : e ≤ 0)
    subst hn
    simp [Rat.zpow_neg, Rat.zpow_natCast, Rat.div_def]

theorem pow2_add (a b : Int) : pow2 (a + b) = pow2 a * pow2 b := by
  simp only [pow2_eq]; exact Rat.zpow_add (by decide) a b

theorem pow2_nat (n : Nat) : pow2 n = (2 : Rat) ^ n := by
  rw [pow2_eq]; rfl

theorem pow2_pos (e : Int) : 0 < pow2 e := by
  rw [pow2_eq]; exact Rat.zpow_pos (by decide)

theorem pow2_ne (e : Int) : pow2 e ≠ 0 := Rat.ne_of_gt (pow2_pos e)

theorem one_le_two_pow (n : Nat) : (1 : Rat) ≤ (2 : Rat) ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [Rat.pow_succ]; grind

theorem pow2_lt_succ (e : Int) : pow2 e < pow2 (e + 1) := by
  rw [pow2_add, show pow2 1 = 2 by decide]; have := pow2_pos e; grind

theorem pow2_le_of_le {a b : Int} (h : a ≤ b) : pow2 a ≤ pow2 b := by
  obtain ⟨n, hn⟩ := Int.eq_ofNat_of_zero_le (by omega : 0 ≤ b - a)
  rw [show b = a + n by omega, pow2_add, pow2_nat]
  have := pow2_pos a; have := one_le_two_pow n
  have : pow2 a * 1 ≤ pow2 a * 2 ^ n := Rat.mul_le_mul_of_nonneg_left this (Rat.le_of_lt (pow2_pos a))
  grind

theorem pow2_lt_of_lt {a b : Int} (h : a < b) : pow2 a < pow2 b := by
  have := pow2_lt_succ a; have := pow2_le_of_le (show a + 1 ≤ b by omega); grind

theorem pow2_lt_iff {a b : Int} : pow2 a < pow2 b ↔ a < b :=
  ⟨fun h => Int.not_le.1 fun h' => Rat.not_le.2 h (pow2_le_of_le h'), pow2_lt_of_lt⟩

theorem pow2_le_iff {a b : Int} : pow2 a ≤ pow2 b ↔ a ≤ b :=
  ⟨fun h => Int.not_lt.1 fun h' => Rat.not_lt.2 h (pow2_lt_of_lt h'), pow2_le_of_le⟩

/-! ## Decoding -/

/-- v with a sign. -/
def signed (neg : Bool) (v : Rat) : Rat := if neg then -v else v

/-- The significand of a finite pattern: the fraction, with the implicit bit when normal. -/
def mant (b : BitVec 64) : Nat := if biasedExponent b = 0 then fraction b else fraction b + 2 ^ 52

/-- The `k` of `Model.form` for a finite pattern: e − 1 when normal, 0 when subnormal. -/
def kexp (b : BitVec 64) : Nat := if biasedExponent b = 0 then 0 else biasedExponent b - 1

theorem fraction_lt (b : BitVec 64) : fraction b < 2 ^ 52 := Nat.mod_lt _ (by decide)

theorem biasedExponent_lt (b : BitVec 64) : biasedExponent b < 2048 := Nat.mod_lt _ (by decide)

/-- A finite pattern's value: its sign, significand and exponent. -/
theorem toRat_of_finite {b : BitVec 64} (h : isFinite b = true) :
    toRat b = signed (sign b) ((mant b : Rat) * pow2 ((kexp b : Int) - 1074)) := by
  have hq : ((if biasedExponent b = 0 then (1 : Int) else biasedExponent b) - 1075) = (kexp b : Int) - 1074 := by
    unfold kexp; split <;> omega
  unfold toRat signed
  simp only [h, if_true]
  rw [hq]
  have hm : (if biasedExponent b = 0 then fraction b else fraction b + (1 <<< 52)) = mant b := by
    unfold mant; simp [Nat.shiftLeft_eq]
  simp only [hm]
  generalize (kexp b : Int) - 1074 = q
  have hv : (if 0 ≤ q then ((mant b <<< q.toNat : Nat) : Rat)
      else if mant b % (1 <<< (-q).toNat) = 0 then ((mant b >>> (-q).toNat : Nat) : Rat)
      else (mant b : Rat) * pow2 q) = (mant b : Rat) * pow2 q := by
    split
    · rename_i hq0
      rw [Nat.shiftLeft_eq, Rat.natCast_mul, natCast_two_pow, ← pow2_nat]
      congr 2; omega
    · rename_i hq0
      split
      · rename_i hd
        rw [Nat.shiftRight_eq_div_pow]
        rw [Nat.shiftLeft_eq, Nat.one_mul] at hd
        have hd' := Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero hd)
        have : ((mant b / 2 ^ (-q).toNat : Nat) : Rat) * pow2 ((-q).toNat) = mant b := by
          rw [pow2_nat, ← natCast_two_pow, ← Rat.natCast_mul, hd']
        have hp : pow2 q * pow2 ((-q).toNat) = 1 := by
          rw [← pow2_add, show q + ((-q).toNat : Int) = 0 by omega]; decide
        rw [← this, Rat.mul_assoc, Rat.mul_comm (pow2 _), hp, Rat.mul_one]
      · rfl
  rw [hv]

/-- The fields of an assembled pattern. -/
theorem pack_fields (neg : Bool) {e f : Nat} (he : e < 2048) (hf : f < 2 ^ 52) :
    sign (pack neg e f) = neg ∧ biasedExponent (pack neg e f) = e ∧ fraction (pack neg e f) = f := by
  have ht : (pack neg e f).toNat = (if neg then 2 ^ 63 else 0) + e * 2 ^ 52 + f := by
    unfold pack
    simp only [UInt64.toNat_toBitVec, UInt64.toNat_ofNat', Nat.shiftLeft_eq, Nat.one_mul]
    cases neg <;> simp <;> omega
  unfold sign biasedExponent fraction
  rw [BitVec.msb_eq_decide, ht]
  cases neg <;> simp [Nat.shiftLeft_eq] <;> omega

/-! ## The value set over ℚ -/

/-- `Model.form` over ℚ: ±m × 2^k / 2^1074. -/
def formQ (neg : Bool) (m k : Nat) : Rat := signed neg ((m : Rat) * 2 ^ k / 2 ^ 1074)

/-- `Model.finiteNum` over ℚ. -/
def finiteQ (x : Rat) (even : Bool) : Prop :=
  ∃ (neg : Bool) (m k : Nat), x = formQ neg m k ∧ (m % 2 == 0) = even ∧
    ((2 ^ 52 ≤ m ∧ m < 2 ^ 53 ∧ k ≤ 2045) ∨ (0 < m ∧ m < 2 ^ 52 ∧ k = 0))

/-- `Model.candidate` over ℚ. -/
def candQ (y : Rat) (even : Bool) : Prop :=
  finiteQ y even ∨ (y = 0 ∧ even = true) ∨ ((y = 2 ^ 1024 ∨ y = -(2 ^ 1024)) ∧ even = true)

/-- `Model.abs` over ℚ. -/
def absQ (x : Rat) : Rat := if x < 0 then -x else x

/-- `Model.nearest` over ℚ. -/
def nearestQ (x y : Rat) : Prop :=
  ∃ ev, candQ y ev ∧ ∀ z ez, candQ z ez →
    ¬ absQ (x - z) < absQ (x - y) ∧ (absQ (x - z) = absQ (x - y) → z ≠ y → ev = true)

theorem formQ_eq (neg : Bool) (m k : Nat) :
    formQ neg m k = signed neg ((m : Rat) * pow2 ((k : Int) - 1074)) := by
  have : pow2 ((k : Int) - 1074) * pow2 ((1074 : Nat) : Int) = pow2 k := by rw [← pow2_add]; congr 1; omega
  unfold formQ; congr 1
  rw [← pow2_nat, ← pow2_nat, ← this, Rat.div_def, Rat.mul_assoc, Rat.mul_assoc,
    Rat.mul_inv_cancel _ (pow2_ne _), Rat.mul_one]

/-- (a) A finite non-zero pattern's value is `form (sign b) (mant b) (kexp b)`, in the value set. -/
theorem toRat_form {b : BitVec 64} (h : isFinite b = true) (hz : isZero b = false) :
    toRat b = formQ (sign b) (mant b) (kexp b) ∧
      ((2 ^ 52 ≤ mant b ∧ mant b < 2 ^ 53 ∧ kexp b ≤ 2045) ∨ (0 < mant b ∧ mant b < 2 ^ 52 ∧ kexp b = 0)) := by
  refine ⟨by rw [toRat_of_finite h, formQ_eq], ?_⟩
  have := fraction_lt b; have := biasedExponent_lt b
  simp only [isFinite, isZero, bne_iff_ne, ne_eq, Bool.and_eq_false_iff, beq_eq_false_iff_ne] at h hz
  unfold mant kexp; split <;> omega

theorem toRat_finiteQ {b : BitVec 64} (h : isFinite b = true) (hz : isZero b = false) :
    finiteQ (toRat b) (mant b % 2 == 0) :=
  ⟨sign b, mant b, kexp b, (toRat_form h hz).1, rfl, (toRat_form h hz).2⟩

/-- (a) A pattern for every member of the value set. -/
theorem finiteQ_pattern {x : Rat} {ev : Bool} (hx : finiteQ x ev) :
    ∃ b, isFinite b = true ∧ isZero b = false ∧ toRat b = x := by
  obtain ⟨neg, m, k, rfl, -, hb⟩ := hx
  rcases hb with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
  · obtain ⟨hs, he, hf⟩ := pack_fields neg (e := k + 1) (f := m - 2 ^ 52) (by omega) (by omega)
    have hfin : isFinite (pack neg (k + 1) (m - 2 ^ 52)) = true := by
      simp only [isFinite, he, bne_iff_ne, ne_eq]; omega
    refine ⟨_, hfin, by simp [isZero, he], ?_⟩
    rw [(toRat_form hfin (by simp [isZero, he])).1, hs]
    simp only [mant, kexp, he, hf]
    rw [if_neg (by omega), if_neg (by omega), show m - 2 ^ 52 + 2 ^ 52 = m by omega, show k + 1 - 1 = k by omega]
  · subst h3
    obtain ⟨hs, he, hf⟩ := pack_fields neg (e := 0) (f := m) (by omega) h2
    have hfin : isFinite (pack neg 0 m) = true := by simp [isFinite, he]
    have hnz : isZero (pack neg 0 m) = false := by simp [isZero, he, hf]; omega
    refine ⟨_, hfin, hnz, ?_⟩
    rw [(toRat_form hfin hnz).1, hs]
    unfold mant kexp; simp [he, hf]

/-- A pattern is its fields. -/
theorem eq_of_fields {a b : BitVec 64} (hs : sign a = sign b) (he : biasedExponent a = biasedExponent b)
    (hf : fraction a = fraction b) : a = b := by
  apply BitVec.eq_of_toNat_eq
  have ha := a.isLt; have hb := b.isLt
  simp only [sign, biasedExponent, fraction, BitVec.msb_eq_decide, Nat.shiftLeft_eq, Nat.one_mul] at hs he hf
  by_cases h1 : 2 ^ 63 ≤ a.toNat <;> by_cases h2 : 2 ^ 63 ≤ b.toNat <;> simp [h1, h2] at hs <;> omega

theorem signed_mul_pos {neg : Bool} {v : Rat} (hv : 0 < v) : decide (signed neg v < 0) = neg := by
  cases neg <;> simp [signed] <;> grind

/-- The representation ±m × 2^(k−1074) of a value-set member is unique. -/
theorem form_unique {m₁ k₁ m₂ k₂ : Nat}
    (h₁ : (2 ^ 52 ≤ m₁ ∧ m₁ < 2 ^ 53) ∨ (m₁ < 2 ^ 52 ∧ k₁ = 0))
    (h₂ : (2 ^ 52 ≤ m₂ ∧ m₂ < 2 ^ 53) ∨ (m₂ < 2 ^ 52 ∧ k₂ = 0))
    (h : m₁ * 2 ^ k₁ = m₂ * 2 ^ k₂) : m₁ = m₂ ∧ k₁ = k₂ := by
  suffices ∀ {m₁ k₁ m₂ k₂ : Nat}, ((2 ^ 52 ≤ m₁ ∧ m₁ < 2 ^ 53) ∨ (m₁ < 2 ^ 52 ∧ k₁ = 0)) →
      ((2 ^ 52 ≤ m₂ ∧ m₂ < 2 ^ 53) ∨ (m₂ < 2 ^ 52 ∧ k₂ = 0)) → m₁ * 2 ^ k₁ = m₂ * 2 ^ k₂ → k₁ ≤ k₂ →
      m₁ = m₂ ∧ k₁ = k₂ by
    rcases Nat.le_total k₁ k₂ with hk | hk
    · exact this h₁ h₂ h hk
    · have := this h₂ h₁ h.symm hk; omega
  intro m₁ k₁ m₂ k₂ h₁ h₂ h hk
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hk
  rw [Nat.pow_add, Nat.mul_comm (2 ^ k₁) (2 ^ d), ← Nat.mul_assoc] at h
  have h' := Nat.eq_of_mul_eq_mul_right (Nat.two_pow_pos k₁) h
  cases d with
  | zero => simp at h'; omega
  | succ d =>
    have : 2 ≤ 2 ^ (d + 1) := by simpa using Nat.pow_le_pow_right (by omega : 0 < 2) (by omega : 1 ≤ d + 1)
    have hm : 2 * m₂ ≤ m₂ * 2 ^ (d + 1) := by rw [Nat.mul_comm 2]; exact Nat.mul_le_mul_left _ this
    rcases h₁ with h₁ | h₁ <;> rcases h₂ with h₂ | h₂
    · omega
    · omega
    · omega
    · omega

/-- (a) Distinct finite non-zero patterns have distinct values. -/
theorem toRat_inj {a b : BitVec 64} (ha : isFinite a = true) (hza : isZero a = false)
    (hb : isFinite b = true) (hzb : isZero b = false) (h : toRat a = toRat b) : a = b := by
  obtain ⟨fa, ra⟩ := toRat_form ha hza
  obtain ⟨fb, rb⟩ := toRat_form hb hzb
  rw [formQ_eq] at fa fb
  have pa : 0 < (mant a : Rat) * pow2 ((kexp a : Int) - 1074) :=
    Rat.mul_pos (Rat.natCast_pos.2 (by omega)) (pow2_pos _)
  have pb : 0 < (mant b : Rat) * pow2 ((kexp b : Int) - 1074) :=
    Rat.mul_pos (Rat.natCast_pos.2 (by omega)) (pow2_pos _)
  have hs : sign a = sign b := by
    rw [← signed_mul_pos (neg := sign a) pa, ← signed_mul_pos (neg := sign b) pb, ← fa, ← fb, h]
  have hv : (mant a : Rat) * pow2 ((kexp a : Int) - 1074) = (mant b : Rat) * pow2 ((kexp b : Int) - 1074) := by
    have : signed (sign a) _ = signed (sign a) _ := fa.symm.trans (h.trans (hs ▸ fb))
    cases hsa : sign a <;> simp [signed, hsa] at this <;> grind
  have hn : mant a * 2 ^ kexp a = mant b * 2 ^ kexp b := by
    have e : ∀ (m k : Nat), (m : Rat) * pow2 ((k : Int) - 1074) * pow2 1074 = ((m * 2 ^ k : Nat) : Rat) := by
      intro m k; rw [Rat.mul_assoc, ← pow2_add, show (k : Int) - 1074 + 1074 = k by omega, pow2_nat,
        Rat.natCast_mul, natCast_two_pow]
    have := congrArg (· * pow2 1074) hv; simp only [e] at this; exact_mod_cast this
  obtain ⟨hm, hk⟩ := form_unique (by omega) (by omega) hn
  have := fraction_lt a; have := fraction_lt b; have := biasedExponent_lt a; have := biasedExponent_lt b
  simp only [isFinite, isZero, bne_iff_ne, ne_eq, Bool.and_eq_false_iff, beq_eq_false_iff_ne] at ha hb hza hzb
  simp only [mant, kexp] at hm hk
  refine eq_of_fields hs ?_ ?_ <;>
    (by_cases e1 : biasedExponent a = 0 <;> by_cases e2 : biasedExponent b = 0 <;> simp [e1, e2] at hm hk <;> omega)

/-! ## Candidates -/

theorem pow2_1024 : pow2 1024 = 2 ^ 1024 := pow2_nat 1024

theorem absQ_nonneg (x : Rat) : 0 ≤ absQ x := by unfold absQ; split <;> grind

theorem absQ_of_nonneg {x : Rat} (h : 0 ≤ x) : absQ x = x := by unfold absQ; split <;> grind

theorem absQ_of_neg {x : Rat} (h : x < 0) : absQ x = -x := by unfold absQ; split <;> grind

theorem absQ_neg (x : Rat) : absQ (-x) = absQ x := by unfold absQ; split <;> split <;> grind

theorem le_absQ (x : Rat) : x ≤ absQ x ∧ -x ≤ absQ x := by unfold absQ; split <;> grind

theorem absQ_mul_pos {c : Rat} (x : Rat) (hc : 0 < c) : absQ (c * x) = c * absQ x := by
  by_cases h : x < 0
  · simp [absQ, h, (Rat.mul_neg_iff_of_pos_left hc).2 h, Rat.mul_neg]
  · have : ¬ c * x < 0 := fun h' => h ((Rat.mul_neg_iff_of_pos_left hc).1 h')
    simp [absQ, h, this]

theorem lt_of_lt_le {a b c : Rat} (h₁ : a < b) (h₂ : b ≤ c) : a < c := by grind

theorem lt_of_le_lt {a b c : Rat} (h₁ : a ≤ b) (h₂ : b < c) : a < c := by grind

theorem absQ_signed (neg : Bool) {v : Rat} (hv : 0 ≤ v) : absQ (signed neg v) = v := by
  cases neg <;> simp only [signed, Bool.false_eq_true, if_true, if_false]
  · exact absQ_of_nonneg hv
  · rw [absQ_neg, absQ_of_nonneg hv]

theorem neg_signed (neg : Bool) (v : Rat) : -(signed neg v) = signed (!neg) v := by
  cases neg <;> simp [signed]

theorem finiteQ_neg {x : Rat} {ev : Bool} (h : finiteQ x ev) : finiteQ (-x) ev := by
  obtain ⟨neg, m, k, rfl, he, hb⟩ := h
  exact ⟨!neg, m, k, neg_signed _ _, he, hb⟩

theorem candQ_neg {z : Rat} {ev : Bool} (h : candQ z ev) : candQ (-z) ev := by
  rcases h with h | ⟨rfl, h⟩ | ⟨h | h, he⟩
  · exact .inl (finiteQ_neg h)
  · exact .inr (.inl ⟨by decide, h⟩)
  · exact .inr (.inr ⟨.inr (by rw [h]), he⟩)
  · exact .inr (.inr ⟨.inl (by rw [h, Rat.neg_neg]), he⟩)

theorem natCast_lt_two_pow {m n : Nat} (h : m < 2 ^ n) : (m : Rat) < pow2 n := by
  rw [pow2_nat, ← natCast_two_pow]; exact Rat.natCast_lt_natCast.2 h

/-- A significand below 2^w gives a magnitude below 2^(w + k − 1074). -/
theorem mag_lt {m w k : Nat} (h : m < 2 ^ w) :
    (m : Rat) * pow2 ((k : Int) - 1074) < pow2 ((w : Int) + ((k : Int) - 1074)) := by
  rw [pow2_add]; exact Rat.mul_lt_mul_of_pos_right (natCast_lt_two_pow h) (pow2_pos _)

theorem mag_nonneg (m : Nat) (e : Int) : 0 ≤ (m : Rat) * pow2 e :=
  Rat.mul_nonneg (Rat.natCast_nonneg) (Rat.le_of_lt (pow2_pos e))

/-- Every candidate is at most 2^1024 in magnitude. -/
theorem candQ_abs_le {z : Rat} {ev : Bool} (h : candQ z ev) : absQ z ≤ pow2 1024 := by
  have p0 := pow2_pos 1024
  rcases h with ⟨neg, m, k, rfl, -, hb⟩ | ⟨rfl, -⟩ | ⟨h | h, -⟩
  · rw [formQ_eq, absQ_signed _ (mag_nonneg _ _)]
    rcases hb with ⟨-, h2, h3⟩ | ⟨-, h2, h3⟩
    · exact Rat.le_of_lt (lt_of_lt_le (mag_lt (k := k) h2) (pow2_le_of_le (by omega)))
    · exact Rat.le_of_lt (lt_of_lt_le (mag_lt (w := 52) (k := k) h2) (pow2_le_of_le (by omega)))
  · rw [absQ_of_nonneg (Rat.le_refl)]; exact Rat.le_of_lt p0
  · rw [h, ← pow2_1024, absQ_of_nonneg (Rat.le_of_lt p0)]; exact Rat.le_refl
  · rw [h, absQ_neg, ← pow2_1024, absQ_of_nonneg (Rat.le_of_lt p0)]; exact Rat.le_refl

/-- ±m × 2^e is on the grid of 2^p when p ≤ e. -/
theorem on_grid (neg : Bool) (m : Nat) {e p : Int} (h : p ≤ e) :
    ∃ j : Int, signed neg ((m : Rat) * pow2 e) = j * pow2 p := by
  obtain ⟨t, ht⟩ := Int.eq_ofNat_of_zero_le (by omega : 0 ≤ e - p)
  have he : pow2 e = 2 ^ t * pow2 p := by rw [← pow2_nat, ← pow2_add]; congr 1; omega
  have key : (m : Rat) * pow2 e = ((m * 2 ^ t : Nat) : Rat) * pow2 p := by
    rw [he, Rat.natCast_mul, natCast_two_pow, Rat.mul_assoc]
  refine ⟨if neg then -((m * 2 ^ t : Nat) : Int) else ((m * 2 ^ t : Nat) : Int), ?_⟩
  cases neg
  · simp only [signed, Bool.false_eq_true, if_false, Rat.intCast_natCast, key]
  · simp only [signed, if_true, Rat.intCast_neg, Rat.intCast_natCast, key, Rat.neg_mul]

/-- A candidate is a multiple of 2^p when p is the subnormal quantum or it is at least 2^(p+52). -/
theorem candQ_grid {z : Rat} {ez : Bool} (hz : candQ z ez) {p : Int} (hp : -1074 ≤ p)
    (h : p = -1074 ∨ pow2 (p + 52) ≤ absQ z) : ∃ j : Int, z = j * pow2 p := by
  rcases hz with ⟨neg, m, k, rfl, -, hb⟩ | ⟨rfl, -⟩ | ⟨hz | hz, -⟩
  · rw [formQ_eq]; apply on_grid
    rw [formQ_eq, absQ_signed _ (mag_nonneg _ _)] at h
    rcases hb with ⟨-, h2, -⟩ | ⟨-, h2, h3⟩
    · rcases h with h | h
      · omega
      · have := pow2_lt_iff.1 (lt_of_le_lt h (mag_lt (k := k) h2)); omega
    · rcases h with h | h
      · omega
      · have := pow2_lt_iff.1 (lt_of_le_lt h (mag_lt (w := 52) (k := k) h2)); omega
  · exact ⟨0, by simp⟩
  all_goals
    have hp' : p ≤ 1024 := by
      rcases h with h | h
      · omega
      · rw [hz] at h
        first | rw [absQ_neg] at h | skip
        rw [← pow2_1024, absQ_of_nonneg (Rat.le_of_lt (pow2_pos _))] at h
        have := pow2_le_iff.1 h; omega
  · obtain ⟨j, hj⟩ := on_grid false 1 hp'
    exact ⟨j, by rw [hz, ← hj, ← pow2_1024]; simp [signed, Rat.one_mul]⟩
  · obtain ⟨j, hj⟩ := on_grid true 1 hp'
    exact ⟨j, by rw [hz, ← hj, ← pow2_1024]; simp [signed, Rat.one_mul]⟩

/-! ## Rounding to an integer, ties to even -/

/-- m is a nearest integer to t, and an even one on a tie. -/
def IsRound (t : Rat) (m : Nat) : Prop :=
  ∀ j : Int, absQ (t - m) ≤ absQ (t - j) ∧ (absQ (t - m) = absQ (t - j) → j ≠ m → m % 2 = 0)

theorem natCast_one' : ((1 : Nat) : Rat) = 1 := rfl

theorem isRound_of {t f : Rat} {m0 m : Nat} (ht : t = m0 + f) (hf0 : 0 ≤ f) (hf1 : f < 1)
    (hm : (m = m0 ∧ f ≤ 1 / 2 ∧ (f = 1 / 2 → m0 % 2 = 0)) ∨
      (m = m0 + 1 ∧ 1 / 2 ≤ f ∧ (f = 1 / 2 → m0 % 2 = 1))) : IsRound t m := by
  intro j
  have hj : j ≤ (m0 : Int) - 1 ∨ j = m0 ∨ j = (m0 : Int) + 1 ∨ (m0 : Int) + 2 ≤ j := by omega
  have cast : ((m0 : Int) : Rat) = (m0 : Rat) := Rat.intCast_natCast m0
  rcases hj with hj | rfl | rfl | hj
  · have : (j : Rat) ≤ (m0 : Rat) - 1 := by
      rw [← cast, show ((m0 : Int) : Rat) - 1 = (((m0 : Int) - 1 : Int) : Rat) by simp]
      exact Rat.intCast_le_intCast.2 hj
    rcases hm with ⟨rfl, h1, h2⟩ | ⟨rfl, h1, h2⟩ <;>
      (try simp only [Rat.natCast_add, natCast_one']) <;> refine ⟨?_, ?_⟩ <;> (try simp only [absQ]) <;>
      (try split) <;> (try split) <;> grind
  · rcases hm with ⟨rfl, h1, h2⟩ | ⟨rfl, h1, h2⟩ <;>
      (try simp only [cast, Rat.natCast_add, natCast_one']) <;> refine ⟨?_, ?_⟩ <;> (try simp only [absQ]) <;>
      (try split) <;> (try split) <;> grind
  · rcases hm with ⟨rfl, h1, h2⟩ | ⟨rfl, h1, h2⟩ <;>
      (try simp only [cast, Rat.natCast_add, natCast_one', Rat.intCast_add, Rat.intCast_one]) <;>
      refine ⟨?_, ?_⟩ <;> (try simp only [absQ]) <;> (try split) <;> (try split) <;> grind
  · have : (m0 : Rat) + 2 ≤ (j : Rat) := by
      rw [← cast, show ((m0 : Int) : Rat) + 2 = (((m0 : Int) + 2 : Int) : Rat) by simp]
      exact Rat.intCast_le_intCast.2 hj
    rcases hm with ⟨rfl, h1, h2⟩ | ⟨rfl, h1, h2⟩ <;>
      (try simp only [Rat.natCast_add, natCast_one']) <;> refine ⟨?_, ?_⟩ <;> (try simp only [absQ]) <;>
      (try split) <;> (try split) <;> grind

/-- a/c < b/d over ℕ, cross-multiplied. -/
theorem div_lt_div_nat {a b c d : Nat} (hc : 0 < c) (hd : 0 < d) :
    (a : Rat) / c < (b : Rat) / d ↔ a * d < b * c := by
  have hc0 : (c : Rat) ≠ 0 := Rat.ne_of_gt (Rat.natCast_pos.2 hc)
  have hd0 : (d : Rat) ≠ 0 := Rat.ne_of_gt (Rat.natCast_pos.2 hd)
  have hcd : (0 : Rat) < c * d := Rat.mul_pos (Rat.natCast_pos.2 hc) (Rat.natCast_pos.2 hd)
  have e1 : (a : Rat) / c * (c * d) = a * d := by rw [← Rat.mul_assoc, Rat.div_mul_cancel hc0]
  have e2 : (b : Rat) / d * (c * d) = b * c := by
    rw [Rat.mul_comm (c : Rat) d, ← Rat.mul_assoc, Rat.div_mul_cancel hd0]
  rw [← Rat.mul_lt_mul_right hcd, e1, e2, ← Rat.natCast_mul, ← Rat.natCast_mul, Rat.natCast_lt_natCast]

/-- `ofRat`'s rounding of num/den to an integer, ties to even. -/
theorem isRound_div (num den : Nat) (hd : 0 < den) :
    IsRound ((num : Rat) / den)
      (if 2 * (num % den) > den ∨ (2 * (num % den) = den ∧ (num / den) % 2 = 1)
        then num / den + 1 else num / den) := by
  have hd' : (0 : Rat) < den := Rat.natCast_pos.2 hd
  have hnum : (num : Rat) = den * (num / den : Nat) + (num % den : Nat) := by
    rw [← Rat.natCast_mul, ← Rat.natCast_add, Nat.div_add_mod]
  have hr := Nat.mod_lt num hd
  have ht : (num : Rat) / den = (num / den : Nat) + (num % den : Nat) / den := by
    rw [hnum, Rat.div_def, Rat.add_mul, Rat.mul_comm (den : Rat), Rat.mul_assoc,
      Rat.mul_inv_cancel _ (Rat.ne_of_gt hd'), Rat.mul_one, ← Rat.div_def]
  have hf0 : 0 ≤ ((num % den : Nat) : Rat) / den :=
    Rat.mul_nonneg Rat.natCast_nonneg (Rat.le_of_lt (Rat.inv_pos.2 hd'))
  have hf1 : ((num % den : Nat) : Rat) / den < 1 :=
    (Rat.div_lt_iff hd').2 (by rw [Rat.one_mul]; exact Rat.natCast_lt_natCast.2 hr)
  have hA := div_lt_div_nat (a := num % den) (b := 1) hd (by decide : 0 < 2)
  have hB := div_lt_div_nat (a := 1) (b := num % den) (by decide : 0 < 2) hd
  simp only [Rat.natCast_ofNat, Nat.one_mul] at hA hB
  generalize ((num % den : Nat) : Rat) / den = f at ht hf0 hf1 hA hB
  have hE : f = 1 / 2 ↔ 2 * (num % den) = den := by
    constructor
    · intro h; subst h; have := (not_congr hA).1 Rat.lt_irrefl; have := (not_congr hB).1 Rat.lt_irrefl; omega
    · intro h; have := (not_congr hA).2 (by omega); have := (not_congr hB).2 (by omega)
      exact Rat.le_antisymm (Rat.not_lt.1 this) (Rat.not_lt.1 ‹¬f < 1 / 2›)
  apply isRound_of ht hf0 hf1
  split
  · right; refine ⟨rfl, Rat.not_lt.1 fun h => by have := hA.1 h; omega, fun h => by have := hE.1 h; omega⟩
  · left; refine ⟨rfl, Rat.not_lt.1 fun h => by have := hB.1 h; omega, fun h => by have := hE.1 h; omega⟩

end Engine.Binary64
