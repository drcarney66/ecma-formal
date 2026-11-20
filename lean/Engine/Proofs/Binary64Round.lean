module

public import Ecma.Model
public import Engine.Proofs.Binary64Laws

@[expose] public section

/-!
# Binary64's rounding meets the Number laws

Over ℚ: `ofRat` is "the Number value for x" (`Model.NumLaws.numOf_nearest`: the nearest candidate,
ties to even, ±2^1024 as ±∞, a zero with x's sign), exact on the value set and on the integers up
to 2^53.
-/

namespace Engine.Binary64

/-! ## The nearest candidate -/

/-- |X − j·2^q| is 2^q · |X/2^q − j|. -/
theorem absQ_scale (X : Rat) (j : Rat) (q : Int) :
    absQ (X - j * pow2 q) = pow2 q * absQ (X / pow2 q - j) := by
  have hp := pow2_pos q
  have : X - j * pow2 q = pow2 q * (X / pow2 q - j) := by
    have hX : pow2 q * (X / pow2 q) = X := by
      rw [Rat.mul_comm]; exact Rat.div_mul_cancel (pow2_ne q)
    grind
  rw [this, absQ_mul_pos _ hp]

theorem mul_left_cancel_pos {a b c : Rat} (hc : 0 < c) (h : c * a = c * b) : a = b :=
  Rat.le_antisymm (Rat.not_lt.1 fun h' => Rat.lt_irrefl (h ▸ (Rat.mul_lt_mul_left hc).2 h'))
    (Rat.not_lt.1 fun h' => Rat.lt_irrefl (h ▸ (Rat.mul_lt_mul_left hc).2 h'))

/-- m·2^q, m the rounding of X/2^q, is nearest to X > 0 when q is subnormal or X ≥ 2^(q+52). -/
theorem nearest_grid {X : Rat} {q : Int} {m : Nat} (hq : -1074 ≤ q)
    (hg : q = -1074 ∨ pow2 (q + 52) ≤ X) (hm : IsRound (X / pow2 q) m) {z : Rat} {ez : Bool}
    (hz : candQ z ez) :
    ¬ absQ (X - z) < absQ (X - m * pow2 q) ∧
      (absQ (X - z) = absQ (X - m * pow2 q) → z ≠ m * pow2 q → m % 2 = 0) := by
  have hp := pow2_pos q
  have hmI : ((m : Int) : Rat) = (m : Rat) := Rat.intCast_natCast m
  by_cases hon : q = -1074 ∨ pow2 (q + 52) ≤ absQ z
  · obtain ⟨j, rfl⟩ := candQ_grid hz hq hon
    obtain ⟨h1, h2⟩ := hm j
    rw [absQ_scale, absQ_scale]
    refine ⟨fun h => ?_, fun h hne => h2 ?_ fun hj => hne (by rw [hj, hmI])⟩
    · exact Rat.not_le.2 ((Rat.mul_lt_mul_left hp).1 h) h1
    · exact (mul_left_cancel_pos hp h).symm
  · have hz' : absQ z < pow2 (q + 52) := Rat.not_le.1 fun h => hon (.inr h)
    have hgX : pow2 (q + 52) ≤ X := by
      rcases hg with h | h
      · exact absurd (.inl h) hon
      · exact h
    obtain ⟨h1, -⟩ := hm ((2 ^ 52 : Nat) : Int)
    have e52 : ((((2 ^ 52 : Nat) : Int)) : Rat) * pow2 q = pow2 (q + 52) := by
      rw [Rat.intCast_natCast, natCast_two_pow, ← pow2_nat, ← pow2_add, Int.add_comm]; rfl
    have hY : absQ (X - m * pow2 q) ≤ X - pow2 (q + 52) := by
      have := Rat.mul_le_mul_of_nonneg_left h1 (Rat.le_of_lt hp)
      rw [← absQ_scale, ← absQ_scale, e52, absQ_of_nonneg (x := X - pow2 (q + 52)) (by grind)] at this
      exact this
    have hzX : X - pow2 (q + 52) < absQ (X - z) := by
      have := le_absQ z; have := le_absQ (X - z); grind
    exact ⟨fun h => by grind, fun h => by grind⟩

theorem absQ_eq_zero {a : Rat} (h : absQ a = 0) : a = 0 := by unfold absQ at h; split at h <;> grind

theorem nearestQ_neg {x y : Rat} (h : nearestQ x y) : nearestQ (-x) (-y) := by
  obtain ⟨ev, hy, hall⟩ := h
  refine ⟨ev, candQ_neg hy, fun z ez hz => ?_⟩
  obtain ⟨h1, h2⟩ := hall (-z) ez (candQ_neg hz)
  have e1 : absQ (-x - z) = absQ (x - -z) := by rw [← absQ_neg]; congr 1; grind
  have e2 : absQ (-x - -y) = absQ (x - y) := by rw [← absQ_neg]; congr 1; grind
  rw [e1, e2]
  exact ⟨h1, fun h hne => h2 h fun h' => hne (by rw [← h', Rat.neg_neg])⟩

/-- A candidate is its own nearest. -/
theorem nearestQ_self {x : Rat} {ev : Bool} (h : candQ x ev) : nearestQ x x := by
  refine ⟨ev, h, fun z _ _ => ?_⟩
  have e : absQ (x - x) = 0 := by rw [Rat.sub_self]; rfl
  rw [e]
  exact ⟨Rat.not_lt.2 (absQ_nonneg _), fun h hne => absurd (by have := absQ_eq_zero h; grind) hne⟩

/-- The nearest to a candidate is itself. -/
theorem nearestQ_eq_self {x y : Rat} {ev : Bool} (hx : candQ x ev) (h : nearestQ x y) : y = x := by
  obtain ⟨_, _, hall⟩ := h
  have h1 := (hall x ev hx).1
  have e : absQ (x - x) = 0 := by rw [Rat.sub_self]; rfl
  rw [e] at h1
  have := absQ_eq_zero (Rat.le_antisymm (Rat.not_lt.1 h1) (absQ_nonneg _)); grind

/-! ## `ofRat`'s exponent and scaling -/

theorem pow2_div (a b : Int) : pow2 a / pow2 b = pow2 (a - b) := by
  have : pow2 (a - b) * pow2 b = pow2 a := by rw [← pow2_add]; congr 1; omega
  rw [← this, Rat.div_def, Rat.mul_assoc, Rat.mul_inv_cancel _ (pow2_ne _), Rat.mul_one]

theorem natCast_two_pow' (n : Nat) : ((2 ^ n : Nat) : Rat) = pow2 n := by rw [natCast_two_pow, pow2_nat]

/-- `ltPow2 n d e` decides n/d < 2^e. -/
theorem ltPow2_iff {n d : Nat} (e : Int) (hd : 0 < d) : ltPow2 n d e = true ↔ (n : Rat) / d < pow2 e := by
  have hd' : (0 : Rat) < d := Rat.natCast_pos.2 hd
  unfold ltPow2; split
  · rename_i he
    have hp : pow2 e = ((2 ^ e.toNat : Nat) : Rat) := by rw [natCast_two_pow']; congr 1; omega
    rw [hp, Rat.div_lt_iff hd', ← Rat.natCast_mul, Rat.natCast_lt_natCast, Nat.mul_comm, decide_eq_true_iff]
  · rename_i he
    have hp : pow2 e = ((1 : Nat) : Rat) / ((2 ^ (-e).toNat : Nat) : Rat) := by
      rw [natCast_two_pow', natCast_one', show (1 : Rat) = pow2 0 by decide, pow2_div]; congr 1; omega
    rw [hp, div_lt_div_nat hd (Nat.two_pow_pos _), Nat.one_mul, decide_eq_true_iff]

/-- n/d lies within a factor of 2 of 2^(log₂ n − log₂ d). -/
theorem log2_bounds {n d : Nat} (hn : 0 < n) (hd : 0 < d) :
    pow2 ((n.log2 : Int) - d.log2 - 1) < (n : Rat) / d ∧ (n : Rat) / d < pow2 ((n.log2 : Int) - d.log2 + 1) := by
  have a1 := Nat.log2_self_le (Nat.ne_of_gt hn); have a2 := Nat.lt_log2_self (n := n)
  have b1 := Nat.log2_self_le (Nat.ne_of_gt hd); have b2 := Nat.lt_log2_self (n := d)
  constructor
  · rw [show (n.log2 : Int) - d.log2 - 1 = ((n.log2 : Nat) : Int) - ((d.log2 + 1 : Nat) : Int) by omega,
      ← pow2_div, ← natCast_two_pow', ← natCast_two_pow', div_lt_div_nat (Nat.two_pow_pos _) hd]
    exact Nat.mul_lt_mul_of_le_of_lt a1 b2 hn
  · rw [show (n.log2 : Int) - d.log2 + 1 = ((n.log2 + 1 : Nat) : Int) - ((d.log2 : Nat) : Int) by omega,
      ← pow2_div, ← natCast_two_pow', ← natCast_two_pow', div_lt_div_nat hd (Nat.two_pow_pos _)]
    exact Nat.mul_lt_mul_of_lt_of_le a2 b1 hd

/-- `ofRat`'s exponent: 2^E ≤ n/d < 2^(E+1). -/
theorem ofRat_exp {n d : Nat} (hn : 0 < n) (hd : 0 < d) :
    let e0 : Int := (n.log2 : Int) - d.log2
    let E := if ltPow2 n d e0 then e0 - 1 else e0
    pow2 E ≤ (n : Rat) / d ∧ (n : Rat) / d < pow2 (E + 1) := by
  intro e0 E
  obtain ⟨h1, h2⟩ := log2_bounds hn hd
  have hl := ltPow2_iff (n := n) e0 hd
  simp only [E]; split
  · rename_i h
    exact ⟨Rat.le_of_lt h1, by rw [show e0 - 1 + 1 = e0 by omega]; exact hl.1 h⟩
  · rename_i h
    exact ⟨Rat.not_lt.1 fun h' => h (hl.2 h'), h2⟩

/-- `ofRat`'s scaled numerator and denominator: num/den = (n/d) / 2^q. -/
theorem ofRat_scale (n d : Nat) (q : Int) :
    ((if q ≤ 0 then n * 2 ^ (-q).toNat else n : Nat) : Rat) / ((if q ≤ 0 then d else d * 2 ^ q.toNat : Nat) : Rat) =
      (n : Rat) / d / pow2 q := by
  split
  · rename_i hq
    have : pow2 q * pow2 ((-q).toNat : Int) = 1 := by rw [← pow2_add, show q + ((-q).toNat : Int) = 0 by omega]; decide
    rw [Rat.natCast_mul, natCast_two_pow']; grind
  · rename_i hq
    have : pow2 q = pow2 (q.toNat : Int) := by congr 1; omega
    rw [Rat.natCast_mul, natCast_two_pow', ← this]; grind

theorem isRound_le {t : Rat} {m B : Nat} (h : IsRound t m) (ht : t ≤ B) : m ≤ B := by
  have h1 := (h B).1
  rw [Rat.intCast_natCast] at h1
  refine Nat.not_lt.1 fun hc => ?_
  have : ((B + 1 : Nat) : Rat) ≤ m := Rat.natCast_le_natCast.2 hc
  rw [Rat.natCast_add, natCast_one'] at this
  simp only [absQ] at h1; split at h1 <;> split at h1 <;> grind

theorem isRound_ge {t : Rat} {m B : Nat} (h : IsRound t m) (ht : (B : Rat) ≤ t) : B ≤ m := by
  have h1 := (h B).1
  rw [Rat.intCast_natCast] at h1
  refine Nat.not_lt.1 fun hc => ?_
  have : ((m + 1 : Nat) : Rat) ≤ B := Rat.natCast_le_natCast.2 hc
  rw [Rat.natCast_add, natCast_one'] at this
  simp only [absQ] at h1; split at h1 <;> split at h1 <;> grind

/-! ## The Number value for x -/

/-- A pattern's view over ℚ. -/
def viewQ (b : BitVec 64) : Ecma.NumView Rat :=
  if isNaN b then .nan
  else if isFinite b = false then (if sign b then .negInf else .posInf)
  else if isZero b then (if sign b then .negZero else .posZero)
  else .finite (toRat b)

/-- `Model.viewFor` over ℚ. -/
def viewForQ (x y : Rat) : Ecma.NumView Rat :=
  if y = 2 ^ 1024 then .posInf
  else if y = -(2 ^ 1024) then .negInf
  else if y = 0 then (if x < 0 then .negZero else .posZero)
  else .finite y

/-- The view of an assembled finite pattern. -/
theorem viewQ_pack (neg : Bool) {e f : Nat} (he : e < 2047) (hf : f < 2 ^ 52) :
    viewQ (pack neg e f) = if e = 0 ∧ f = 0 then (if neg then .negZero else .posZero) else
      .finite (signed neg (((if e = 0 then f else f + 2 ^ 52 : Nat) : Rat) *
        pow2 (((if e = 0 then 0 else e - 1 : Nat) : Int) - 1074))) := by
  obtain ⟨hs, hb, hfr⟩ := pack_fields neg (e := e) (by omega) hf
  have hfin : isFinite (pack neg e f) = true := by simp [isFinite, hb]; omega
  have ht := toRat_of_finite hfin
  simp only [mant, kexp, hb, hfr, hs] at ht
  unfold viewQ
  simp only [isNaN, isZero, hb, hfr, hs, hfin, ht]
  by_cases h0 : e = 0 <;> by_cases h1 : f = 0 <;> simp [h0, h1] <;> omega

/-- The view of the Number value for a positive x's nearest Y, given the sign. -/
def posView (neg : Bool) (Y : Rat) : Ecma.NumView Rat :=
  if Y = 2 ^ 1024 then (if neg then .negInf else .posInf)
  else if Y = 0 then (if neg then .negZero else .posZero)
  else .finite (signed neg Y)

theorem div_lt_div_pos {a b c : Rat} (hc : 0 < c) : a / c < b / c ↔ a < b := by
  rw [Rat.div_def, Rat.div_def]; exact Rat.mul_lt_mul_right (Rat.inv_pos.2 hc)

/-- 2^1024 is nearest when a value at least 2^1024 is no farther than any candidate. -/
theorem nearest_overflow {X Y0 : Rat} (hY : pow2 1024 ≤ Y0)
    (hN : ∀ z ez, candQ z ez → ¬ absQ (X - z) < absQ (X - Y0)) : nearestQ X (2 ^ 1024) := by
  rw [← pow2_1024]
  refine ⟨true, .inr (.inr ⟨.inl pow2_1024, rfl⟩), fun z ez hz => ⟨fun h => ?_, fun _ _ => rfl⟩⟩
  have hzb := Rat.le_trans (le_absQ z).1 (candQ_abs_le hz)
  have h1 := hN z ez hz
  have := le_absQ (X - z); have := le_absQ (X - Y0)
  simp only [absQ] at h h1; split at h <;> split at h <;> split at h1 <;> split at h1 <;> grind


theorem viewQ_inf (neg : Bool) :
    viewQ (if neg then negInfinity else posInfinity) = if neg then .negInf else .posInf := by
  cases neg <;> simp [viewQ, isNaN, isFinite, sign, biasedExponent, fraction, negInfinity, posInfinity] <;> decide

theorem two_pow_1024_pos : (0 : Rat) < 2 ^ 1024 := pow2_1024 ▸ pow2_pos 1024

/-- The overflow case: Y = 2^1024. -/
theorem overflow_case (neg : Bool) {X Y0 : Rat} (hY : pow2 1024 ≤ Y0)
    (hN : ∀ z ez, candQ z ez → ¬ absQ (X - z) < absQ (X - Y0)) :
    ∃ Y, 0 ≤ Y ∧ nearestQ X Y ∧ viewQ (if neg then negInfinity else posInfinity) = posView neg Y :=
  ⟨2 ^ 1024, Rat.le_of_lt two_pow_1024_pos, nearest_overflow hY hN, by rw [viewQ_inf]; simp [posView]⟩

/-- The finite case: Y = m × 2^(k−1074) in the value set. -/
theorem finite_case (neg : Bool) {X : Rat} {m k : Nat}
    (hb : (2 ^ 52 ≤ m ∧ m < 2 ^ 53 ∧ k ≤ 2045) ∨ (0 < m ∧ m < 2 ^ 52 ∧ k = 0))
    (hN : ∀ z ez, candQ z ez → ¬ absQ (X - z) < absQ (X - m * pow2 ((k : Int) - 1074)) ∧
      (absQ (X - z) = absQ (X - m * pow2 ((k : Int) - 1074)) → z ≠ m * pow2 ((k : Int) - 1074) → m % 2 = 0)) :
    0 ≤ (m : Rat) * pow2 ((k : Int) - 1074) ∧ nearestQ X ((m : Rat) * pow2 ((k : Int) - 1074)) ∧
      posView neg ((m : Rat) * pow2 ((k : Int) - 1074)) = .finite (signed neg ((m : Rat) * pow2 ((k : Int) - 1074))) := by
  have hm : 0 < m := by omega
  have hpos : 0 < (m : Rat) * pow2 ((k : Int) - 1074) :=
    Rat.mul_pos (Rat.natCast_pos.2 hm) (pow2_pos _)
  have hlt : (m : Rat) * pow2 ((k : Int) - 1074) < 2 ^ 1024 := by
    rw [← pow2_1024]
    exact lt_of_lt_le (mag_lt (w := 53) (by omega)) (pow2_le_of_le (by omega))
  refine ⟨Rat.le_of_lt hpos, ⟨m % 2 == 0, .inl ⟨false, m, k, by rw [formQ_eq]; rfl, rfl, hb⟩,
    fun z ez hz => ⟨(hN z ez hz).1, fun h hne => by simp [(hN z ez hz).2 h hne]⟩⟩, ?_⟩
  simp only [posView, Rat.ne_of_gt hpos, Rat.ne_of_lt hlt, if_false]

/-- `ofRat`'s general path for n/d > 0 with 2^E ≤ n/d < 2^(E+1). -/
theorem ofRat_general (neg : Bool) {n d : Nat} {E : Int} (hd : 0 < d)
    (hE : pow2 E ≤ (n : Rat) / d ∧ (n : Rat) / d < pow2 (E + 1)) :
    ∃ Y, 0 ≤ Y ∧ nearestQ ((n : Rat) / d) Y ∧ viewQ (
      let q : Int := max E (-1022) - 52
      let num := if q ≤ 0 then n * 2 ^ (-q).toNat else n
      let den := if q ≤ 0 then d else d * 2 ^ q.toNat
      let m := num / den
      let r := num % den
      let m := if 2 * r > den ∨ (2 * r = den ∧ m % 2 = 1) then m + 1 else m
      let (m, q) := if m = 2 ^ 53 then (2 ^ 52, q + 1) else (m, q)
      if m < 2 ^ 52 then pack neg 0 m
      else
        let biased : Int := q + 52 + 1023
        if 2047 ≤ biased then (if neg then negInfinity else posInfinity)
        else pack neg biased.toNat ((m - 2 ^ 52) % 2 ^ 52)) = posView neg Y := by
  dsimp only
  generalize hX : (n : Rat) / d = X at hE
  generalize hq : max E (-1022) - 52 = q
  have hden : 0 < (if q ≤ 0 then d else d * 2 ^ q.toNat) := by
    split
    · exact hd
    · exact Nat.mul_pos hd (Nat.two_pow_pos _)
  have hs := ofRat_scale n d q
  generalize (if q ≤ 0 then n * 2 ^ (-q).toNat else n) = num at hs ⊢
  generalize (if q ≤ 0 then d else d * 2 ^ q.toNat) = den at hs hden ⊢
  have hR := isRound_div num den hden
  generalize (if 2 * (num % den) > den ∨ (2 * (num % den) = den ∧ (num / den) % 2 = 1)
    then num / den + 1 else num / den) = m0 at hR ⊢
  rw [hs, hX] at hR
  have hp := pow2_pos q
  have hq1 : -1074 ≤ q := by omega
  have hg : q = -1074 ∨ pow2 (q + 52) ≤ X := by
    by_cases h : E ≤ -1022
    · left; omega
    · right; rw [show q + 52 = E by omega]; exact hE.1
  have hN := fun z ez (hz : candQ z ez) => nearest_grid hq1 hg hR hz
  have ht : X / pow2 q < pow2 53 := by
    have h1 := (div_lt_div_pos hp).2 hE.2
    rw [pow2_div] at h1; exact lt_of_lt_le h1 (pow2_le_of_le (by omega))
  have hm53 : m0 ≤ 2 ^ 53 := isRound_le hR (by rw [natCast_two_pow']; exact Rat.le_of_lt ht)
  have hm52 : -1022 ≤ E → 2 ^ 52 ≤ m0 := fun h => by
    have h1 : pow2 E / pow2 q ≤ X / pow2 q := Rat.not_lt.1 fun h' => Rat.not_lt.2 hE.1 ((div_lt_div_pos hp).1 h')
    rw [pow2_div, show E - q = 52 by omega] at h1
    exact isRound_ge hR (by rw [natCast_two_pow']; exact h1)
  have hX0 : 0 < X := lt_of_lt_le (pow2_pos E) hE.1
  by_cases hc : m0 = 2 ^ 53
  · subst hc
    simp only [if_true, show ¬ (2 ^ 52 : Nat) < 2 ^ 52 by decide, if_false]
    have hY0 : ((2 ^ 53 : Nat) : Rat) * pow2 q = pow2 (q + 53) := by
      rw [natCast_two_pow', ← pow2_add, Int.add_comm]; rfl
    by_cases ho : 2047 ≤ q + 1 + 52 + 1023
    · simp only [ho, if_true]
      exact overflow_case neg (by rw [hY0]; exact pow2_le_of_le (by omega)) fun z ez hz => (hN z ez hz).1
    · simp only [ho, if_false, Nat.sub_self, Nat.zero_mod]
      have hv := viewQ_pack neg (e := (q + 1 + 52 + 1023).toNat) (f := 0) (by omega) (by decide)
      have hk : (((q + 1 + 52 + 1023).toNat - 1 : Nat) : Int) - 1074 = q + 1 := by omega
      simp only [show (q + 1 + 52 + 1023).toNat ≠ 0 by omega, false_and, if_false, Nat.zero_add, hk] at hv
      rw [hv]
      have hk' : (((q + 1075).toNat : Nat) : Int) - 1074 = q + 1 := by omega
      have e1 : ((2 ^ 52 : Nat) : Rat) * pow2 (q + 1) = ((2 ^ 53 : Nat) : Rat) * pow2 q := by
        rw [hY0, natCast_two_pow', ← pow2_add]; congr 1; omega
      obtain ⟨h1, h2, h3⟩ := finite_case neg (X := X) (m := 2 ^ 52) (k := (q + 1075).toNat)
        (.inl ⟨by decide, by decide, by omega⟩) (by rw [hk', e1]; exact hN)
      rw [hk', e1] at h1 h2 h3
      exact ⟨_, h1, h2, by rw [h3, e1]⟩
  · have hc' : m0 < 2 ^ 53 := by omega
    simp only [hc, if_false]
    by_cases hs52 : m0 < 2 ^ 52
    · simp only [hs52, if_true]
      have hq' : q = -1074 := by
        by_cases h : -1022 ≤ E
        · exact absurd (hm52 h) (by omega)
        · omega
      subst hq'
      rw [viewQ_pack neg (by decide) hs52]
      by_cases h0 : m0 = 0
      · subst h0
        refine ⟨0, Rat.le_refl, ⟨true, .inr (.inl ⟨rfl, rfl⟩), fun z ez hz => ⟨?_, fun _ _ => rfl⟩⟩, ?_⟩
        · have := (hN z ez hz).1; simpa using this
        · simp [posView, Rat.ne_of_lt two_pow_1024_pos]
      · simp only [h0, and_false, if_false, if_true]
        obtain ⟨h1, h2, h3⟩ := finite_case neg (X := X) (m := m0) (k := 0) (.inr ⟨by omega, hs52, rfl⟩)
          (by simpa using hN)
        exact ⟨_, h1, h2, by rw [h3]⟩
    · simp only [hs52, if_false]
      by_cases ho : 2047 ≤ q + 52 + 1023
      · simp only [ho, if_true]
        refine overflow_case neg (Y0 := m0 * pow2 q) ?_ fun z ez hz => (hN z ez hz).1
        have : pow2 1024 ≤ ((2 ^ 52 : Nat) : Rat) * pow2 q := by
          rw [natCast_two_pow', ← pow2_add]; exact pow2_le_of_le (by omega)
        exact Rat.le_trans this (Rat.mul_le_mul_of_nonneg_right (Rat.natCast_le_natCast.2 (by omega))
          (Rat.le_of_lt hp))
      · simp only [ho, if_false]
        have hf : (m0 - 2 ^ 52) % 2 ^ 52 = m0 - 2 ^ 52 := Nat.mod_eq_of_lt (by omega)
        rw [hf, viewQ_pack neg (by omega) (by omega)]
        have hk : ((q + 52 + 1023).toNat - 1 : Nat) = (q + 1074).toNat := by omega
        have hk' : (((q + 1074).toNat : Nat) : Int) - 1074 = q := by omega
        simp only [show (q + 52 + 1023).toNat ≠ 0 by omega, false_and, if_false,
          Nat.sub_add_cancel (Nat.not_lt.1 hs52), hk]
        obtain ⟨h1, h2, h3⟩ := finite_case neg (X := X) (m := m0) (k := (q + 1074).toNat)
          (.inl ⟨by omega, hc', by omega⟩) (by rw [hk']; exact hN)
        rw [hk'] at h1 h2 h3
        exact ⟨_, h1, h2, by rw [hk']; exact h3.symm⟩

/-- `ofRat`'s integer path: 0 < n < 2^53 is exact. -/
theorem ofRat_fast (neg : Bool) {n : Nat} (hn : 0 < n) (h53 : n >>> 53 = 0) :
    ∃ Y, 0 ≤ Y ∧ nearestQ (n : Rat) Y ∧
      viewQ (pack neg (Nat.log2 n + 1023) ((n <<< (52 - Nat.log2 n)) - (1 <<< 52))) = posView neg Y := by
  have hlt : n < 2 ^ 53 := by
    rw [Nat.shiftRight_eq_div_pow, Nat.div_eq_zero_iff] at h53; omega
  have a1 := Nat.log2_self_le (Nat.ne_of_gt hn); have a2 := Nat.lt_log2_self (n := n)
  generalize Nat.log2 n = E at a1 a2
  have hE : E ≤ 52 := Nat.lt_succ_iff.1 ((Nat.pow_lt_pow_iff_right (by decide)).1 (Nat.lt_of_le_of_lt a1 hlt))
  rw [Nat.shiftLeft_eq, Nat.shiftLeft_eq, Nat.one_mul]
  have hM1 : 2 ^ 52 ≤ n * 2 ^ (52 - E) := by
    have := Nat.mul_le_mul_right (2 ^ (52 - E)) a1
    rwa [← Nat.pow_add, Nat.add_sub_cancel' hE] at this
  have hM2 : n * 2 ^ (52 - E) < 2 ^ 53 := by
    have := Nat.mul_lt_mul_of_pos_right a2 (Nat.two_pow_pos (52 - E))
    rwa [← Nat.pow_add, show E + 1 + (52 - E) = 53 by omega] at this
  rw [viewQ_pack neg (by omega) (by omega)]
  simp only [show E + 1023 ≠ 0 by omega, false_and, if_false, Nat.sub_add_cancel hM1,
    show E + 1023 - 1 = E + 1022 by omega]
  have hval : (n : Rat) = ((n * 2 ^ (52 - E) : Nat) : Rat) * pow2 (((E + 1022 : Nat) : Int) - 1074) := by
    rw [Rat.natCast_mul, natCast_two_pow', Rat.mul_assoc, ← pow2_add,
      show ((52 - E : Nat) : Int) + (((E + 1022 : Nat) : Int) - 1074) = 0 by omega]
    exact (Rat.mul_one _).symm
  obtain ⟨h1, h2, h3⟩ := finite_case neg (X := n) (m := n * 2 ^ (52 - E)) (k := E + 1022)
    (.inl ⟨hM1, hM2, by omega⟩) fun z ez hz => by
      rw [← hval, Rat.sub_self]
      exact ⟨Rat.not_lt.2 (absQ_nonneg _), fun h hne => absurd (by have := absQ_eq_zero (h.trans rfl); grind) hne⟩
  rw [← hval] at h1 h2 h3
  exact ⟨_, h1, h2, by rw [h3, hval]⟩

theorem natAbs_div_den (x : Rat) : (x.num.natAbs : Rat) / x.den = absQ x := by
  have h : (x.num : Rat) / (x.den : Rat) = x := by
    rw [← Rat.intCast_natCast, ← Rat.divInt_eq_div]; exact Rat.num_divInt_den x
  have hn := (Rat.num_nonneg (q := x))
  unfold absQ; split
  · rename_i hx
    have : ((x.num.natAbs : Int) : Rat) = -(x.num : Rat) := by
      rw [Int.ofNat_natAbs_of_nonpos (by have : ¬ 0 ≤ x.num := fun h => Rat.not_le.2 hx (hn.1 h); omega), Rat.intCast_neg]
    rw [← Rat.intCast_natCast, this, Rat.div_def, Rat.neg_mul, ← Rat.div_def, h]
  · rename_i hx
    have : ((x.num.natAbs : Int) : Rat) = (x.num : Rat) := by
      rw [Int.natAbs_of_nonneg (hn.2 (Rat.not_lt.1 hx))]
    rw [← Rat.intCast_natCast, this, h]

/-- (b) `ofRat x` for x ≠ 0 is the nearest candidate, ±∞ for ±2^1024, a zero with x's sign for 0. -/
theorem ofRat_view {x : Rat} (hx : x ≠ 0) : ∃ y, nearestQ x y ∧ viewQ (ofRat x) = viewForQ x y := by
  have hn : 0 < x.num.natAbs := Int.natAbs_pos.2 fun h => hx (Rat.num_eq_zero.1 h)
  have key : ∃ Y, 0 ≤ Y ∧ nearestQ (absQ x) Y ∧ viewQ (ofRat x) = posView (decide (x < 0)) Y := by
    rw [← natAbs_div_den]
    unfold ofRat; rw [if_neg hx]; dsimp only
    by_cases h : x.den = 1 ∧ x.num.natAbs >>> 53 = 0
    · rw [if_pos h, h.1, natCast_one', show ∀ a : Rat, a / 1 = a from fun a => by grind]
      exact ofRat_fast _ hn h.2
    · rw [if_neg h]; exact ofRat_general _ x.den_pos (ofRat_exp hn x.den_pos)
  obtain ⟨Y, hY0, hN, hv⟩ := key
  have h1024 := two_pow_1024_pos
  refine ⟨signed (decide (x < 0)) Y, ?_, ?_⟩
  · by_cases h : x < 0
    · have := nearestQ_neg hN
      rw [absQ_of_neg h, Rat.neg_neg] at this
      simpa [signed, h] using this
    · simpa [signed, h, absQ_of_nonneg (Rat.not_lt.1 h)] using hN
  · rw [hv]
    by_cases h : x < 0 <;> by_cases hY1 : Y = 2 ^ 1024 <;> by_cases hY2 : Y = 0 <;>
      simp [posView, viewForQ, signed, h, hY1, hY2] <;> grind

/-- A member of the value set is non-zero and below 2^1024 in magnitude. -/
theorem finiteQ_bounds {x : Rat} {ev : Bool} (h : finiteQ x ev) : x ≠ 0 ∧ absQ x < 2 ^ 1024 := by
  obtain ⟨neg, m, k, rfl, -, hb⟩ := h
  have hpos : 0 < (m : Rat) * pow2 ((k : Int) - 1074) := Rat.mul_pos (Rat.natCast_pos.2 (by omega)) (pow2_pos _)
  rw [formQ_eq, absQ_signed _ (Rat.le_of_lt hpos), ← pow2_1024]
  refine ⟨fun h0 => ?_, lt_of_lt_le (mag_lt (w := 53) (by omega)) (pow2_le_of_le (by omega))⟩
  cases neg <;> simp only [signed, Bool.false_eq_true, if_true, if_false] at h0 <;> grind

/-- `ofRat` is exact on the value set. -/
theorem ofRat_finite {x : Rat} {ev : Bool} (h : finiteQ x ev) : viewQ (ofRat x) = .finite x := by
  obtain ⟨h0, hb⟩ := finiteQ_bounds h
  obtain ⟨y, hy, hv⟩ := ofRat_view h0
  rw [nearestQ_eq_self (.inl h) hy] at hv
  have h1 : x < 2 ^ 1024 := lt_of_le_lt (le_absQ x).1 hb
  have h2 : -x < 2 ^ 1024 := lt_of_le_lt (le_absQ x).2 hb
  rw [hv, viewForQ, if_neg (Rat.ne_of_lt h1),
    if_neg fun h' => Rat.lt_irrefl (by rw [h', Rat.neg_neg] at h2; exact h2), if_neg h0]

/-! ## Integers -/

/-- An integer 0 < n < 2^53, normalized: n = n·2^(52 − log₂ n) × 2^(log₂ n + 1022 − 1074). -/
theorem nat_norm {n : Nat} (hn : 0 < n) (hlt : n < 2 ^ 53) :
    2 ^ 52 ≤ n * 2 ^ (52 - Nat.log2 n) ∧ n * 2 ^ (52 - Nat.log2 n) < 2 ^ 53 ∧ Nat.log2 n ≤ 52 ∧
      (n : Rat) = ((n * 2 ^ (52 - Nat.log2 n) : Nat) : Rat) * pow2 (((Nat.log2 n + 1022 : Nat) : Int) - 1074) := by
  have a1 := Nat.log2_self_le (Nat.ne_of_gt hn); have a2 := Nat.lt_log2_self (n := n)
  generalize Nat.log2 n = E at a1 a2 ⊢
  have hE : E ≤ 52 := Nat.lt_succ_iff.1 ((Nat.pow_lt_pow_iff_right (by decide)).1 (Nat.lt_of_le_of_lt a1 hlt))
  refine ⟨?_, ?_, hE, ?_⟩
  · have := Nat.mul_le_mul_right (2 ^ (52 - E)) a1
    rwa [← Nat.pow_add, Nat.add_sub_cancel' hE] at this
  · have := Nat.mul_lt_mul_of_pos_right a2 (Nat.two_pow_pos (52 - E))
    rwa [← Nat.pow_add, show E + 1 + (52 - E) = 53 by omega] at this
  · rw [Rat.natCast_mul, natCast_two_pow', Rat.mul_assoc, ← pow2_add,
      show ((52 - E : Nat) : Int) + (((E + 1022 : Nat) : Int) - 1074) = 0 by omega]
    exact (Rat.mul_one _).symm

/-- An integer 0 < n ≤ 2^53 is in the value set. -/
theorem nat_finiteQ {n : Nat} (hn : 0 < n) (h : n ≤ 2 ^ 53) : ∃ ev, finiteQ (n : Rat) ev := by
  rcases Nat.lt_or_eq_of_le h with h | rfl
  · obtain ⟨h1, h2, h3, hv⟩ := nat_norm hn h
    exact ⟨_, false, _, _, by rw [formQ_eq]; exact hv, rfl, .inl ⟨h1, h2, by omega⟩⟩
  · refine ⟨true, false, 2 ^ 52, 1075, ?_, rfl, .inl ⟨by omega, by omega, by omega⟩⟩
    rw [formQ_eq, natCast_two_pow', natCast_two_pow', ← pow2_add]; rfl

/-- An integer t, 0 < |t| ≤ 2^53, is in the value set. -/
theorem int_finiteQ {t : Int} (h0 : t ≠ 0) (h : t.natAbs ≤ 2 ^ 53) : ∃ ev, finiteQ (t : Rat) ev := by
  obtain ⟨ev, hf⟩ := nat_finiteQ (Int.natAbs_pos.2 h0) h
  rcases Int.natAbs_eq t with he | he
  · exact ⟨ev, by rw [he, Rat.intCast_natCast]; exact hf⟩
  · exact ⟨ev, by rw [he, Rat.intCast_neg, Rat.intCast_natCast]; exact finiteQ_neg hf⟩

theorem ofRat_zero : ofRat 0 = posZero := by simp [ofRat]

/-- `ofRat` is exact on the integers 0 < |t| ≤ 2^53. -/
theorem ofRat_int {t : Int} (h0 : t ≠ 0) (h : t.natAbs ≤ 2 ^ 53) : viewQ (ofRat t) = .finite t :=
  (int_finiteQ h0 h).elim fun _ hf => ofRat_finite hf

end Engine.Binary64
