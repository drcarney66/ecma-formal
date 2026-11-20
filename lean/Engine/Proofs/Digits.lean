module

public import Engine.Model.Digits
public import Engine.Proofs.Binary64Round
public import Engine.Proofs.Binary64Ops

@[expose] public section

/-!
# Number::toString's digits meet step 5's condition, with k least

Over ℚ, for a finite positive binary64 value b with ℝ(b) = X and a radix r ≥ 2 (`digits_spec`): `digits b r` meets
the step's condition (`Valid`), and nothing that meets it has fewer digits.

* The reals that round to b (`ofRat v = b`) lie between X/2 and 3X/2 (`round_bounds`: the candidates 0 and the next
  value above X are no nearer), contain an interval around X (`round_near`: every other candidate is at least the
  spacing of the values at X away), and are an interval (`round_convex`: rounding is monotone, by the midpoint).
* So a tuple that meets the condition has n from e - 1 to e + 1 (`valid_exp`), and at its n one of the two clamped
  integers around X × r^(k-n) meets it too (`valid_tries`): the tuples `tries` holds decide each k
  (`at_complete`), and some k up to the fuel has one (`valid_exists`).
-/

namespace Engine.Model.Digits

open Engine.Binary64

/-! ## Powers of the radix -/

theorem one_le_pow {q : Rat} (h : 1 ≤ q) : ∀ n : Nat, 1 ≤ q ^ n
  | 0 => by simp
  | n + 1 => by
    rw [Rat.pow_succ]
    have := one_le_pow h n
    have : q ^ n * 1 ≤ q ^ n * q := Rat.mul_le_mul_of_nonneg_left h (by grind)
    grind

theorem rq_two {r : Nat} (hr : 2 ≤ r) : (2 : Rat) ≤ r := by
  have := Rat.natCast_le_natCast.2 hr
  simpa using this

theorem rq_ne {r : Nat} (hr : 2 ≤ r) : (r : Rat) ≠ 0 := by have := rq_two hr; grind

theorem zp_pos {r : Nat} (hr : 2 ≤ r) (z : Int) : 0 < (r : Rat) ^ z := Rat.zpow_pos (by have := rq_two hr; grind)

theorem zp_add {r : Nat} (hr : 2 ≤ r) (a b : Int) : (r : Rat) ^ (a + b) = (r : Rat) ^ a * (r : Rat) ^ b :=
  Rat.zpow_add (rq_ne hr) a b

theorem zp_one {r : Nat} : (r : Rat) ^ (1 : Int) = r := Rat.zpow_one _

theorem zp_le {r : Nat} (hr : 2 ≤ r) {a c : Int} (h : a ≤ c) : (r : Rat) ^ a ≤ (r : Rat) ^ c := by
  obtain ⟨n, hn⟩ := Int.eq_ofNat_of_zero_le (show 0 ≤ c - a by omega)
  rw [show c = a + n by omega, zp_add hr, Rat.zpow_natCast]
  have h1 := one_le_pow (show (1 : Rat) ≤ r by have := rq_two hr; grind) n
  have h2 := zp_pos hr a
  have : (r : Rat) ^ a * 1 ≤ (r : Rat) ^ a * (r : Rat) ^ n := Rat.mul_le_mul_of_nonneg_left h1 (by grind)
  grind

/-- r^(a+1) ≥ 2 r^a. -/
theorem zp_succ {r : Nat} (hr : 2 ≤ r) (a : Int) : 2 * (r : Rat) ^ a ≤ (r : Rat) ^ (a + 1) := by
  rw [zp_add hr, zp_one]
  have := zp_pos hr a
  have := rq_two hr
  have : (r : Rat) ^ a * 2 ≤ (r : Rat) ^ a * r := Rat.mul_le_mul_of_nonneg_left (rq_two hr) (by grind)
  grind

theorem zp_lt {r : Nat} (hr : 2 ≤ r) {a c : Int} (h : a < c) : (r : Rat) ^ a < (r : Rat) ^ c := by
  have := zp_succ hr a
  have := zp_le hr (show a + 1 ≤ c by omega)
  have := zp_pos hr a
  grind

theorem zp_nat {r : Nat} (j : Nat) : (r : Rat) ^ (j : Int) = ((r ^ j : Nat) : Rat) := by
  rw [Rat.zpow_natCast, Rat.natCast_pow]

theorem int_pow_cast (a : Int) (j : Nat) : ((a ^ j : Int) : Rat) = (a : Rat) ^ j := Rat.intCast_pow a j

/-- The k-digit bounds over ℚ: r^(k-1) and r^k. -/
theorem lo_cast {r : Nat} (k : Nat) (hk : 1 ≤ k) : (((r : Int) ^ (k - 1) : Int) : Rat) = (r : Rat) ^ ((k : Int) - 1) := by
  rw [int_pow_cast, Rat.intCast_natCast, ← Rat.zpow_natCast]
  congr 1
  omega

theorem hi_cast {r : Nat} (k : Nat) : (((r : Int) ^ k : Int) : Rat) = (r : Rat) ^ (k : Int) := by
  rw [int_pow_cast, Rat.intCast_natCast, Rat.zpow_natCast]

theorem inv_le_inv {a b : Rat} (ha : 0 < a) (h : a ≤ b) : b⁻¹ ≤ a⁻¹ := by
  have hb : 0 < b := by grind
  have hab : 0 < a * b := Rat.mul_pos ha hb
  apply Rat.le_of_mul_le_mul_left _ hab
  rw [Rat.mul_assoc, Rat.mul_inv_cancel _ (by grind), Rat.mul_comm a b, Rat.mul_assoc,
    Rat.mul_inv_cancel _ (by grind)]
  grind

theorem inv_lt_inv {a b : Rat} (ha : 0 < a) (h : a < b) : b⁻¹ < a⁻¹ := by
  have hb : 0 < b := by grind
  have hab : 0 < a * b := Rat.mul_pos ha hb
  apply (Rat.mul_lt_mul_left hab).1
  rw [Rat.mul_assoc, Rat.mul_inv_cancel _ (by grind), Rat.mul_comm a b, Rat.mul_assoc,
    Rat.mul_inv_cancel _ (by grind)]
  grind

/-- 2^j ≤ r^j. -/
theorem two_pow_le {r : Nat} (hr : 2 ≤ r) : ∀ j : Nat, (2 : Rat) ^ j ≤ (r : Rat) ^ j
  | 0 => by simp
  | j + 1 => by
    rw [Rat.pow_succ, Rat.pow_succ]
    have ih := two_pow_le hr j
    have h2 : (0 : Rat) < 2 ^ j := Rat.pow_pos (by decide)
    have h1 : (2 : Rat) ^ j * 2 ≤ (r : Rat) ^ j * 2 := Rat.mul_le_mul_of_nonneg_right ih (by decide)
    have h3 : (r : Rat) ^ j * 2 ≤ (r : Rat) ^ j * r := Rat.mul_le_mul_of_nonneg_left (rq_two hr) (by grind)
    grind

/-! ## The exponent -/

theorem nlog_spec {r : Nat} (hr : 2 ≤ r) : ∀ f n : Nat, 1 ≤ n → n ≤ f →
    r ^ nlog r f n ≤ n ∧ n < r ^ (nlog r f n + 1)
  | 0, n, h1, h2 => by omega
  | f + 1, n, h1, h2 => by
    unfold nlog
    split
    · simp; omega
    · rename_i h
      have hq : 1 ≤ n / r := (Nat.le_div_iff_mul_le (by omega)).2 (by omega)
      have hf : n / r ≤ f := by
        have := Nat.div_lt_self (show 0 < n by omega) (show 1 < r by omega)
        omega
      obtain ⟨a, b⟩ := nlog_spec hr f (n / r) hq hf
      refine ⟨?_, ?_⟩
      · rw [Nat.pow_succ]
        exact Nat.le_trans (Nat.mul_le_mul_right r a) (Nat.div_mul_le_self n r)
      · rw [Nat.pow_succ]
        have h3 := Nat.div_add_mod n r
        have h4 := Nat.mod_lt n (show 0 < r by omega)
        have h5 : r * (n / r + 1) ≤ r * r ^ (nlog r f (n / r) + 1) := Nat.mul_le_mul_left r b
        have h6 : r * (n / r + 1) = r * (n / r) + r := Nat.mul_succ r (n / r)
        have h7 : r * r ^ (nlog r f (n / r) + 1) = r ^ (nlog r f (n / r) + 1) * r := Nat.mul_comm _ _
        omega

/-- `expOf`: r^(e-1) ≤ X < r^e. -/
theorem expOf_spec {r : Nat} (hr : 2 ≤ r) {X : Rat} (hX : 0 < X) :
    (r : Rat) ^ (expOf r X - 1) ≤ X ∧ X < (r : Rat) ^ expOf r X := by
  unfold expOf
  split
  · rename_i h1
    have hF : 1 ≤ X.floor := Rat.le_floor_iff.2 (by simpa using h1)
    obtain ⟨a, b⟩ := nlog_spec hr X.floor.toNat X.floor.toNat (by omega) (Nat.le_refl _)
    generalize nlog r X.floor.toNat X.floor.toNat = L at a b
    have eF : ((X.floor.toNat : Nat) : Rat) = (X.floor : Rat) := by
      rw [← Rat.intCast_natCast, Int.toNat_of_nonneg (by omega)]
    have a' := Rat.natCast_le_natCast.2 a
    have b' := Rat.natCast_le_natCast.2 (show X.floor.toNat + 1 ≤ r ^ (L + 1) by omega)
    rw [Rat.natCast_add, eF] at b'
    rw [eF] at a'
    rw [show ((L : Int) + 1 - 1) = (L : Int) by omega, zp_nat, show ((L : Int) + 1) = ((L + 1 : Nat) : Int) by omega,
      zp_nat]
    have := Rat.floor_le X
    have := Rat.lt_floor_add_one X
    rw [Rat.intCast_add] at this
    simp only [natCast_one', Rat.intCast_one] at b' this ⊢
    grind
  · rename_i h1
    have hX1 : X < 1 := by grind
    have hY : 1 < X⁻¹ := by
      have := inv_lt_inv hX hX1
      rwa [show (1 : Rat)⁻¹ = 1 from Rat.inv_eq_of_mul_eq_one (Rat.mul_one 1)] at this
    have hc : 2 ≤ X⁻¹.ceil := by
      have : ¬ (X⁻¹.ceil ≤ 1) := fun h => by
        have := Rat.ceil_le_iff.1 h
        simp at this
        grind
      omega
    obtain ⟨a, b⟩ := nlog_spec hr (X⁻¹.ceil - 1).toNat (X⁻¹.ceil - 1).toNat (by omega) (Nat.le_refl _)
    generalize nlog r (X⁻¹.ceil - 1).toNat (X⁻¹.ceil - 1).toNat = L at a b
    have eC : (((X⁻¹.ceil - 1).toNat : Nat) : Rat) = ((X⁻¹.ceil - 1 : Int) : Rat) := by
      rw [← Rat.intCast_natCast, Int.toNat_of_nonneg (by omega)]
    have a' := Rat.natCast_le_natCast.2 a
    have b' := Rat.natCast_le_natCast.2 (show (X⁻¹.ceil - 1).toNat + 1 ≤ r ^ (L + 1) by omega)
    rw [Rat.natCast_add, eC] at b'
    rw [eC] at a'
    -- c - 1 < Y ≤ c
    have hlt : ((X⁻¹.ceil - 1 : Int) : Rat) < X⁻¹ := by
      have : ¬ (X⁻¹ ≤ ((X⁻¹.ceil - 1 : Int) : Rat)) := fun h => by
        have := Rat.ceil_le_iff.2 h
        omega
      grind
    have hle : X⁻¹ ≤ ((X⁻¹.ceil : Int) : Rat) := Rat.ceil_le_iff.1 (Int.le_refl _)
    rw [Rat.intCast_sub] at hlt b'
    simp only [Rat.intCast_one, natCast_one'] at hlt b'
    have p1 : ((r ^ L : Nat) : Rat) < X⁻¹ := by grind
    have p2 : X⁻¹ ≤ ((r ^ (L + 1) : Nat) : Rat) := by grind
    have q1 : 0 < ((r ^ L : Nat) : Rat) := by
      rw [← zp_nat]; exact zp_pos hr _
    have e1 : (r : Rat) ^ (-(L : Int)) = (((r ^ L : Nat) : Rat))⁻¹ := by rw [Rat.zpow_neg, zp_nat]
    have e2 : (r : Rat) ^ (-(L : Int) - 1) = (((r ^ (L + 1) : Nat) : Rat))⁻¹ := by
      rw [show -(L : Int) - 1 = -((L + 1 : Nat) : Int) by omega, Rat.zpow_neg, zp_nat]
    rw [e1, e2]
    have hXX : X = X⁻¹⁻¹ := (Rat.inv_inv X).symm
    refine ⟨?_, ?_⟩
    · rw [hXX]; exact inv_le_inv (by grind) p2
    · rw [hXX]; exact inv_lt_inv q1 p1

/-! ## The reals that round to b -/

section Round
variable {b : BitVec 64} {X : Rat}

/-- b's view is finite with value X. -/
abbrev Fin (b : BitVec 64) (X : Rat) : Prop := viewQ b = .finite X ∧ 0 < X

theorem fin_parts (h : Fin b X) : isFinite b = true ∧ isZero b = false ∧ toRat b = X := by
  rcases viewQ_cases b with ⟨va, -⟩ | ⟨va, -⟩ | ⟨va, -⟩ | ⟨va, -⟩ | ⟨va, -⟩ |
      ⟨x, va, -, -, hf, hz, -, -, -, hx, -, -⟩ <;> rw [h.1] at va <;> cases va
  exact ⟨hf, hz, hx⟩

theorem fin_finiteQ (h : Fin b X) : ∃ ev, finiteQ X ev := by
  obtain ⟨hf, hz, hx⟩ := fin_parts h
  exact ⟨_, hx ▸ toRat_finiteQ hf hz⟩

/-- A pattern whose view is b's is b. -/
theorem view_inj (h : Fin b X) {c : BitVec 64} (hc : viewQ c = .finite X) : c = b := by
  obtain ⟨hf, hz, hx⟩ := fin_parts h
  rcases viewQ_cases c with ⟨va, -⟩ | ⟨va, -⟩ | ⟨va, -⟩ | ⟨va, -⟩ | ⟨va, -⟩ |
      ⟨y, va, -, -, hfc, hzc, -, -, -, hy, -, -⟩ <;> rw [hc] at va <;> cases va
  exact toRat_inj hfc hzc hf hz (hy.trans hx.symm)

theorem viewFor_X (h : Fin b X) (v : Rat) : viewForQ v X = .finite X := by
  obtain ⟨ev, hq⟩ := fin_finiteQ h
  obtain ⟨h0, hb⟩ := finiteQ_bounds hq
  have h1 : X < 2 ^ 1024 := lt_of_le_lt (le_absQ X).1 hb
  have h2 : -X < 2 ^ 1024 := lt_of_le_lt (le_absQ X).2 hb
  unfold viewForQ
  rw [if_neg (Rat.ne_of_lt h1), if_neg fun h' => Rat.lt_irrefl (by rw [h', Rat.neg_neg] at h2; exact h2), if_neg h0]

/-- X rounds to b. -/
theorem round_X (h : Fin b X) : ofRat X = b := by
  obtain ⟨ev, hq⟩ := fin_finiteQ h
  exact view_inj h (ofRat_finite hq)

/-- What rounds to b has X as its nearest candidate. -/
theorem round_nearest (h : Fin b X) {v : Rat} (hv : ofRat v = b) : nearestQ v X := by
  have hv0 : v ≠ 0 := by
    rintro rfl
    rw [ofRat_zero] at hv
    have := h.1
    rw [← hv, viewQ_posZero] at this
    cases this
  obtain ⟨y, hy, hview⟩ := ofRat_view hv0
  rw [hv, h.1] at hview
  have : y = X := by
    unfold viewForQ at hview
    split at hview
    · cases hview
    · split at hview
      · cases hview
      · split at hview
        · split at hview <;> cases hview
        · cases hview; rfl
  exact this ▸ hy

/-- A real whose nearest candidate is X rounds to b. -/
theorem round_of_nearest (h : Fin b X) {v : Rat} (hv0 : v ≠ 0) (hy : ∀ y, nearestQ v y → y = X) : ofRat v = b := by
  obtain ⟨y, hn, hview⟩ := ofRat_view hv0
  rw [hy y hn, viewFor_X h] at hview
  exact view_inj h hview

/-- A candidate above X, at most 2X: the next value. -/
theorem cand_above (h : Fin b X) : ∃ Z ez, candQ Z ez ∧ X < Z ∧ Z ≤ 2 * X := by
  obtain ⟨ev, neg, m, k, hX, -, hb⟩ := fin_finiteQ h
  have hX0 := h.2
  have hI : (0 : Rat) < ((2 : Rat) ^ 1074)⁻¹ := Rat.inv_pos.2 (Rat.pow_pos (by decide))
  have hw : 0 < (2 : Rat) ^ k * ((2 : Rat) ^ 1074)⁻¹ := Rat.mul_pos (Rat.pow_pos (by decide)) hI
  have eF : ∀ (m' k' : Nat), formQ false m' k' = (m' : Rat) * ((2 : Rat) ^ k' * ((2 : Rat) ^ 1074)⁻¹) := by
    intro m' k'
    simp only [formQ, signed, Bool.false_eq_true, ↓reduceIte]
    rw [Rat.div_def, Rat.mul_assoc]
  have hneg : neg = false := by
    cases neg
    · rfl
    · exfalso
      have e : formQ true m k = -((m : Rat) * ((2 : Rat) ^ k * ((2 : Rat) ^ 1074)⁻¹)) := by
        simp only [formQ, signed, ↓reduceIte]
        rw [Rat.div_def, Rat.mul_assoc]
      have := Rat.mul_nonneg (Rat.natCast_nonneg (a := m)) (Rat.le_of_lt hw)
      rw [hX, e] at hX0
      grind
  subst hneg
  have e1 : formQ false (2 ^ 52) (k + 1) = ((2 ^ 53 : Nat) : Rat) * ((2 : Rat) ^ k * ((2 : Rat) ^ 1074)⁻¹) := by
    rw [eF, Rat.pow_succ, natCast_two_pow, natCast_two_pow,
      show (2 : Rat) ^ 53 = (2 : Rat) ^ 52 * 2 by rw [← Rat.pow_succ]]
    grind
  have e2 : (2 : Rat) ^ 1024 = ((2 ^ 53 : Nat) : Rat) * ((2 : Rat) ^ 2045 * ((2 : Rat) ^ 1074)⁻¹) := by
    rw [← Rat.mul_assoc, ← natCast_two_pow 2045, ← Rat.natCast_mul,
      show 2 ^ 53 * 2 ^ 2045 = 2 ^ 1024 * 2 ^ 1074 by rw [← Nat.pow_add, ← Nat.pow_add], Rat.natCast_mul,
      Rat.mul_assoc, natCast_two_pow 1074, Rat.mul_inv_cancel _ (Rat.ne_of_gt (Rat.pow_pos (by decide))), Rat.mul_one,
      natCast_two_pow]
  rw [eF] at hX
  generalize hW : (2 : Rat) ^ k * ((2 : Rat) ^ 1074)⁻¹ = W at hw hX e1
  have lt : ∀ a c : Nat, a < c → (a : Rat) * W < (c : Rat) * W := fun a c h =>
    (Rat.mul_lt_mul_right hw).2 (Rat.natCast_lt_natCast.2 h)
  have le : ∀ a c : Nat, a ≤ 2 * c → (a : Rat) * W ≤ 2 * ((c : Rat) * W) := fun a c h => by
    have := Rat.mul_le_mul_of_nonneg_right (Rat.natCast_le_natCast.2 h) (Rat.le_of_lt hw)
    rw [Rat.natCast_mul, Rat.mul_assoc] at this
    exact this
  rcases hb with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
  · by_cases hk : k = 2045
    · subst hk
      rw [hW] at e2
      refine ⟨2 ^ 1024, true, .inr (.inr ⟨.inl rfl, rfl⟩), ?_, ?_⟩
      · rw [e2, hX]; exact lt _ _ h2
      · rw [e2, hX]; exact le _ _ (by omega)
    · refine ⟨formQ false (2 ^ 52) (k + 1), true,
        .inl ⟨false, 2 ^ 52, k + 1, rfl, rfl, .inl ⟨Nat.le_refl _, by decide, by omega⟩⟩, ?_, ?_⟩
      · rw [e1, hX]; exact lt _ _ h2
      · rw [e1, hX]; exact le _ _ (by omega)
  · subst h3
    refine ⟨formQ false (m + 1) 0, (m + 1) % 2 == 0, .inl ⟨false, m + 1, 0, rfl, rfl, ?_⟩, ?_, ?_⟩
    · by_cases hm : m + 1 < 2 ^ 52
      · exact .inr ⟨by omega, hm, rfl⟩
      · exact .inl ⟨by omega, by omega, by omega⟩
    · rw [eF, hW, hX]; exact lt _ _ (by omega)
    · rw [eF, hW, hX]; exact le _ _ (by omega)

theorem absQ_cases (x : Rat) : (absQ x = x ∧ 0 ≤ x) ∨ (absQ x = -x ∧ x < 0) := by
  unfold absQ; split
  · right; grind
  · left; grind

theorem abs_tri (a b c : Rat) : absQ (a - c) ≤ absQ (b - a) + absQ (b - c) := by
  rcases absQ_cases (a - c) with e1 | e1 <;> rcases absQ_cases (b - a) with e2 | e2 <;>
    rcases absQ_cases (b - c) with e3 | e3 <;> grind

/-- What rounds to b lies between X/2 and 3X/2. -/
theorem round_bounds (h : Fin b X) {v : Rat} (hv : ofRat v = b) : X / 2 ≤ v ∧ v ≤ 3 * X / 2 := by
  obtain ⟨ev, -, hn⟩ := round_nearest h hv
  obtain ⟨Z, ez, hZ, h1, h2⟩ := cand_above h
  have a := (hn 0 true (.inr (.inl ⟨rfl, rfl⟩))).1
  have c := (hn Z ez hZ).1
  have := h.2
  rcases absQ_cases (v - 0) with e1 | e1 <;> rcases absQ_cases (v - X) with e2 | e2 <;>
    rcases absQ_cases (v - Z) with e3 | e3 <;> constructor <;> grind

/-- Rounding is monotone: what lies between two reals that round to b rounds to b. -/
theorem round_convex (h : Fin b X) {a c v : Rat} (ha : ofRat a = b) (hc : ofRat c = b) (h1 : a ≤ v)
    (h2 : v ≤ c) : ofRat v = b := by
  by_cases e1 : v = a
  · exact e1 ▸ ha
  by_cases e2 : v = c
  · exact e2 ▸ hc
  have ha0 := (round_bounds h ha).1
  have := h.2
  refine round_of_nearest h (by grind) fun y hy => ?_
  obtain ⟨_, hyc, hyn⟩ := hy
  obtain ⟨_, -, han⟩ := round_nearest h ha
  obtain ⟨_, -, hcn⟩ := round_nearest h hc
  obtain ⟨evX, hX⟩ := fin_finiteQ h
  have v1 := (hyn X evX (.inl hX)).1
  have a1 := (han y _ hyc).1
  have c1 := (hcn y _ hyc).1
  rcases absQ_cases (v - X) with e1 | e1 <;> rcases absQ_cases (v - y) with e2 | e2 <;>
    rcases absQ_cases (a - X) with e3 | e3 <;> rcases absQ_cases (a - y) with e4 | e4 <;>
    rcases absQ_cases (c - X) with e5 | e5 <;> rcases absQ_cases (c - y) with e6 | e6 <;> grind

/-- The spacing of the values at X: every other candidate is at least 2^p away, and X is a multiple of 2^p. -/
theorem cand_spacing (h : Fin b X) : ∃ p : Int, -1074 ≤ p ∧ pow2 p ≤ X ∧
    ∀ z ez, candQ z ez → z ≠ X → pow2 p ≤ absQ (z - X) := by
  obtain ⟨ev, hq⟩ := fin_finiteQ h
  have hq' := hq
  obtain ⟨neg, m, k, hX, -, hb⟩ := hq
  have hX0 := h.2
  rw [formQ_eq] at hX
  have hneg : neg = false := by
    cases neg
    · rfl
    · exfalso
      have := Rat.mul_nonneg (Rat.natCast_nonneg (a := m)) (Rat.le_of_lt (pow2_pos ((k : Int) - 1074)))
      simp only [hX, signed, if_true] at hX0
      grind
  subst hneg
  simp only [signed, Bool.false_eq_true, if_false] at hX
  -- the grid: 2^(k - 1075) for a normal value of k ≥ 1, else 2^-1074
  let p : Int := if k = 0 then -1074 else (k : Int) - 1075
  let i : Int := if k = 0 then m else 2 * m
  have hXp : X = (i : Rat) * pow2 p := by
    by_cases hk : k = 0
    · simp only [p, i, hk, if_true]; rw [hX, hk]; simp [Rat.intCast_natCast]
    · simp only [p, i, hk, if_false]
      rw [hX, show (k : Int) - 1074 = ((k : Int) - 1075) + 1 by omega, pow2_add, show pow2 1 = 2 by decide]
      simp only [Rat.intCast_mul, Rat.intCast_natCast]
      have : ((2 : Int) : Rat) = 2 := rfl
      rw [this]; grind
  have hp : -1074 ≤ p := by simp only [p]; split <;> omega
  have hpos := pow2_pos p
  have hi : 1 ≤ i := by
    simp only [i]
    rcases hb with ⟨h1, -, -⟩ | ⟨h1, -, -⟩ <;> split <;> omega
  refine ⟨p, hp, ?_, ?_⟩
  · rw [hXp]
    have : (1 : Rat) ≤ (i : Rat) := by exact_mod_cast hi
    have := Rat.mul_le_mul_of_nonneg_right this (Rat.le_of_lt hpos)
    grind
  · intro z ez hz hne
    by_cases hg : p = -1074 ∨ pow2 (p + 52) ≤ absQ z
    · obtain ⟨j, hj⟩ := candQ_grid hz hp hg
      have hji : j ≠ i := fun e => hne (by rw [hj, hXp, e])
      have : z - X = ((j - i : Int) : Rat) * pow2 p := by
        rw [hj, hXp, Rat.intCast_sub]; grind
      rw [this, Rat.mul_comm, absQ_mul_pos _ hpos]
      have h1 : (1 : Rat) ≤ absQ ((j - i : Int) : Rat) := by
        have hd : j - i ≤ -1 ∨ 1 ≤ j - i := by omega
        rcases hd with hd | hd
        · have := Rat.intCast_le_intCast.2 hd
          rw [Rat.intCast_neg, Rat.intCast_one] at this
          rcases absQ_cases ((j - i : Int) : Rat) with e | e <;> grind
        · have := Rat.intCast_le_intCast.2 hd
          rw [Rat.intCast_one] at this
          rcases absQ_cases ((j - i : Int) : Rat) with e | e <;> grind
      have := Rat.mul_le_mul_of_nonneg_left h1 (Rat.le_of_lt hpos)
      grind
    · simp only [not_or] at hg
      obtain ⟨hp1, hz1⟩ := hg
      have hk : k ≠ 0 := by intro hk; apply hp1; simp [p, hk]
      have hm : 2 ^ 52 ≤ m := by rcases hb with ⟨h1, -, -⟩ | ⟨-, -, h3⟩ <;> omega
      have hX2 : pow2 (p + 53) ≤ X := by
        rw [hX]
        have e : p + 53 = 52 + ((k : Int) - 1074) := by simp only [p, hk, if_false]; omega
        rw [e, pow2_add, show pow2 52 = ((2 ^ 52 : Nat) : Rat) by simp [pow2]]
        exact Rat.mul_le_mul_of_nonneg_right (Rat.natCast_le_natCast.2 hm) (Rat.le_of_lt (pow2_pos _))
      have e1 : pow2 (p + 53) = 2 * pow2 (p + 52) := by
        rw [show p + 53 = (p + 52) + 1 by omega, pow2_add, show pow2 1 = 2 by decide, Rat.mul_comm]
      have e2 : pow2 p ≤ pow2 (p + 52) := pow2_le_of_le (by omega)
      have hz2 := Rat.not_le.1 hz1
      have := le_absQ z
      rcases absQ_cases (z - X) with e1 | e1 <;> rcases absQ_cases z with e2 | e2 <;> grind

/-- An interval around X rounds to b. -/
theorem round_near (h : Fin b X) : ∃ p : Int, -1075 ≤ p ∧ ∀ v, absQ (v - X) < pow2 p → ofRat v = b := by
  obtain ⟨p, hp, hpX, hsp⟩ := cand_spacing h
  have e : pow2 p = 2 * pow2 (p - 1) := by
    rw [show p = (p - 1) + 1 by omega, pow2_add, show pow2 1 = 2 by decide, Rat.mul_comm]; simp
  have hp1 := pow2_pos (p - 1)
  refine ⟨p - 1, by omega, fun v hv => ?_⟩
  have hv0 : v ≠ 0 := by
    rintro rfl
    rcases absQ_cases (0 - X) with e1 | e1 <;> grind
  refine round_of_nearest h hv0 fun y hy => ?_
  obtain ⟨_, hyc, hyn⟩ := hy
  obtain ⟨evX, hX⟩ := fin_finiteQ h
  have v1 := Rat.not_lt.1 (hyn X evX (.inl hX)).1
  refine Classical.byContradiction fun hne => ?_
  have h3 := hsp y _ hyc hne
  have tri := abs_tri y v X
  clear hyn hsp
  generalize absQ (y - X) = A at h3 tri
  generalize absQ (v - y) = B at v1 tri
  generalize absQ (v - X) = C at v1 tri hv
  generalize pow2 p = P at e h3
  generalize pow2 (p - 1) = Q at e hv
  grind

end Round

/-! ## The condition -/

/-- Step 5's condition on n, k and s for b at radix r. -/
def Valid (b : BitVec 64) (r : Nat) (n : Int) (k : Nat) (s : Int) : Prop :=
  1 ≤ k ∧ (r : Int) ^ (k - 1) ≤ s ∧ s < (r : Int) ^ k ∧ ofRat ((s : Rat) * (r : Rat) ^ (n - k)) = b

theorem meets_iff {b : BitVec 64} {r : Nat} {n : Int} {k : Nat} {s : Int} :
    meets b r n k s = true ↔ (r : Int) ^ (k - 1) ≤ s ∧ s < (r : Int) ^ k ∧ ofRat ((s : Rat) * (r : Rat) ^ (n - k)) = b := by
  simp [meets, and_assoc]

section Cond
variable {b : BitVec 64} {X : Rat} {r : Nat}

/-- The value s × r^(n-k) of a tuple that meets the condition lies from r^(n-1) to r^n. -/
theorem valid_value (hr : 2 ≤ r) {n : Int} {k : Nat} {s : Int} (hv : Valid b r n k s) :
    (r : Rat) ^ (n - 1) ≤ (s : Rat) * (r : Rat) ^ (n - k) ∧ (s : Rat) * (r : Rat) ^ (n - k) < (r : Rat) ^ n := by
  obtain ⟨hk, h1, h2, -⟩ := hv
  have a := Rat.intCast_le_intCast.2 h1
  have c := Rat.intCast_lt_intCast.2 h2
  rw [lo_cast k hk] at a
  rw [hi_cast k] at c
  have hq := zp_pos hr (n - k)
  have e1 : (r : Rat) ^ (n - 1) = (r : Rat) ^ ((k : Int) - 1) * (r : Rat) ^ (n - k) := by
    rw [← zp_add hr]; congr 1; omega
  have e2 : (r : Rat) ^ n = (r : Rat) ^ (k : Int) * (r : Rat) ^ (n - k) := by
    rw [← zp_add hr]; congr 1; omega
  rw [e1, e2]
  exact ⟨Rat.mul_le_mul_of_nonneg_right a (Rat.le_of_lt hq), (Rat.mul_lt_mul_right hq).2 c⟩

/-- A tuple that meets the condition has n from e - 1 to e + 1. -/
theorem valid_exp (hr : 2 ≤ r) (h : Fin b X) {e : Int} (he : (r : Rat) ^ (e - 1) ≤ X ∧ X < (r : Rat) ^ e)
    {n : Int} {k : Nat} {s : Int} (hv : Valid b r n k s) : e - 1 ≤ n ∧ n ≤ e + 1 := by
  obtain ⟨v1, v2⟩ := valid_value hr hv
  obtain ⟨b1, b2⟩ := round_bounds h hv.2.2.2
  have hX := h.2
  constructor
  · refine Classical.byContradiction fun hn => ?_
    have := zp_le hr (show n ≤ e - 2 by omega)
    have := zp_succ hr (e - 2)
    rw [show e - 2 + 1 = e - 1 by omega] at this
    grind
  · refine Classical.byContradiction fun hn => ?_
    have := zp_le hr (show e + 1 ≤ n - 1 by omega)
    have := zp_succ hr e
    grind

theorem clamp_lo {v lo hi : Int} (h : lo ≤ hi) : lo ≤ clamp v lo hi ∧ clamp v lo hi ≤ hi := by
  unfold clamp; split <;> (try split) <;> omega

/-- At a tuple's n, one of the two clamped integers around X × r^(k-n) meets the condition too. -/
theorem valid_tries (hr : 2 ≤ r) (h : Fin b X) {n : Int} {k : Nat} {s : Int} (hv : Valid b r n k s) :
    let f := (X * (r : Rat) ^ ((k : Int) - n)).floor
    Valid b r n k (clamp f ((r : Int) ^ (k - 1)) ((r : Int) ^ k - 1)) ∨
      Valid b r n k (clamp (f + 1) ((r : Int) ^ (k - 1)) ((r : Int) ^ k - 1)) := by
  intro f
  obtain ⟨hk, h1, h2, h3⟩ := hv
  have hq := zp_pos hr (n - k)
  have hinv : (r : Rat) ^ ((k : Int) - n) * (r : Rat) ^ (n - k) = 1 := by
    rw [← zp_add hr, show (k : Int) - n + (n - k) = 0 by omega, Rat.zpow_zero]
  have hlohi : (r : Int) ^ (k - 1) ≤ (r : Int) ^ k - 1 := by
    have : (r : Int) ^ k = (r : Int) ^ (k - 1) * r := by
      rw [← Int.pow_succ]; congr 1; omega
    have : 0 < (r : Int) ^ (k - 1) := Int.pow_pos (by omega)
    have : (r : Int) ^ (k - 1) * 2 ≤ (r : Int) ^ (k - 1) * r := Int.mul_le_mul_of_nonneg_left (by omega) (by omega)
    omega
  have hXv := round_X h
  -- X' × r^(n-k) = X
  have eX : X * (r : Rat) ^ ((k : Int) - n) * (r : Rat) ^ (n - k) = X := by rw [Rat.mul_assoc, hinv, Rat.mul_one]
  generalize hX' : X * (r : Rat) ^ ((k : Int) - n) = X' at eX
  have hf : f = X'.floor := by simp only [f, hX']
  by_cases hs : (s : Rat) ≤ X'
  · left
    obtain ⟨c1, c2⟩ := clamp_lo (v := f) hlohi
    have hsf : s ≤ f := hf ▸ Rat.le_floor_iff.2 hs
    have hc1 : s ≤ clamp f ((r : Int) ^ (k - 1)) ((r : Int) ^ k - 1) := by unfold clamp; split <;> (try split) <;> omega
    have hc2 : clamp f ((r : Int) ^ (k - 1)) ((r : Int) ^ k - 1) ≤ f := by unfold clamp; split <;> (try split) <;> omega
    refine ⟨hk, c1, by omega, ?_⟩
    refine round_convex h h3 hXv ?_ ?_
    · exact Rat.mul_le_mul_of_nonneg_right (Rat.intCast_le_intCast.2 hc1) (Rat.le_of_lt hq)
    · rw [← eX]
      refine Rat.mul_le_mul_of_nonneg_right ?_ (Rat.le_of_lt hq)
      have := Rat.intCast_le_intCast.2 hc2
      have := Rat.floor_le X'
      rw [← hf] at this
      grind
  · right
    have hs' : X' < (s : Rat) := Rat.not_le.1 hs
    obtain ⟨c1, c2⟩ := clamp_lo (v := f + 1) hlohi
    have hsf : f + 1 ≤ s := by
      have := (Rat.floor_lt_iff (a := X') (x := s)).2 hs'
      omega
    have hc1 : clamp (f + 1) ((r : Int) ^ (k - 1)) ((r : Int) ^ k - 1) ≤ s := by
      unfold clamp; split <;> (try split) <;> omega
    have hc2 : f + 1 ≤ clamp (f + 1) ((r : Int) ^ (k - 1)) ((r : Int) ^ k - 1) := by
      unfold clamp; split <;> (try split) <;> omega
    refine ⟨hk, c1, by omega, ?_⟩
    refine round_convex h hXv h3 ?_ ?_
    · rw [← eX]
      refine Rat.mul_le_mul_of_nonneg_right ?_ (Rat.le_of_lt hq)
      have := Rat.intCast_le_intCast.2 hc2
      have := Rat.lt_floor_add_one X'
      rw [← hf] at this
      grind
    · exact Rat.mul_le_mul_of_nonneg_right (Rat.intCast_le_intCast.2 hc1) (Rat.le_of_lt hq)

theorem best_mem {X : Rat} {k : Nat} : ∀ {l : List (Int × Int)} {t : Int × Int}, best r X k l = some t → t ∈ l
  | [], _, h => by simp [best] at h
  | a :: l, t, h => by
    simp only [best, Option.some.injEq] at h
    subst h
    have : ∀ (acc : Int × Int) (l' : List (Int × Int)), acc ∈ a :: l → (∀ c ∈ l', c ∈ a :: l) →
        l'.foldl (fun a c => if better r X k c a then c else a) acc ∈ a :: l := by
      intro acc l'
      induction l' generalizing acc with
      | nil => intro h _; exact h
      | cons c l' ih =>
        intro hacc hl
        simp only [List.foldl_cons]
        apply ih
        · split
          · exact hl c (by simp)
          · exact hacc
        · intro c' hc'; exact hl c' (by simp [hc'])
    exact this a l (by simp) (fun c hc => by simp [hc])

/-- A tuple taken at k meets the condition. -/
theorem at_valid {e : Int} {k : Nat} {n s : Int} (hk : 1 ≤ k) (h : at? b r X e k = some (n, s)) :
    Valid b r n k s := by
  have := List.mem_filter.1 (best_mem h)
  exact ⟨hk, meets_iff.1 this.2⟩

/-- Where a tuple with k digits meets the condition, one is taken at k. -/
theorem at_complete (hr : 2 ≤ r) (h : Fin b X) {e : Int} (he : (r : Rat) ^ (e - 1) ≤ X ∧ X < (r : Rat) ^ e)
    {n : Int} {k : Nat} {s : Int} (hv : Valid b r n k s) : (at? b r X e k).isSome := by
  obtain ⟨n1, n2⟩ := valid_exp hr h he hv
  have hn : n ∈ [e - 1, e, e + 1] := by simp; omega
  have hin : ∃ c, Valid b r n k c ∧ (n, c) ∈ tries r X e k := by
    rcases valid_tries hr h hv with hc | hc
    · exact ⟨_, hc, List.mem_flatMap.2 ⟨n, hn, by simp⟩⟩
    · exact ⟨_, hc, List.mem_flatMap.2 ⟨n, hn, by simp⟩⟩
  obtain ⟨c, hc, hm⟩ := hin
  have hf : (n, c) ∈ (tries r X e k).filter (fun t => meets b r t.1 k t.2) :=
    List.mem_filter.2 ⟨hm, meets_iff.2 hc.2⟩
  unfold at?
  generalize (tries r X e k).filter (fun t => meets b r t.1 k t.2) = l at hf
  cases l with
  | nil => simp at hf
  | cons a l => simp [best]

/-- Some k up to the fuel has a tuple that meets the condition. -/
theorem valid_exists (hr : 2 ≤ r) (h : Fin b X) {e : Int} (he : (r : Rat) ^ (e - 1) ≤ X ∧ X < (r : Rat) ^ e) :
    ∃ k n s, 1 ≤ k ∧ k ≤ fuel ∧ Valid b r n k s := by
  obtain ⟨p, hp, hnear⟩ := round_near h
  obtain ⟨ev, hq⟩ := fin_finiteQ h
  have hX0 := h.2
  have hX1 : X < 2 ^ 1024 := lt_of_le_lt (le_absQ X).1 (finiteQ_bounds hq).2
  have he1 : e ≤ 1024 := by
    refine Classical.byContradiction fun hc => ?_
    have e1 : (r : Rat) ^ (e - 1) = (r : Rat) ^ (e - 1).toNat := by
      rw [← Rat.zpow_natCast]; congr 1; omega
    have := two_pow_le hr (e - 1).toNat
    have h2 : (2 : Rat) ^ 1024 ≤ (2 : Rat) ^ (e - 1).toNat := by
      rw [← natCast_two_pow, ← natCast_two_pow]
      exact Rat.natCast_le_natCast.2 (Nat.pow_le_pow_right (by decide) (by omega))
    grind
  let J : Nat := (1 - p).toNat
  let kk : Nat := max 1 (e + J).toNat
  have hkk1 : 1 ≤ kk := Nat.le_max_left _ _
  have hkk2 : e + J ≤ kk := by simp only [kk]; omega
  have hkkf : kk ≤ fuel := by simp only [kk, J, fuel]; omega
  let D : Nat := (kk - e).toNat
  have hD : (kk : Int) - e = D := by simp only [D]; omega
  have hDp : -(D : Int) ≤ p := by simp only [D] at hD ⊢; omega
  have hq1 := zp_pos hr ((kk : Int) - e)
  have hq2 := zp_pos hr (e - kk)
  have hinv : (r : Rat) ^ ((kk : Int) - e) * (r : Rat) ^ (e - kk) = 1 := by
    rw [← zp_add hr, show (kk : Int) - e + (e - kk) = 0 by omega, Rat.zpow_zero]
  generalize hX' : X * (r : Rat) ^ ((kk : Int) - e) = X'
  have eX : X' * (r : Rat) ^ (e - kk) = X := by rw [← hX', Rat.mul_assoc, hinv, Rat.mul_one]
  have hlo : (r : Rat) ^ ((kk : Int) - 1) ≤ X' := by
    rw [← hX', show (kk : Int) - 1 = (e - 1) + ((kk : Int) - e) by omega, zp_add hr]
    exact Rat.mul_le_mul_of_nonneg_right he.1 (Rat.le_of_lt hq1)
  have hhi : X' < (r : Rat) ^ (kk : Int) := by
    have := (Rat.mul_lt_mul_right hq1).2 he.2
    rw [← zp_add hr, show e + ((kk : Int) - e) = kk by omega] at this
    rw [← hX']; exact this
  refine ⟨kk, e, X'.floor, hkk1, hkkf, hkk1, ?_, ?_, ?_⟩
  · apply Rat.le_floor_iff.2
    rw [lo_cast kk hkk1]
    exact hlo
  · have := Rat.floor_le X'
    have : ((X'.floor : Int) : Rat) < (((r : Int) ^ kk : Int) : Rat) := by rw [hi_cast]; grind
    exact Rat.intCast_lt_intCast.1 this
  · apply hnear
    have a := Rat.floor_le X'
    have c := Rat.lt_floor_add_one X'
    rw [Rat.intCast_add, Rat.intCast_one] at c
    have a' := Rat.mul_le_mul_of_nonneg_right a (Rat.le_of_lt hq2)
    have c' := (Rat.mul_lt_mul_right hq2).2 c
    rw [eX] at a'
    rw [eX, Rat.add_mul, Rat.one_mul] at c'
    -- r^(e-kk) ≤ 2^(-D) ≤ 2^p
    have hb : (r : Rat) ^ (e - kk) ≤ pow2 p := by
      have e1 : (r : Rat) ^ (e - kk) = (((r : Rat) ^ D))⁻¹ := by
        rw [show e - (kk : Int) = -(D : Int) by omega, Rat.zpow_neg, Rat.zpow_natCast]
      have e2 : pow2 (-(D : Int)) = (((2 : Rat) ^ D))⁻¹ := by
        rw [pow2_eq, Rat.zpow_neg, Rat.zpow_natCast]
      rw [e1]
      exact Rat.le_trans (inv_le_inv (Rat.pow_pos (by decide)) (two_pow_le hr D)) (by rw [← e2]; exact pow2_le_of_le hDp)
    rcases absQ_cases (X'.floor * (r : Rat) ^ (e - kk) - X) with e1 | e1 <;> grind

theorem search_spec {e : Int} : ∀ (f k0 : Nat) {n : Int} {k : Nat} {s : Int},
    search b r X e f k0 = some (n, k, s) →
      k0 ≤ k ∧ at? b r X e k = some (n, s) ∧ ∀ j, k0 ≤ j → j < k → at? b r X e j = none
  | 0, k0, _, _, _, h => by simp [search] at h
  | f + 1, k0, n, k, s, h => by
    simp only [search] at h
    cases hat : at? b r X e k0 with
    | some t =>
      obtain ⟨n', s'⟩ := t
      simp only [hat, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      exact ⟨Nat.le_refl _, hat, fun j h1 h2 => by omega⟩
    | none =>
      simp only [hat] at h
      obtain ⟨a, c, d⟩ := search_spec f (k0 + 1) h
      refine ⟨by omega, c, fun j h1 h2 => ?_⟩
      by_cases hj : j = k0
      · subst hj; exact hat
      · exact d j (by omega) h2

theorem search_some {e : Int} : ∀ (f k0 k : Nat), k0 ≤ k → k < k0 + f → (at? b r X e k).isSome →
    (search b r X e f k0).isSome
  | 0, _, _, h1, h2, _ => by omega
  | f + 1, k0, k, h1, h2, hk => by
    simp only [search]
    cases hat : at? b r X e k0 with
    | some t => obtain ⟨n, s⟩ := t; simp
    | none =>
      have : k ≠ k0 := by rintro rfl; rw [hat] at hk; simp at hk
      exact search_some f (k0 + 1) k (by omega) (by omega) hk

theorem search_first {e : Int} : ∀ (f k0 : Nat) {k : Nat} {n s : Int}, k0 ≤ k → k < k0 + f →
    (∀ j, k0 ≤ j → j < k → at? b r X e j = none) → at? b r X e k = some (n, s) →
    search b r X e f k0 = some (n, k, s)
  | 0, _, _, _, _, h1, h2, _, _ => by omega
  | f + 1, k0, k, n, s, h1, h2, hn, hk => by
    simp only [search]
    by_cases e0 : k = k0
    · subst e0; rw [hk]
    · rw [hn k0 (Nat.le_refl _) (by omega)]
      exact search_first f (k0 + 1) (by omega) (by omega) (fun j a c => hn j (by omega) c) hk

end Cond

/-- Number::toString's digits for a finite positive b at a radix r ≥ 2: they meet step 5's condition, and nothing
that meets it has fewer digits. -/
theorem digits_spec {b : BitVec 64} {X : Rat} {r : Nat} (hr : 2 ≤ r) (h : Fin b X) :
    Valid b r (digits b r).1 (digits b r).2.1 (digits b r).2.2 ∧
      ∀ n k s, Valid b r n k s → (digits b r).2.1 ≤ k := by
  obtain ⟨-, -, hX⟩ := fin_parts h
  have he := expOf_spec hr h.2
  obtain ⟨k, n, s, hk1, hkf, hv⟩ := valid_exists hr h he
  have hs : (search b r X (expOf r X) fuel 1).isSome :=
    search_some _ _ k hk1 (by omega) (at_complete hr h he hv)
  obtain ⟨⟨n', k', s'⟩, hsome⟩ := Option.isSome_iff_exists.1 hs
  obtain ⟨h1, h2, h3⟩ := search_spec fuel 1 hsome
  have hd : digits b r = (n', k', s') := by simp [digits, hX, hsome]
  rw [hd]
  refine ⟨at_valid h1 h2, fun n k s hv => ?_⟩
  refine Classical.byContradiction fun hlt => ?_
  simp only at hlt
  have := h3 k hv.1 (by omega)
  have := at_complete hr h he hv
  simp_all

/-! ## The closest tuple -/

theorem dist_nonneg (r : Nat) (X : Rat) (k : Nat) (t : Int × Int) : 0 ≤ dist r X k t := by
  unfold dist; dsimp only; split <;> grind

/-- `best` takes the one tuple at distance 0, where there is one. -/
theorem best_zero {r : Nat} {X : Rat} {k : Nat} {l : List (Int × Int)} {t : Int × Int} (ht : t ∈ l)
    (h0 : dist r X k t = 0) (hu : ∀ u ∈ l, dist r X k u = 0 → u = t) : best r X k l = some t := by
  cases l with
  | nil => simp at ht
  | cons a l =>
    simp only [best, Option.some.injEq]
    have key : ∀ (rest : List (Int × Int)) (acc : Int × Int), acc ∈ a :: l → (∀ c ∈ rest, c ∈ a :: l) →
        (acc = t ∨ t ∈ rest) → rest.foldl (fun a c => if better r X k c a then c else a) acc = t := by
      intro rest
      induction rest with
      | nil => intro acc _ _ h; simpa using h
      | cons c rest ih =>
        intro acc hacc hl h
        simp only [List.foldl_cons]
        have hc : c ∈ a :: l := hl c (by simp)
        apply ih _ (by split; exact hc; exact hacc) (fun c' hc' => hl c' (by simp [hc']))
        by_cases ha : acc = t
        · left
          subst ha
          split
          · rename_i hb
            simp only [better, Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true, beq_iff_eq] at hb
            have := dist_nonneg r X k c
            rcases hb with hb | ⟨hb, -⟩
            · grind
            · exact hu c hc (by grind)
          · rfl
        · rcases h with h | h
          · exact absurd h ha
          · simp only [List.mem_cons] at h
            rcases h with rfl | h
            · left
              have hpos : 0 < dist r X k acc := by
                have := dist_nonneg r X k acc
                have : dist r X k acc ≠ 0 := fun e => ha (hu acc hacc e)
                grind
              rw [if_pos (by simp [better, h0, hpos])]
            · right; exact h
    have ht' : a = t ∨ t ∈ l := by
      simp only [List.mem_cons] at ht
      rcases ht with e | e
      · exact .inl e.symm
      · exact .inr e
    exact key l a (by simp) (fun c hc => by simp [hc]) ht'

/-- The exponent is the one integer e with r^(e-1) ≤ X < r^e. -/
theorem exp_unique {r : Nat} (hr : 2 ≤ r) {X : Rat} {e e' : Int} (h : (r : Rat) ^ (e - 1) ≤ X ∧ X < (r : Rat) ^ e)
    (h' : (r : Rat) ^ (e' - 1) ≤ X ∧ X < (r : Rat) ^ e') : e = e' := by
  rcases Int.lt_trichotomy e e' with c | c | c
  · have := zp_le hr (show e ≤ e' - 1 by omega); grind
  · exact c
  · have := zp_le hr (show e' ≤ e - 1 by omega); grind


/-- `decExp`: 10^e ≤ X < 10^(e+1). -/
theorem decExp_spec {X : Rat} (hX : 0 < X) :
    ((10 : Nat) : Rat) ^ decExp X ≤ X ∧ X < ((10 : Nat) : Rat) ^ (decExp X + 1) := by
  unfold decExp
  dsimp only
  split
  · rename_i e he
    have := List.find?_some he
    simpa [isDecExp] using this
  · have := expOf_spec (r := 10) (by decide) hX
    rw [show expOf 10 X - 1 + 1 = expOf 10 X by omega]
    exact this

end Engine.Model.Digits
