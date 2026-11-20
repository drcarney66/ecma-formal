module

public import Engine.Proofs.Step.Rows.LoopSkip.Nearest
public import Engine.Proofs.Math
public import Engine.Proofs.Num

@[expose] public section

/-!
# Number::toString at the integer Numbers below 2^53

`lsIntKeys`: the entry's Number::toString (`numberToStr`) at the Number of an integer 1 ≤ i < 2^53 and radix 10
answers the decimal digits of i: the arithmetic fact `LsIntKeys` the HasProperty loop's skip assumes. Step 5's n, k
and s there are the digits of i without its trailing zeros (`lsik_digits10`, the engine's `Digits.digits`, its search
followed: no tuple with fewer digits meets the condition, and the one with those digits is at distance 0).
-/

namespace Engine.Machine

open Ecma Ecma.Machine Engine.Accel
open Engine.Model (MathVal)
open Engine.Model.Digits (Fin absQ_cases)

/-- The radix. -/
abbrev lsikTen : MathVal := MathVal.int ((10 : Nat) : Int)

theorem lsik_ofQ_int (z : Int) : MathVal.ofQ (z : Rat) = .int z :=
  MathVal.toQ_inj (by rw [MathVal.toQ_ofQ]; rfl)

theorem lsik_empty : (F.strLit "" : Array UInt16) = #[] := by
  show Model.utf16 "" = #[]
  unfold Model.utf16
  rw [String.foldl_eq_foldl_toList]
  rfl

/-! ## The Number of an integer -/

/-- The Number of an integer 0 < |v| ≤ 2^53 is exactly v. -/
theorem lsik_view (v : Int) (h0 : v ≠ 0) (h : v.natAbs ≤ 2 ^ 53) :
    F.numView (F.numOf (MathVal.int v)) = .finite (MathVal.int v) := by
  rw [Engine.Impl.view_numOf]
  show Model.mapV (Binary64.viewQ (Binary64.ofRat (v : Rat))) = _
  rw [Binary64.ofRat_int h0 h]
  show NumView.finite (MathVal.ofQ (v : Rat)) = _
  rw [lsik_ofQ_int]

/-! ## Step 5 at an integer -/

/-- The pattern of the Number of an integer 0 < |v| ≤ 2^53 is its rounding. -/
theorem lsik_bits (v : Int) (h0 : v ≠ 0) (h : v.natAbs ≤ 2 ^ 53) :
    (F.numOf (MathVal.int v)).1 = Binary64.ofRat (v : Rat) := by
  have hv := Binary64.ofRat_int h0 h
  have hn : Binary64.isNaN (Binary64.ofRat (v : Rat)) = false := by
    rcases Binary64.viewQ_cases (Binary64.ofRat (v : Rat)) with ⟨va, -⟩ | ⟨va, -⟩ | ⟨va, -⟩ | ⟨va, -⟩ | ⟨va, -⟩ |
        ⟨y, va, hn, -⟩ <;> rw [hv] at va <;> cases va
    exact hn
  have e : F.numOf (MathVal.int v) = Model.Num.of (Binary64.ofRat (v : Rat)) := rfl
  rw [e]
  simp [Model.Num.of, hn]

theorem lsik_fin (i : Nat) (hi : 0 < i) (hi53 : i < 2 ^ 53) :
    Fin (Binary64.ofRat ((i : Int) : Rat)) ((i : Int) : Rat) :=
  ⟨Binary64.ofRat_int (by omega) (by omega), Rat.intCast_lt_intCast.2 (show (0 : Int) < i by omega)⟩

/-- A positive integer that rounds to the Number of an integer 0 < i < 2^53 is i. -/
theorem lsik_round_int {i : Nat} (hi : 0 < i) (hi53 : i < 2 ^ 53) {v : Int} (hv0 : 0 < v)
    (h : Binary64.ofRat (v : Rat) = Binary64.ofRat ((i : Int) : Rat)) : v = i := by
  obtain ⟨_, -, hn⟩ := Engine.Model.Digits.round_nearest (lsik_fin i hi hi53) h
  refine Classical.byContradiction fun hne => ?_
  have hne' : (v : Rat) ≠ ((i : Int) : Rat) := fun e => hne (Rat.intCast_inj.1 e)
  by_cases hb : v.natAbs ≤ 2 ^ 53
  · obtain ⟨ev, hc⟩ := Binary64.int_finiteQ (t := v) (by omega) hb
    have h1 := (hn _ ev (.inl hc)).1
    rcases absQ_cases ((v : Rat) - (v : Rat)) with e1 | e1 <;>
      rcases absQ_cases ((v : Rat) - ((i : Int) : Rat)) with e2 | e2 <;> grind
  · obtain ⟨ev, hc⟩ := Binary64.nat_finiteQ (n := 2 ^ 53) (by decide) (Nat.le_refl _)
    have h1 := (hn _ ev (.inl hc)).1
    have a1 : ((2 ^ 53 : Nat) : Rat) < (v : Rat) := by
      rw [← Rat.intCast_natCast]; exact Rat.intCast_lt_intCast.2 (by omega)
    have a2 : ((i : Int) : Rat) < ((2 ^ 53 : Nat) : Rat) := by
      rw [← Rat.intCast_natCast]; exact Rat.intCast_lt_intCast.2 (by omega)
    rcases absQ_cases ((v : Rat) - ((2 ^ 53 : Nat) : Rat)) with e1 | e1 <;>
      rcases absQ_cases ((v : Rat) - ((i : Int) : Rat)) with e2 | e2 <;> grind

theorem lsik_ten_pos (j : Int) : (0 : Rat) < (((10 : Nat) : Rat)) ^ j := Engine.Model.Digits.zp_pos (by decide) j

/-- s × 10^(n-K) = m × 10^T with 10^(K-1) ≤ s < 10^K, and m of K digits not a multiple of 10: n = K + T and s = m. -/
theorem lsik_unique (m T K : Nat) (hm : m % 10 ≠ 0) (h1 : 10 ^ (K - 1) ≤ m) (hK : 1 ≤ K) (n s : Int)
    (hs2 : s < ((10 : Nat) : Int) ^ K)
    (h : (s : Rat) * ((10 : Nat) : Rat) ^ (n - K) = (m : Rat) * ((10 : Nat) : Rat) ^ (T : Int)) :
    n = ((K + T : Nat) : Int) ∧ s = m := by
  have hr : 2 ≤ 10 := by decide
  have e : ((10 : Nat) : Rat) ^ (n - K) = ((10 : Nat) : Rat) ^ (T : Int) * ((10 : Nat) : Rat) ^ (n - K - T) := by
    rw [← Engine.Model.Digits.zp_add hr]; congr 1; omega
  rw [e, Rat.mul_comm (m : Rat), ← Rat.mul_assoc, Rat.mul_comm (s : Rat), Rat.mul_assoc] at h
  have h2 := Binary64.mul_left_cancel_pos (lsik_ten_pos _) h
  have hs2' : s < ((10 ^ K : Nat) : Int) := by rw [Int.natCast_pow]; exact hs2
  rcases Int.lt_or_le (n - K - T) 0 with hj | hj
  · obtain ⟨a, ha⟩ := Int.eq_ofNat_of_zero_le (show 0 ≤ -(n - K - T) by omega)
    have e2 : (s : Rat) = (m : Rat) * ((10 ^ a : Nat) : Rat) := by
      rw [← h2, Rat.mul_assoc, ← Engine.Model.Digits.zp_nat, ← ha, ← Engine.Model.Digits.zp_add hr,
        show n - K - T + -(n - K - T) = 0 by omega, Rat.zpow_zero, Rat.mul_one]
    have e3 : s = ((m * 10 ^ a : Nat) : Int) := by
      apply Rat.intCast_inj.1
      rw [e2, Rat.intCast_natCast, Rat.natCast_mul]
    have : 10 ^ K ≤ m * 10 ^ a := by
      have h3 : 10 ≤ 10 ^ a := by
        have := Nat.pow_le_pow_right (show 0 < 10 by decide) (show 1 ≤ a by omega)
        simpa using this
      have h4 : 10 ^ K = 10 ^ (K - 1) * 10 := by rw [← Nat.pow_succ]; congr 1; omega
      rw [h4]
      exact Nat.mul_le_mul h1 h3
    omega
  · obtain ⟨a, ha⟩ := Int.eq_ofNat_of_zero_le hj
    rw [ha, Engine.Model.Digits.zp_nat] at h2
    have e3 : s * ((10 ^ a : Nat) : Int) = (m : Int) := by
      apply Rat.intCast_inj.1
      rw [Rat.intCast_mul, Rat.intCast_natCast, Rat.intCast_natCast]
      exact h2
    cases a with
    | zero => simp at e3; refine ⟨by omega, e3⟩
    | succ a =>
      exfalso
      rw [Nat.pow_succ, Int.natCast_mul, ← Int.mul_assoc] at e3
      omega

/-- Step 5's n, k and s at the Number of m × 10^T < 2^53, m of K digits and not a multiple of 10: K + T, K and m. -/
theorem lsik_digits10 (m T K : Nat) (hm : m % 10 ≠ 0) (hK : 1 ≤ K) (hK16 : K ≤ 16) (h1 : 10 ^ (K - 1) ≤ m)
    (h2 : m < 10 ^ K) (hi53 : m * 10 ^ T < 2 ^ 53) :
    Engine.Model.Digits.digits (Binary64.ofRat (((m * 10 ^ T : Nat) : Int) : Rat)) 10 =
      (((K + T : Nat) : Int), K, (m : Int)) := by
  have hr : 2 ≤ 10 := by decide
  have hT : 0 < 10 ^ T := Nat.pow_pos (by decide)
  have hm0 : 0 < m := by omega
  have hi : 0 < m * 10 ^ T := Nat.mul_pos hm0 hT
  have hF := lsik_fin _ hi hi53
  have hXm : (((m * 10 ^ T : Nat) : Int) : Rat) = (m : Rat) * ((10 : Nat) : Rat) ^ (T : Int) := by
    rw [Engine.Model.Digits.zp_nat, Rat.intCast_natCast, Rat.natCast_mul]
  generalize hb : Binary64.ofRat (((m * 10 ^ T : Nat) : Int) : Rat) = b at hF ⊢
  generalize hXd : (((m * 10 ^ T : Nat) : Int) : Rat) = X at hF hb hXm
  obtain ⟨-, -, hX⟩ := Engine.Model.Digits.fin_parts hF
  have hpow : ∀ a : Nat, ((10 : Nat) : Int) ^ a = ((10 ^ a : Nat) : Int) := fun a => (Int.natCast_pow 10 a).symm
  -- the exponent
  have he : Engine.Model.Digits.expOf 10 X = ((K + T : Nat) : Int) := by
    refine Engine.Model.Digits.exp_unique hr (Engine.Model.Digits.expOf_spec hr hF.2) ⟨?_, ?_⟩
    · rw [show ((K + T : Nat) : Int) - 1 = ((K - 1 + T : Nat) : Int) by omega, Engine.Model.Digits.zp_nat, ← hXd,
        Rat.intCast_natCast]
      exact Rat.natCast_le_natCast.2 (by rw [Nat.pow_add]; exact Nat.mul_le_mul_right _ h1)
    · rw [Engine.Model.Digits.zp_nat, ← hXd, Rat.intCast_natCast]
      exact Rat.natCast_lt_natCast.2 (by rw [Nat.pow_add]; exact Nat.mul_lt_mul_of_pos_right h2 hT)
  -- fewer digits: no tuple tried meets the condition
  have hnone : ∀ j, 1 ≤ j → j < K → Engine.Model.Digits.at? b 10 X ((K + T : Nat) : Int) j = none := by
    intro j hj1 hjK
    unfold Engine.Model.Digits.at?
    rw [List.filter_eq_nil_iff.2 ?_]
    · rfl
    intro t ht hmeets
    simp only [Engine.Model.Digits.tries, List.mem_flatMap, List.mem_cons, List.mem_singleton, List.not_mem_nil,
      or_false] at ht
    obtain ⟨n, hn, ht⟩ := ht
    have hlohi : ((10 : Nat) : Int) ^ (j - 1) ≤ ((10 : Nat) : Int) ^ j - 1 := by
      rw [hpow, hpow]
      have : 10 ^ j = 10 ^ (j - 1) * 10 := by rw [← Nat.pow_succ]; congr 1; omega
      have : 0 < 10 ^ (j - 1) := Nat.pow_pos (by decide)
      omega
    obtain ⟨c, ⟨hc1, hc2⟩, rfl⟩ : ∃ c, (((10 : Nat) : Int) ^ (j - 1) ≤ c ∧ c ≤ ((10 : Nat) : Int) ^ j - 1) ∧
        t = (n, c) := by
      rcases ht with rfl | rfl
      · exact ⟨_, Engine.Model.Digits.clamp_lo hlohi, rfl⟩
      · exact ⟨_, Engine.Model.Digits.clamp_lo hlohi, rfl⟩
    obtain ⟨-, -, hof⟩ := Engine.Model.Digits.meets_iff.1 hmeets
    obtain ⟨d, hd⟩ := Int.eq_ofNat_of_zero_le (show 0 ≤ n - j by omega)
    have hv : ((c : Int) : Rat) * ((10 : Nat) : Rat) ^ (n - j) = ((c * ((10 ^ d : Nat) : Int) : Int) : Rat) := by
      rw [hd, Engine.Model.Digits.zp_nat, Rat.intCast_mul, Rat.intCast_natCast]
    simp only at hof
    rw [hv, ← hb, ← hXd] at hof
    have hc0 : 0 < c := by
      have : 0 < 10 ^ (j - 1) := Nat.pow_pos (by decide)
      rw [hpow] at hc1; omega
    have hd0 : (0 : Int) < ((10 ^ d : Nat) : Int) := by
      have : 0 < 10 ^ d := Nat.pow_pos (by decide)
      omega
    have e1 := lsik_round_int hi hi53 (Int.mul_pos hc0 hd0) hof
    have hdT : T ≤ d := by omega
    rw [show d = (d - T) + T by omega, Nat.pow_add, Int.natCast_mul, Int.natCast_mul, ← Int.mul_assoc] at e1
    have e2 := Int.eq_of_mul_eq_mul_right (by omega) e1
    cases hdt : d - T with
    | zero =>
      rw [hdt] at e2
      simp at e2
      have : 10 ^ j ≤ 10 ^ (K - 1) := Nat.pow_le_pow_right (by decide) (by omega)
      rw [hpow] at hc2
      omega
    | succ a =>
      rw [hdt, Nat.pow_succ, Int.natCast_mul, ← Int.mul_assoc] at e2
      omega
  -- K digits: the tuple (K + T, m), alone at distance 0
  have hlohi : ((10 : Nat) : Int) ^ (K - 1) ≤ (m : Int) ∧ (m : Int) ≤ ((10 : Nat) : Int) ^ K - 1 := by
    rw [hpow, hpow]; omega
  have hfl : (X * ((10 : Nat) : Rat) ^ ((K : Int) - ((K + T : Nat) : Int))).floor = (m : Int) := by
    rw [hXm, Rat.mul_assoc, ← Engine.Model.Digits.zp_add hr, show (T : Int) + ((K : Int) - ((K + T : Nat) : Int)) = 0 by
      omega, Rat.zpow_zero, Rat.mul_one, ← Rat.intCast_natCast, Rat.floor_intCast]
  have hcl : Engine.Model.Digits.clamp (m : Int) (((10 : Nat) : Int) ^ (K - 1)) (((10 : Nat) : Int) ^ K - 1) = m := by
    unfold Engine.Model.Digits.clamp; split <;> (try split) <;> omega
  have hval : ((m : Int) : Rat) * ((10 : Nat) : Rat) ^ (((K + T : Nat) : Int) - K) = X := by
    rw [hXm, Rat.intCast_natCast, show ((K + T : Nat) : Int) - K = T by omega]
  have hmeet : Engine.Model.Digits.meets b 10 ((K + T : Nat) : Int) K (m : Int) = true :=
    Engine.Model.Digits.meets_iff.2 ⟨hlohi.1, by have := hlohi.2; omega, by rw [hval]; exact hb⟩
  have hat : Engine.Model.Digits.at? b 10 X ((K + T : Nat) : Int) K = some (((K + T : Nat) : Int), (m : Int)) := by
    unfold Engine.Model.Digits.at?
    apply Engine.Model.Digits.best_zero
    · refine List.mem_filter.2 ⟨?_, hmeet⟩
      simp only [Engine.Model.Digits.tries]
      refine List.mem_flatMap.2 ⟨((K + T : Nat) : Int), by simp, ?_⟩
      rw [hfl, hcl]
      simp
    · simp only [Engine.Model.Digits.dist]
      rw [hval]
      simp [Rat.sub_self]
    · intro u hu h0
      obtain ⟨hu, hum⟩ := List.mem_filter.1 hu
      obtain ⟨-, hs2, -⟩ := Engine.Model.Digits.meets_iff.1 hum
      have hv0 : (u.2 : Rat) * ((10 : Nat) : Rat) ^ (u.1 - K) = (m : Rat) * ((10 : Nat) : Rat) ^ (T : Int) := by
        rw [← hXm]
        unfold Engine.Model.Digits.dist at h0
        simp only at h0
        split at h0 <;> grind
      obtain ⟨e1, e2⟩ := lsik_unique m T K hm h1 hK u.1 u.2 hs2 hv0
      exact Prod.ext e1 e2
  have hs := Engine.Model.Digits.search_first (b := b) (r := 10) (X := X) (e := ((K + T : Nat) : Int))
    Engine.Model.Digits.fuel 1 hK (by simp [Engine.Model.Digits.fuel]; omega) (fun j a c => hnone j a c) hat
  unfold Engine.Model.Digits.digits
  simp only [hX, he, hs]
  rfl

/-! ## The decimal digits -/

/-- The code units of the decimal digits of n. -/
def lsikU (n : Nat) : Array UInt16 := Model.utf16 (toString n)

theorem lsik_U_lt (n : Nat) (h : n < 10) : lsikU n = #[(48 + n).toUInt16] := by
  unfold lsikU
  rw [ls_utf16_digits, Nat.toDigits_of_lt_base h]
  simp only [List.foldl_cons, List.foldl_nil]
  rw [ls_digit_unit _ _ h]
  rfl

theorem lsik_U_ge (n : Nat) (h : 10 ≤ n) : lsikU n = (lsikU (n / 10)).push (48 + n % 10).toUInt16 := by
  unfold lsikU
  rw [ls_utf16_digits, ls_utf16_digits, Nat.toDigits_of_base_le (by omega) h, List.foldl_append]
  simp only [List.foldl_cons, List.foldl_nil]
  rw [ls_digit_unit _ _ (Nat.mod_lt _ (by omega))]

theorem lsik_U_size : ∀ K m : Nat, 1 ≤ K → 10 ^ (K - 1) ≤ m → m < 10 ^ K → (lsikU m).size = K := by
  intro K
  induction K with
  | zero => intro m h; omega
  | succ K ih =>
    intro m _ h1 h2
    by_cases hK : K = 0
    · subst hK
      rw [lsik_U_lt m (by simpa using h2)]
      rfl
    · have e1 : 10 ^ (K + 1) = 10 ^ K * 10 := by rw [Nat.pow_succ]
      have e2 : 10 ^ K = 10 ^ (K - 1) * 10 := by
        rw [← Nat.pow_succ]; congr 1; omega
      have e3 : K + 1 - 1 = K := by omega
      rw [e3] at h1
      have hp : 0 < 10 ^ (K - 1) := Nat.pow_pos (by decide)
      rw [lsik_U_ge m (by omega), Array.size_push, ih (m / 10) (by omega) (by omega) (by omega)]

theorem lsik_op_sub (a b : MathVal) : op? .sub a b = some (F.sub a b) := rfl
theorem lsik_eq_eq (x y : MathVal) : eq? x y = some (MathVal.eq x y) := rfl
theorem lsik_ge_eq (x y : MathVal) : ge? x y = some (MathVal.lt y x || MathVal.eq x y) := rfl
theorem lsik_ne_eq (x y : MathVal) : ne? x y = some (!MathVal.eq x y) := rfl
theorem lsik_inInt_eq (lo hi n : MathVal) : inInt? lo hi n =
    some ((MathVal.lt lo n || MathVal.eq lo n) && (MathVal.lt n hi || MathVal.eq n hi)) := rfl

theorem lsik_cat2 (a b : F.Str) : cat? [.str a, .str b] = some (a ++ b) := by
  show some ((F.strLit "" ++ a) ++ b) = _
  rw [lsik_empty]; simp

theorem lsik_intToRadix (n : Nat) : F.intToRadix (.int (n : Int)) lsikTen = lsikU n := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    by_cases hn : n < 10
    · have hdig := Engine.Model.intToRadix_digit n 10 (by decide) (by decide) hn
      have hdl : ("0123456789abcdefghijklmnopqrstuvwxyz" : String).toList =
          ['0', '1', '2', '3', '4', '5', '6', '7', '8', '9', 'a', 'b', 'c', 'd', 'e', 'f', 'g', 'h', 'i', 'j', 'k',
           'l', 'm', 'n', 'o', 'p', 'q', 'r', 's', 't', 'u', 'v', 'w', 'x', 'y', 'z'] := rfl
      have hdigs : Model.utf16 "0123456789abcdefghijklmnopqrstuvwxyz" = #[48, 49, 50, 51, 52, 53, 54, 55, 56, 57,
          97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118,
          119, 120, 121, 122] := by unfold Model.utf16; rw [String.foldl_eq_foldl_toList, hdl]; rfl
      have hs : F.strSub (F.strLit "0123456789abcdefghijklmnopqrstuvwxyz") (F.ofNat n) (F.ofNat (n + 1)) =
          #[(48 + n).toUInt16] := by
        show (Model.utf16 "0123456789abcdefghijklmnopqrstuvwxyz").extract n (n + 1) = _
        rw [hdigs]
        rcases (by omega : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 ∨ n = 6 ∨ n = 7 ∨ n = 8 ∨ n = 9) with
          rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
      rw [show (.int (n : Int) : MathVal) = F.ofNat n from rfl, show lsikTen = F.ofNat 10 from rfl, hdig, hs, lsik_U_lt n hn]
    · have hle : 10 ≤ n := by omega
      have hdiv := Engine.Model.intToRadix_div n 10 (by decide) (by decide) hle
      have h1 : F.intToRadix (.int (n : Int)) lsikTen =
          F.intToRadix (.int ((n / 10 : Nat) : Int)) lsikTen ++
          F.intToRadix (.int ((n % 10 : Nat) : Int)) lsikTen := hdiv
      rw [h1, ih (n / 10) (Nat.div_lt_self (by omega) (by decide)),
        ih (n % 10) (Nat.lt_of_lt_of_le (Nat.mod_lt n (by decide)) hle),
        lsik_U_lt (n % 10) (Nat.mod_lt n (by decide)), lsik_U_ge n hle, Array.push_eq_append]

/-- The representation of `n` using radix `10`. -/
theorem lsik_repr (n : Nat) (h0 : 0 < n) (h : n < 10 ^ 64) : repr? (.int (n : Int)) lsikTen = some (lsikU n) := by
  have c1 : MathVal.lt (MathVal.int ((0 : Nat) : Int)) (MathVal.int (n : Int)) = true := by
    show decide (((0 : Nat) : Int) < (n : Int)) = true; exact decide_eq_true (by omega)
  have c2 : MathVal.lt lsikTen (MathVal.int ((2 : Nat) : Int)) = false := rfl
  have c3 : MathVal.lt (MathVal.int ((36 : Nat) : Int)) lsikTen = false := rfl
  unfold repr?
  simp only [bind, pure, Option.bind_some, lsik_ge_eq, lsik_inInt_eq, c1, c2, c3, Bool.true_or,
    Bool.or_true, Bool.not_false, Bool.and_true]
  show some (F.intToRadix (.int (n : Int)) lsikTen) = _
  rw [lsik_intToRadix n]

theorem lsik_rep (r : Nat) (u : UInt16) : #[u] ++ Array.replicate r u = Array.replicate (r + 1) u := by
  apply Array.toList_inj.1
  simp [List.replicate_succ]

theorem lsik_strRepeat (T : Nat) (u : UInt16) : F.strRepeat (.int (T : Int)) #[u] = Array.replicate T u := by
  induction T with
  | zero =>
    have h0 := Engine.Model.strRepeat_zero #[u]
    rw [show F.strLit "" = #[] from lsik_empty] at h0
    exact h0
  | succ T ih =>
    have hs := Engine.Model.strRepeat_succ T #[u]
    have h1 : F.strConcat (F.strRepeat (F.ofNat T) #[u]) #[u] = F.strRepeat (F.ofNat T) #[u] ++ #[u] := rfl
    rw [show (.int ((T + 1 : Nat) : Int) : MathVal) = F.ofNat (T + 1) from rfl, hs, h1,
      show F.ofNat T = .int (T : Int) from rfl, ih]
    apply Array.toList_inj.1
    simp only [Array.toList_append, Array.toList_replicate]
    change List.replicate T u ++ [u] = List.replicate (T + 1) u
    clear hs h1 ih
    induction T with
    | zero => rfl
    | succ k hk => simp only [List.replicate_succ, List.cons_append] at hk ⊢; exact congrArg (u :: ·) hk

theorem lsik_occ (z : Int) (T : Nat) (hz : z = T) (hT : T < 2200) :
    occ? (.int z) (F.ofNat 48) = some (Array.replicate T (48 : Nat).toUInt16) := by
  subst hz
  have hc : cat? [.math (F.ofNat 48)] = some #[(48 : Nat).toUInt16] := by
    unfold cat?; rw [show F.strLit "" = #[] from lsik_empty]; rfl
  have hi : F.isInt (.int (T : Int)) = true := rfl
  have hl : F.lt (.int (T : Int)) (F.ofNat 0) = false := by
    show decide ((T : Int) < 0) = false; exact decide_eq_false (by omega)
  unfold occ?
  simp only [bind, pure, Option.bind_some, hi, hl, Bool.not_false, Bool.and_self, hc]
  show some (F.strRepeat (.int (T : Int)) #[(48 : Nat).toUInt16]) = _
  rw [lsik_strRepeat]

/-- The digits of n × 10^T are those of n and T zeros. -/
theorem lsik_zeros : ∀ (T n : Nat), 0 < n →
    lsikU n ++ Array.replicate T (48 : Nat).toUInt16 = lsikU (n * 10 ^ T) := by
  intro T
  induction T with
  | zero => intro n _; simp
  | succ T ih =>
    intro n hn
    have e : lsikU (n * 10) = (lsikU n).push (48 : Nat).toUInt16 := by
      rw [lsik_U_ge (n * 10) (by omega), show n * 10 / 10 = n by omega, show n * 10 % 10 = 0 by omega]
    rw [← lsik_rep, ← Array.append_assoc, ← Array.push_eq_append, ← e, ih (n * 10) (by omega),
      Nat.pow_succ, Nat.mul_assoc, Nat.mul_comm 10]

/-- Steps 6 to 11 at an integer's n, k and s. -/
theorem lsik_render (m T K : Nat) (hm : 0 < m) (h1 : 10 ^ (K - 1) ≤ m) (h2 : m < 10 ^ K) (hK : 1 ≤ K) (hK64 : K ≤ 64)
    (hKT : K + T ≤ 21) :
    render? lsikTen (.int ((K + T : Nat) : Int)) (.int K) (.int m) = some (lsikU (m * 10 ^ T)) := by
  have hor : or? (ne? lsikTen (F.ofNat 10)) (inInt? (.int (-5)) (F.ofNat 21) (.int ((K + T : Nat) : Int))) =
      some true := by
    rw [lsik_ne_eq, lsik_inInt_eq]
    show or? (some false) (some ((decide ((-5 : Int) < ((K + T : Nat) : Int)) || (-5 : Int) == ((K + T : Nat) : Int)) &&
      (decide (((K + T : Nat) : Int) < ((21 : Nat) : Int)) || ((K + T : Nat) : Int) == ((21 : Nat) : Int)))) = _
    have a1 : decide ((-5 : Int) < ((K + T : Nat) : Int)) = true := decide_eq_true (by omega)
    have a2 : (decide (((K + T : Nat) : Int) < ((21 : Nat) : Int)) || ((K + T : Nat) : Int) == ((21 : Nat) : Int)) =
        true := by
      simp
      omega
    rw [a1, a2]
    rfl
  have hge : ge? (.int ((K + T : Nat) : Int)) (.int (K : Int)) = some true := by
    rw [lsik_ge_eq]
    show some (decide ((K : Int) < ((K + T : Nat) : Int)) || ((K + T : Nat) : Int) == (K : Int)) = _
    congr 1
    simp
    omega
  have hrepr := lsik_repr m hm (Nat.lt_of_lt_of_le h2 (Nat.pow_le_pow_right (by decide) hK64))
  have hkd : kDigits? (.int (K : Int)) (lsikU m) = some (lsikU m) := by
    have hs := lsik_U_size K m hK h1 h2
    show (do guard (((lsikU m).size : Int) == (K : Int)); return lsikU m : Option F.Str) = _
    rw [hs]
    simp
    rfl
  have hocc : occ? (MathVal.add (.int ((K + T : Nat) : Int)) (MathVal.neg (.int (K : Int)))) (F.ofNat 48) =
      some (Array.replicate T (48 : Nat).toUInt16) :=
    lsik_occ (((K + T : Nat) : Int) + -(K : Int)) T (by omega) (by omega)
  unfold render?
  simp only [bind, Option.bind_some, hor, hge, lsik_op_sub, hrepr, hkd, hocc, lsik_cat2, ite_true]
  rw [lsik_zeros T m hm]

/-! ## Number::toString at an integer -/

/-- A positive integer is its digits without their trailing zeros, times a power of ten. -/
theorem lsik_strip : ∀ n i : Nat, i ≤ n → 0 < i → ∃ m T : Nat, i = m * 10 ^ T ∧ m % 10 ≠ 0 := by
  intro n
  induction n with
  | zero => intro i h h0; omega
  | succ n ih =>
    intro i h h0
    by_cases hm : i % 10 = 0
    · obtain ⟨m, T, e, hm'⟩ := ih (i / 10) (by omega) (by omega)
      refine ⟨m, T + 1, ?_, hm'⟩
      rw [Nat.pow_succ, ← Nat.mul_assoc, ← e]
      omega
    · exact ⟨i, 0, by simp, hm⟩

private theorem lsik_at (i : Nat) (hi : 0 < i) (hi53 : i < 2 ^ 53) :
    let x := F.numOf (Model.MathVal.int i)
    numberToStr (F.ofNat 10) x = some (F.strLit (toString i)) ∧
    ∃ (n k s : Nat),
      F.numView x = .finite (.int i) ∧
      F.numLt x (F.numZero true) = false ∧
      step5 (F.ofNat 10) x = (.int n, .int k, .int s) ∧
      n ≤ 21 ∧ k ≤ n ∧
      kDigits? (.int k) (F.intToRadix (.int s) (.int 10)) = some (F.intToRadix (.int s) (.int 10)) ∧
      cat? [.str (F.intToRadix (.int s) (.int 10)),
        .str (F.strRepeat (.int (n - k : Nat)) #[(48 : Nat).toUInt16])] = some (F.strLit (toString i)) := by
  obtain ⟨m, T, rfl, hm⟩ := lsik_strip i i (Nat.le_refl _) hi
  have hT : 0 < 10 ^ T := Nat.pow_pos (by decide)
  have hm0 : 0 < m := Nat.pos_of_ne_zero fun h => by subst h; omega
  have hmi : m ≤ m * 10 ^ T := Nat.le_mul_of_pos_right _ hT
  obtain ⟨hK2, hK1⟩ := Engine.Model.Digits.nlog_spec (r := 10) (by decide) m m (by omega) (Nat.le_refl _)
  generalize hL : Engine.Model.Digits.nlog 10 m m = L at hK1 hK2
  have hlo : 10 ^ (L + T) ≤ m * 10 ^ T := by
    rw [Nat.pow_add]; exact Nat.mul_le_mul_right _ hK2
  have hLT : L + T < 16 :=
    (Nat.pow_lt_pow_iff_right (by decide : 1 < 10)).1 (Nat.lt_of_le_of_lt hlo (Nat.lt_trans hi53 (by decide)))
  have hd := lsik_digits10 m T (L + 1) hm (by omega) (by omega) (by simpa using hK2) hK1 hi53
  have hbits := lsik_bits ((m * 10 ^ T : Nat) : Int) (by omega) (by omega)
  have hv : F.numView (F.numOf (MathVal.int ((m * 10 ^ T : Nat) : Int))) =
      .finite (MathVal.int ((m * 10 ^ T : Nat) : Int)) := lsik_view _ (by omega) (by omega)
  have hlt : F.numLt (F.numOf (MathVal.int ((m * 10 ^ T : Nat) : Int))) (F.numZero true) = false := by
    show Binary64.lt (Model.Num.of (Binary64.ofRat (((m * 10 ^ T : Nat) : Int) : Rat))).1
      (Model.Num.of (Binary64.zero true)).1 = false
    rw [Binary64.lt_view, Model.viewQ_of, Model.viewQ_of, Binary64.ofRat_int (by omega) (by omega),
      Binary64.viewQ_zero]
    simp only [Binary64.realQ, ite_true]
    have : ¬ ((((m * 10 ^ T : Nat) : Int) : Rat) < ((0 : Int) : Rat)) := by
      rw [Rat.intCast_lt_intCast]; omega
    exact decide_eq_false this
  have h5 : step5 lsikTen (F.numOf (MathVal.int ((m * 10 ^ T : Nat) : Int))) =
      (.int ((L + 1 + T : Nat) : Int), .int ((L + 1 : Nat) : Int), .int (m : Int)) := by
    show (MathVal.int (Engine.Model.Digits.digits (F.numOf (MathVal.int ((m * 10 ^ T : Nat) : Int))).1 10).1,
      MathVal.int ((Engine.Model.Digits.digits (F.numOf (MathVal.int ((m * 10 ^ T : Nat) : Int))).1 10).2.1 : Int),
      MathVal.int (Engine.Model.Digits.digits (F.numOf (MathVal.int ((m * 10 ^ T : Nat) : Int))).1 10).2.2) = _
    rw [hbits, hd]
  have hok : step5Ok lsikTen (MathVal.int ((m * 10 ^ T : Nat) : Int)) = true := by
    have : ((0 : Nat) : Int) < ((m * 10 ^ T : Nat) : Int) := by omega
    show (decide (((0 : Nat) : Int) < ((m * 10 ^ T : Nat) : Int)) && true &&
      !decide (((10 : Nat) : Int) < ((2 : Nat) : Int)) && !decide (((36 : Nat) : Int) < ((10 : Nat) : Int))) = true
    simp only [this, decide_true, Bool.true_and, Bool.and_true]
    decide
  have hr := lsik_render m T (L + 1) hm0 (by simpa using hK2) hK1 (by omega) (by omega) (by omega)
  have h4 : fromStep4 lsikTen (F.numOf (MathVal.int ((m * 10 ^ T : Nat) : Int))) = some (lsikU (m * 10 ^ T)) := by
    unfold fromStep4
    rw [hv]
    simp only [hok, ite_true, h5]
    exact hr
  have h1 : ∀ neg, fromStep1 lsikTen neg (F.numOf (MathVal.int ((m * 10 ^ T : Nat) : Int))) =
      fromStep4 lsikTen (F.numOf (MathVal.int ((m * 10 ^ T : Nat) : Int))) := by
    intro neg
    unfold fromStep1
    rw [hv]
    have hlt' : Binary64.lt (Model.Num.of (MathVal.int ((m * 10 ^ T : Nat) : Int)).toNum).val
        (Model.Num.of (Binary64.zero true)).val = false := hlt
    simp only [hlt', Bool.false_eq_true, ite_false]
  refine ⟨?_, L + 1 + T, L + 1, m, hv, hlt, h5, by omega, by omega, ?_, ?_⟩
  · show fromStep1 lsikTen _ (F.numOf (MathVal.int ((m * 10 ^ T : Nat) : Int))) = _
    rw [h1, h4]; rfl
  · rw [show (.int 10 : MathVal) = lsikTen from rfl, lsik_intToRadix m]
    have hs := lsik_U_size (L + 1) m (by omega) (by simpa using hK2) hK1
    show (do guard (((lsikU m).size : Int) == ((L + 1 : Nat) : Int)); return lsikU m : Option F.Str) = _
    rw [hs]; simp; rfl
  · rw [show (.int 10 : MathVal) = lsikTen from rfl, lsik_intToRadix m, lsik_strRepeat,
      show L + 1 + T - (L + 1) = T by omega, lsik_cat2, lsik_zeros T m hm0]
    rfl

/-- Number::toString at the Number of an integer 1 ≤ i < 2^53 and radix 10: the decimal digits of i. -/
theorem lsIntKeys : LsIntKeys :=
  ⟨fun i hi hi53 => (lsik_at i hi hi53).1, fun i hi hi53 => (lsik_at i hi hi53).2⟩


end Engine.Machine
