module

public import Engine.Model
public import Engine.Proofs.Seq

@[expose] public section

/-! # `Engine.Impl` satisfies `Model.ByteLaws` -/

namespace Engine.Impl

open Ecma Engine.Model

private theorem impl_isInt (m : MathVal) : Impl.isInt m = MathVal.isInt m := rfl
private theorem impl_lt (a b : MathVal) : Impl.lt a b = MathVal.lt a b := rfl
private theorem impl_eq (a b : MathVal) : Impl.eq a b = MathVal.eq a b := rfl
private theorem impl_ofNat (k : Nat) : Impl.ofNat k = .int k := rfl
private theorem impl_bytesLen (bs : ByteArray) : Impl.bytesLen bs = bytesLen bs := rfl
private theorem impl_bytesZero (n : MathVal) : Impl.bytesZero n = bytesZero n := rfl
private theorem impl_bytesGet (bs : ByteArray) (i : MathVal) : Impl.bytesGet bs i = bytesGet bs i := rfl
private theorem impl_bytesSet (bs : ByteArray) (i v : MathVal) : Impl.bytesSet bs i v = bytesSet bs i v := rfl
private theorem impl_bytesFill (bs : ByteArray) (v : MathVal) : Impl.bytesFill bs v = bytesFill bs v := rfl

private theorem u8_toNat {bv : Nat} (hbv : bv < 256) : (UInt8.ofNat bv).toNat = bv := by
  have : (UInt8.ofNat bv).toNat = bv % 256 := rfl
  rw [this, Nat.mod_eq_of_lt hbv]

private theorem isNat_of {v : MathVal} (hi : Impl.isInt v = true) (h0 : Impl.lt v (Impl.ofNat 0) = false) :
    ∃ k : Nat, v = .int k := by
  rw [impl_isInt] at hi
  rw [impl_lt, impl_ofNat] at h0
  cases v with
  | frac _ _ => cases hi
  | int z =>
    rw [MathVal.lt_int] at h0
    have hz := of_decide_eq_false h0
    exact ⟨z.toNat, by congr 1; exact (Int.toNat_of_nonneg (by omega)).symm⟩

private theorem isByte_iff (v : MathVal) : Model.isByte Impl v ↔ ∃ k : Nat, k < 256 ∧ v = .int k := by
  unfold Model.isByte
  rw [impl_isInt, impl_lt, impl_lt, impl_ofNat, impl_ofNat]
  constructor
  · rintro ⟨hi, h0, h1⟩
    cases v with
    | frac _ _ => cases hi
    | int z =>
      rw [MathVal.lt_int] at h0 h1
      have hz0 := of_decide_eq_false h0
      have hz1 := of_decide_eq_true h1
      exact ⟨z.toNat, by omega, by congr 1; exact (Int.toNat_of_nonneg (by omega)).symm⟩
  · rintro ⟨k, hk, rfl⟩
    refine ⟨rfl, ?_, ?_⟩ <;> rw [MathVal.lt_int]
    · exact decide_eq_false (by omega)
    · exact decide_eq_true (by omega)

private theorem byte?_iff (v : MathVal) (b : UInt8) : byte? v = some b ↔ v = .int b.toNat := by
  cases v with
  | frac q hq =>
    simp [byte?]
  | int j =>
    unfold byte?; dsimp only
    constructor
    · intro h
      by_cases hj : 0 ≤ j ∧ j < 256
      · simp [hj] at h; cases h
        rw [u8_toNat (by omega)]
        congr 1; exact (Int.toNat_of_nonneg hj.1).symm
      · simp [hj] at h
    · intro h; cases h
      have hb : b.toNat < 256 := b.toBitVec.isLt
      have hcond : 0 ≤ (b.toNat : Int) ∧ (b.toNat : Int) < 256 := ⟨by omega, by omega⟩
      simp [hcond]

private theorem fillLoop_size : ∀ n b acc, (fillLoop n b acc).size = acc.size + n
  | 0, _, acc => rfl
  | n + 1, b, acc => by
    unfold fillLoop
    rw [fillLoop_size n b (acc.push b), ByteArray.size_push]
    omega

private theorem get_push_lt {acc : ByteArray} {b : UInt8} {j : Nat} (hj : j < acc.size) :
    (acc.push b).get! j = acc.get! j := by
  cases acc with
  | mk ds =>
    show (ds.push b)[j]! = ds[j]!
    have hj' : j < ds.size := hj
    rw [Array.getElem!_eq_getD, Array.getElem!_eq_getD,
      Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?,
      Array.getElem?_push_lt hj', Array.getElem?_eq_some_getElem ds j hj']

private theorem get_push_eq {acc : ByteArray} {b : UInt8} :
    (acc.push b).get! acc.size = b := by
  cases acc with
  | mk ds =>
    show (ds.push b)[ds.size]! = b
    simp

private theorem fillLoop_get_all : ∀ n b acc k,
    k < acc.size + n → (∀ j < acc.size, acc.get! j = b) → (fillLoop n b acc).get! k = b
  | 0, _, acc, k, hk, hacc => hacc k (by omega)
  | n + 1, b, acc, k, hk, hacc => by
    unfold fillLoop
    apply fillLoop_get_all n b (acc.push b) k (by rw [ByteArray.size_push]; omega)
    intro j hj
    rw [ByteArray.size_push] at hj
    by_cases hja : j < acc.size
    · rw [get_push_lt hja]; exact hacc j hja
    · have : j = acc.size := by omega
      subst this; exact get_push_eq

private theorem empty_size : ByteArray.empty.size = 0 := rfl

private theorem emptyCap_size (n : Nat) : (ByteArray.emptyWithCapacity n).size = 0 := rfl

private theorem lt_zero_int (z : Int) : MathVal.lt (.int z) (.int (0 : Nat)) = decide (z < 0) :=
  MathVal.lt_int z 0

private theorem bytesGet_nat (bs : ByteArray) (k : Nat) :
    bytesGet bs (.int k) = if k < bs.size then some (.int (bs.get! k).toNat) else none := by
  unfold bytesGet; rw [MathVal.idx_nat]; rfl

private theorem bytesGet_negi (bs : ByteArray) {j : Int} (hj : j < 0) : bytesGet bs (.int j) = none := by
  unfold bytesGet; rw [MathVal.idx_negi hj]; rfl

private theorem byteArray_set_get_self (bs : ByteArray) {k : Nat} (b : UInt8) (hk : k < bs.size) :
    (bs.set! k b).get! k = b := by
  cases bs with
  | mk ds =>
    show (ds.set! k b)[k]! = b
    have hk' : k < ds.size := hk
    simp [Array.set!_eq_setIfInBounds, hk']

private theorem byteArray_set_get_ne (bs : ByteArray) {k m : Nat} (b : UInt8) (hm : m < bs.size) (hne : m ≠ k) :
    (bs.set! k b).get! m = bs.get! m := by
  cases bs with
  | mk ds =>
    show (ds.set! k b)[m]! = ds[m]!
    have hm' : m < ds.size := hm
    simp [Array.set!_eq_setIfInBounds, hm', Ne.symm hne]

theorem bytesLen_nonneg_law (bs : ByteArray) :
    Impl.isInt (Impl.bytesLen bs) = true ∧ Impl.lt (Impl.bytesLen bs) (Impl.ofNat 0) = false := by
  rw [impl_isInt, impl_lt, impl_ofNat, impl_bytesLen]
  refine ⟨rfl, ?_⟩
  show MathVal.lt (.int bs.size) (.int 0) = false
  rw [MathVal.lt_int]; exact decide_eq_false (by omega)

theorem bytesGet_bounds_law (bs : ByteArray) (i : MathVal) :
    (Impl.isInt i = true ∧ Impl.lt i (Impl.ofNat 0) = false ∧ Impl.lt i (Impl.bytesLen bs) = true) ↔
      (Impl.bytesGet bs i).isSome = true := by
  rw [impl_isInt, impl_lt, impl_lt, impl_ofNat, impl_bytesLen, impl_bytesGet]
  cases i with
  | frac q hq =>
    have hi : MathVal.isInt (.frac q hq) = false := rfl
    have hg : bytesGet bs (.frac q hq) = none := rfl
    rw [hi, hg]; simp
  | int z =>
    by_cases hz : 0 ≤ z
    · obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le hz
      have hi : MathVal.isInt (.int k) = true := rfl
      have h0 : MathVal.lt (.int k) (.int (0 : Nat)) = false := by rw [lt_zero_int]; exact decide_eq_false (by omega)
      have hlt : MathVal.lt (.int k) (bytesLen bs) = decide (k < bs.size) := MathVal.lt_nat k bs.size
      rw [hi, h0, hlt, bytesGet_nat]
      by_cases hk : k < bs.size <;> simp [hk]
    · have h0 : MathVal.lt (.int z) (.int (0 : Nat)) = true := by rw [lt_zero_int]; exact decide_eq_true (by omega)
      rw [bytesGet_negi bs (by omega), h0]; simp

theorem bytesGet_byte_law (bs : ByteArray) (i b : MathVal) (h : Impl.bytesGet bs i = some b) :
    Model.isByte Impl b := by
  rw [impl_bytesGet] at h
  cases i with
  | frac _ _ => cases h
  | int z =>
    by_cases hz : 0 ≤ z
    · obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le hz
      rw [bytesGet_nat] at h
      by_cases hk : k < bs.size
      · simp only [hk, ↓reduceIte] at h; cases h
        exact (isByte_iff _).2 ⟨(bs.get! k).toNat, (bs.get! k).toBitVec.isLt, rfl⟩
      · simp only [hk, ↓reduceIte] at h; cases h
    · rw [bytesGet_negi bs (by omega)] at h; cases h

theorem bytesZero_len_law (n : MathVal) (hi : Impl.isInt n = true) (h0 : Impl.lt n (Impl.ofNat 0) = false) :
    Impl.bytesLen (Impl.bytesZero n) = n := by
  obtain ⟨k, rfl⟩ := isNat_of hi h0
  rw [impl_bytesLen, impl_bytesZero]
  unfold bytesLen bytesZero
  rw [MathVal.idx_nat, fillLoop_size, emptyCap_size]
  simp

theorem bytesZero_get_law (n i b : MathVal) (h : Impl.bytesGet (Impl.bytesZero n) i = some b) :
    b = Impl.ofNat 0 := by
  rw [impl_bytesGet, impl_bytesZero] at h
  rw [impl_ofNat]
  cases i with
  | frac _ _ => cases h
  | int z =>
    by_cases hz : 0 ≤ z
    · obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le hz
      rw [bytesGet_nat] at h
      by_cases hk : k < (bytesZero n).size
      · simp only [hk, ↓reduceIte] at h; cases h
        have hz0 : (bytesZero n).get! k = 0 := by
          unfold bytesZero
          rcases hnd : MathVal.idx n with _ | m
          · unfold bytesZero at hk; rw [hnd, empty_size] at hk; omega
          · unfold bytesZero at hk; rw [hnd, fillLoop_size, emptyCap_size] at hk
            dsimp only
            apply fillLoop_get_all
            · rw [emptyCap_size]; omega
            · intro j hj; rw [emptyCap_size] at hj; omega
        rw [hz0]; rfl
      · simp only [hk, ↓reduceIte] at h; cases h
    · rw [bytesGet_negi _ (by omega)] at h; cases h

theorem bytesSet_len_law (bs : ByteArray) (i v : MathVal) :
    Impl.bytesLen (Impl.bytesSet bs i v) = Impl.bytesLen bs := by
  rw [impl_bytesLen, impl_bytesLen, impl_bytesSet]
  unfold bytesLen bytesSet
  rcases MathVal.idx i with _ | k <;> rcases byte? v with _ | b <;> try rfl
  dsimp only
  split
  · cases bs with | mk ds => simp
  · rfl

theorem bytesSet_get_law (bs : ByteArray) (i v j : MathVal)
    (hi : Impl.isInt i = true) (h0 : Impl.lt i (Impl.ofNat 0) = false)
    (hlt : Impl.lt i (Impl.bytesLen bs) = true) (hv : Model.isByte Impl v) :
    Impl.bytesGet (Impl.bytesSet bs i v) j = if Impl.eq j i then some v else Impl.bytesGet bs j := by
  obtain ⟨k, rfl⟩ := isNat_of hi h0
  rw [impl_lt, impl_bytesLen] at hlt
  have hk : k < bs.size := by
    change MathVal.lt (.int k) (.int bs.size) = true at hlt
    rw [MathVal.lt_nat] at hlt; exact of_decide_eq_true hlt
  obtain ⟨bv, hbv, rfl⟩ := (isByte_iff v).1 hv
  have hbyte : byte? (.int bv) = some (UInt8.ofNat bv) := by
    rw [byte?_iff, u8_toNat hbv]
  rw [impl_bytesGet, impl_bytesGet, impl_eq, impl_bytesSet]
  have hset : bytesSet bs (.int k) (.int bv) = bs.set! k (UInt8.ofNat bv) := by
    unfold bytesSet; rw [MathVal.idx_nat, hbyte]; simp only [hk, ↓reduceIte]
  rw [hset]
  cases j with
  | frac q hq =>
    have hne : MathVal.eq (.frac q hq) (.int k) = false := MathVal.eq_frac_int q hq k
    rw [hne]; rfl
  | int z =>
    rw [MathVal.eq_int]
    by_cases hz : 0 ≤ z
    · obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hz
      rw [bytesGet_nat, bytesGet_nat]
      have hsz : (bs.set! k (UInt8.ofNat bv)).size = bs.size := by cases bs; simp
      rw [hsz]
      by_cases hmk : m = k
      · subst hmk
        simp [hk]
        rw [byteArray_set_get_self bs (UInt8.ofNat bv) hk, u8_toNat hbv]
      · have hne : decide ((m : Int) = (k : Int)) = false := decide_eq_false (by omega)
        simp only [hne, Bool.false_eq_true, ↓reduceIte]
        by_cases hm : m < bs.size
        · simp only [hm, ↓reduceIte]
          rw [byteArray_set_get_ne bs _ hm hmk]
        · simp [hm]
    · have hne : decide (z = (k : Int)) = false := decide_eq_false (by omega)
      simp only [hne, Bool.false_eq_true, ↓reduceIte]
      rw [bytesGet_negi _ (by omega), bytesGet_negi _ (by omega)]

theorem bytesFill_len_law (bs : ByteArray) (v : MathVal) :
    Impl.bytesLen (Impl.bytesFill bs v) = Impl.bytesLen bs := by
  rw [impl_bytesLen, impl_bytesLen, impl_bytesFill]
  unfold bytesLen bytesFill
  rcases byte? v with _ | b
  · rfl
  · dsimp only; rw [fillLoop_size, emptyCap_size]; simp

theorem bytesFill_get_law (bs : ByteArray) (v i : MathVal) (hv : Model.isByte Impl v)
    (hi : Impl.isInt i = true) (h0 : Impl.lt i (Impl.ofNat 0) = false)
    (hlt : Impl.lt i (Impl.bytesLen bs) = true) :
    Impl.bytesGet (Impl.bytesFill bs v) i = some v := by
  obtain ⟨bv, hbv, rfl⟩ := (isByte_iff v).1 hv
  have hbyte : byte? (.int bv) = some (UInt8.ofNat bv) := by
    rw [byte?_iff, u8_toNat hbv]
  obtain ⟨k, rfl⟩ := isNat_of hi h0
  rw [impl_lt, impl_bytesLen] at hlt
  have hk : k < bs.size := by
    change MathVal.lt (.int k) (.int bs.size) = true at hlt
    rw [MathVal.lt_nat] at hlt; exact of_decide_eq_true hlt
  rw [impl_bytesGet, impl_bytesFill]
  have hfill : bytesFill bs (.int bv) = fillLoop bs.size (UInt8.ofNat bv) (ByteArray.emptyWithCapacity bs.size) := by
    unfold bytesFill; rw [hbyte]
  rw [hfill, bytesGet_nat, fillLoop_size, emptyCap_size, Nat.zero_add]
  simp only [hk, ↓reduceIte]
  have hg : (fillLoop bs.size (UInt8.ofNat bv) (ByteArray.emptyWithCapacity bs.size)).get! k = UInt8.ofNat bv := by
    apply fillLoop_get_all
    · rw [emptyCap_size]; omega
    · intro j hj; rw [emptyCap_size] at hj; omega
  rw [hg, u8_toNat hbv]

/-- `Engine.Impl` satisfies `Model.ByteLaws`. -/
theorem byteLaws : Model.ByteLaws Impl where
  bytesLen_nonneg := bytesLen_nonneg_law
  bytesGet_bounds := bytesGet_bounds_law
  bytesGet_byte := bytesGet_byte_law
  bytesZero_len := bytesZero_len_law
  bytesZero_get := bytesZero_get_law
  bytesSet_len := bytesSet_len_law
  bytesSet_get := bytesSet_get_law
  bytesFill_len := bytesFill_len_law
  bytesFill_get := bytesFill_get_law

end Engine.Impl
