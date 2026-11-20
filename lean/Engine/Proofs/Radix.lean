module

public import Engine.Model

@[expose] public section

/-! # Proofs of `Model.strRepeat` and `Model.intToRadix` for `Engine.Impl` -/

namespace Engine.Model

private theorem impl_ofNat (n : Nat) : Impl.ofNat n = .int n := rfl
private theorem impl_strLit (s : String) : Impl.strLit s = utf16 s := rfl
private theorem impl_strConcat (s t : Array UInt16) : Impl.strConcat s t = s ++ t := rfl
private theorem impl_strRepeat (n : MathVal) (s : Array UInt16) :
    Impl.strRepeat n s = strRepeat n s := rfl

private theorem idx_nat (n : Nat) : MathVal.idx (.int n) = some n := by
  simp [MathVal.idx]

private theorem idx_zero : MathVal.idx (.int 0) = some 0 := idx_nat 0

private theorem utf16_empty : utf16 "" = #[] := by
  unfold utf16; rw [String.foldl_eq_foldl_toList]; rfl

private theorem mkEmpty_eq (c : Nat) : Array.mkEmpty (α := UInt16) c = #[] := rfl

private theorem strRepeatAux_acc (s : Array UInt16) :
    ∀ k acc, strRepeatAux s k acc = acc ++ strRepeatAux s k #[]
  | 0, acc => by simp [strRepeatAux]
  | k + 1, acc => by
    simp only [strRepeatAux]
    rw [strRepeatAux_acc s k (acc ++ s), strRepeatAux_acc s k (#[] ++ s)]
    simp [Array.append_assoc]

private theorem strRepeatAux_succ (s : Array UInt16) :
    ∀ k, strRepeatAux s (k + 1) #[] = strRepeatAux s k #[] ++ s
  | 0 => by simp [strRepeatAux]
  | k + 1 => by
    calc strRepeatAux s (k + 2) #[]
      _ = strRepeatAux s (k + 1) s := by simp [strRepeatAux]
      _ = s ++ strRepeatAux s (k + 1) #[] := strRepeatAux_acc s (k + 1) s
      _ = s ++ (strRepeatAux s k #[] ++ s) := by rw [strRepeatAux_succ s k]
      _ = (s ++ strRepeatAux s k #[]) ++ s := Array.append_assoc.symm
      _ = strRepeatAux s k s ++ s := by rw [← strRepeatAux_acc s k s]
      _ = strRepeatAux s (k + 1) #[] ++ s := by simp [strRepeatAux]

theorem strRepeat_zero (s : Array UInt16) :
    Impl.strRepeat (Impl.ofNat 0) s = Impl.strLit "" := by
  rw [impl_ofNat, impl_strRepeat, impl_strLit, utf16_empty, Int.natCast_zero]
  unfold strRepeat
  split
  · rfl
  · simp only [idx_zero, strRepeatAux, mkEmpty_eq]

theorem strRepeat_succ (n : Nat) (s : Array UInt16) :
    Impl.strRepeat (Impl.ofNat (n + 1)) s =
      Impl.strConcat (Impl.strRepeat (Impl.ofNat n) s) s := by
  rw [impl_ofNat, impl_strRepeat, impl_strConcat, impl_strRepeat, impl_ofNat]
  unfold strRepeat
  split
  · rename_i hs
    have hem : s = #[] := Array.size_eq_zero_iff.mp (by simpa [Array.isEmpty] using hs)
    subst hem; simp
  · simp only [idx_nat, mkEmpty_eq, strRepeatAux_succ]

private theorem radixLoop_lt {r : Nat} (hr : 2 ≤ r) {n : Nat} (hn : n < r) (acc : List UInt16) :
    radixLoop r hr n acc = radixDigit n :: acc := by
  rw [radixLoop]; simp [hn]

private theorem radixLoop_ge {r : Nat} (hr : 2 ≤ r) {n : Nat} (hn : r ≤ n) (acc : List UInt16) :
    radixLoop r hr n acc = radixLoop r hr (n / r) (radixDigit (n % r) :: acc) := by
  have hnot : ¬ n < r := by omega
  rw [radixLoop]; simp [hnot]

private theorem radixLoop_acc {r : Nat} (hr : 2 ≤ r) :
    ∀ n acc, radixLoop r hr n acc = radixLoop r hr n [] ++ acc := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro acc
    by_cases hn : n < r
    · rw [radixLoop_lt hr hn acc, radixLoop_lt hr hn []]; simp
    · have hle : r ≤ n := by omega
      have hlt : n / r < n := Nat.div_lt_self (by omega) (by omega)
      rw [radixLoop_ge hr hle acc, radixLoop_ge hr hle []]
      rw [ih (n / r) hlt (radixDigit (n % r) :: acc), ih (n / r) hlt [radixDigit (n % r)]]
      simp [List.append_assoc]

private theorem utf16_digits36 :
    utf16 "0123456789abcdefghijklmnopqrstuvwxyz" =
      #[48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 97, 98, 99, 100, 101, 102, 103, 104,
        105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122] := by
  unfold utf16; rw [String.foldl_eq_foldl_toList]; rfl

private theorem radixDigit_eq_extract (d : Nat) (hd : d < 36) :
    #[radixDigit d] = (utf16 "0123456789abcdefghijklmnopqrstuvwxyz").extract d (d + 1) := by
  rw [utf16_digits36]
  have hall : ∀ k : Fin 36,
      #[radixDigit k.1] = (#[48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 97, 98, 99, 100, 101, 102, 103, 104,
        105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122] :
        Array UInt16).extract k.1 (k.1 + 1) := by
    decide
  exact hall ⟨d, hd⟩

theorem intToRadix_digit (n r : Nat) (hr1 : 2 ≤ r) (hr2 : r ≤ 36) (hn : n < r) :
    Impl.intToRadix (Impl.ofNat n) (Impl.ofNat r) =
      Impl.strSub (Impl.strLit "0123456789abcdefghijklmnopqrstuvwxyz") (Impl.ofNat n) (Impl.ofNat (n + 1)) := by
  simp only [impl_strLit]
  unfold intToRadix
  simp only [idx_nat, hr1, hr2, and_self, ↓reduceDIte, radixLoop_lt hr1 hn []]
  exact radixDigit_eq_extract n (by omega)

theorem intToRadix_div (n r : Nat) (hr1 : 2 ≤ r) (hr2 : r ≤ 36) (hn : r ≤ n) :
    Impl.intToRadix (Impl.ofNat n) (Impl.ofNat r) =
      Impl.strConcat (Impl.intToRadix (Impl.ofNat (n / r)) (Impl.ofNat r))
        (Impl.intToRadix (Impl.ofNat (n % r)) (Impl.ofNat r)) := by
  change intToRadix (.int n) (.int r) = intToRadix (.int ↑(n / r)) (.int r) ++ intToRadix (.int ↑(n % r)) (.int r)
  unfold intToRadix
  have hmod : n % r < r := Nat.mod_lt n (by omega)
  simp only [idx_nat, hr1, hr2, and_self, ↓reduceDIte]
  rw [radixLoop_ge hr1 hn [], radixLoop_acc hr1 (n / r) [radixDigit (n % r)], radixLoop_lt hr1 hmod []]
  apply Array.toList_inj.1
  simp only [Array.toList_append]

end Engine.Model
