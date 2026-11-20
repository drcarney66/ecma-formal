module

public import Engine.Proofs.Math

@[expose] public section

/-!
# The laws of Strings, Symbols and addresses at the engine's model

A String is an array of code units (§6.1.4), a Symbol a number with a description, an address a number.
-/

namespace Engine.Model.MathVal

theorem idx_nat (k : Nat) : idx (.int k) = some k := by simp [idx]

theorem idx_some {i : MathVal} {k : Nat} (h : idx i = some k) : i = .int k := by
  cases i with
  | int j =>
    simp only [idx] at h
    split at h
    · rename_i hj
      injection h with h
      subst h
      congr 1
      exact (Int.toNat_of_nonneg hj).symm
    · cases h
  | frac q hq => cases h

theorem lt_nat (a b : Nat) : lt (.int a) (.int b) = decide (a < b) := by
  simp [lt]

/-- A difference from an integer that is an integer is of an integer. -/
theorem sub_int_eq {a : MathVal} {n m : Int} (h : add a (neg (.int n)) = .int m) : a = .int (m + n) := by
  apply toQ_inj
  have h := congrArg toQ h
  simp only [toQ_add, toQ_neg, toQ_int] at h
  rw [toQ_int, Rat.intCast_add, ← h, Rat.add_assoc, Rat.neg_add_cancel, Rat.add_zero]

end Engine.Model.MathVal

namespace Engine.Impl
open Ecma Engine.Model

/-- `Impl.strAt`, unfolded. -/
theorem strAt_def (s : Array UInt16) (i : MathVal) :
    Impl.strAt s i = (MathVal.idx i).bind fun k => s[k]?.map fun u => MathVal.int u.toNat := rfl

theorem strAt_nat (s : Array UInt16) (k : Nat) :
    Impl.strAt s (.int k) = s[k]?.map fun u => MathVal.int u.toNat := by
  rw [strAt_def, MathVal.idx_nat]; rfl

theorem strAt_some : ∀ (s : Array UInt16) (i c : MathVal), Impl.strAt s i = some c →
    (∃ k, i = Impl.ofNat k ∧ Impl.lt i (Impl.strLen s) = true) ∧ ∃ u, u < 65536 ∧ c = Impl.ofNat u := by
  intro s i c h
  rw [strAt_def] at h
  cases hi : MathVal.idx i with
  | none => rw [hi] at h; cases h
  | some k =>
    have e := MathVal.idx_some hi
    subst e
    rw [hi] at h
    simp only [Option.bind_some] at h
    cases hu : s[k]? with
    | none => rw [hu] at h; cases h
    | some u =>
      rw [hu] at h
      injection h with hc
      have hk : k < s.size := (Array.getElem?_eq_some_iff.1 hu).1
      refine ⟨⟨k, rfl, ?_⟩, ⟨u.toNat, UInt16.toNat_lt u, hc.symm⟩⟩
      show MathVal.lt (.int k) (.int s.size) = true
      rw [MathVal.lt_nat]
      exact decide_eq_true hk

theorem strEq_iff : ∀ s t : Array UInt16, Impl.strEq s t = true ↔ s = t := by
  intro s t
  show (s == t) = true ↔ s = t
  simp

theorem symEq_iff : ∀ a b : Nat × Option (Array UInt16), Impl.symEq a b = true ↔ a = b := by
  intro a b
  show (a.1 == b.1 && a.2 == b.2) = true ↔ a = b
  obtain ⟨a1, a2⟩ := a
  obtain ⟨b1, b2⟩ := b
  simp [Prod.mk.injEq]

theorem symDesc_new : ∀ (k : Nat) (d : Option (Array UInt16)), Impl.symDesc (Impl.symNew k d) = d := fun _ _ => rfl

theorem symNew_inj : ∀ (k : Nat) (d : Option (Array UInt16)) (k' : Nat) (d' : Option (Array UInt16)),
    Impl.symNew k d = Impl.symNew k' d' → k = k' := by
  intro k d k' d' h
  exact (Prod.mk.inj h).1

theorem addrEq_iff : ∀ a b : Nat, Impl.addrEq a b = true ↔ a = b := by
  intro a b
  show (a == b) = true ↔ a = b
  simp


theorem strConcat_len : ∀ s t : Array UInt16, Impl.strLen (Impl.strConcat s t) = Impl.add (Impl.strLen s) (Impl.strLen t) := by
  intro s t
  show MathVal.int ((s ++ t).size : Nat) = MathVal.add (.int s.size) (.int t.size)
  simp [MathVal.add]

theorem strOfUnit_len : ∀ u : Nat, u < 65536 → Impl.strLen (Impl.strOfUnit (Impl.ofNat u)) = Impl.ofNat 1 := by
  intro u _
  show Impl.strLen (match MathVal.idx (.int u) with | some k => #[k.toUInt16] | none => #[]) = MathVal.int 1
  rw [MathVal.idx_nat]
  rfl

theorem strOfUnit_at : ∀ u : Nat, u < 65536 →
    Impl.strAt (Impl.strOfUnit (Impl.ofNat u)) (Impl.ofNat 0) = some (Impl.ofNat u) := by
  intro u hu
  show Impl.strAt (match MathVal.idx (.int u) with | some k => #[k.toUInt16] | none => #[]) (.int (0 : Nat)) = some (MathVal.int u)
  rw [MathVal.idx_nat, strAt_nat]
  have : (u.toUInt16).toNat = u := by
    simp [Nat.toUInt16, UInt16.toNat_ofNat', Nat.mod_eq_of_lt (show u < 2 ^ 16 from hu)]
  simp [this]

/-- A List's elements are the array's. -/
theorem seqList_eq {α : Type} (xs : Array α) : seqList (M := Impl) xs = xs.toList := by
  show Array.foldl (fun l x => l ++ [x]) [] xs = _
  rw [← Array.foldl_toList]
  generalize xs.toList = l
  have : ∀ (l acc : List α), List.foldl (fun l x => l ++ [x]) acc l = acc ++ l := by
    intro l; induction l with
    | nil => intro acc; simp
    | cons x xs ih => intro acc; simp [ih]
  simpa using this l []

theorem strUnits_len : ∀ s : Array UInt16, Impl.ofNat (seqList (M := Impl) (Impl.strUnits s)).length = Impl.strLen s := by
  intro s
  show MathVal.int ((seqList (M := Impl) (s.map fun u => MathVal.int u.toNat)).length : Nat) = MathVal.int s.size
  rw [seqList_eq]
  simp

theorem strUnits_at : ∀ (s : Array UInt16) (k : Nat),
    (seqList (M := Impl) (Impl.strUnits s))[k]? = Impl.strAt s (Impl.ofNat k) := by
  intro s k
  show (seqList (M := Impl) (s.map fun u => MathVal.int u.toNat))[k]? = Impl.strAt s (.int k)
  rw [seqList_eq, strAt_nat]
  simp

theorem str_ext : ∀ s t : Array UInt16, Impl.strLen s = Impl.strLen t →
    (∀ k, Impl.strAt s (Impl.ofNat k) = Impl.strAt t (Impl.ofNat k)) → s = t := by
  intro s t hl ha
  have hs : s.size = t.size := Int.ofNat.inj (MathVal.int.inj hl)
  apply Array.ext hs
  intro k h1 h2
  have h := ha k
  change Impl.strAt s (.int k) = Impl.strAt t (.int k) at h
  rw [strAt_nat, strAt_nat] at h
  simp only [Array.getElem?_eq_getElem h1, Array.getElem?_eq_getElem h2, Option.map_some] at h
  have h := MathVal.int.inj (Option.some.inj h)
  exact UInt16.toNat_inj.1 (Int.ofNat.inj h)

theorem strConcat_at : ∀ (s t : Array UInt16) (i : MathVal), Impl.strAt (Impl.strConcat s t) i =
    if Impl.lt i (Impl.strLen s) then Impl.strAt s i else Impl.strAt t (Impl.sub i (Impl.strLen s)) := by
  intro s t i
  show Impl.strAt (s ++ t) i = if MathVal.lt i (.int s.size) then Impl.strAt s i
    else Impl.strAt t (MathVal.add i (MathVal.neg (.int s.size)))
  cases i with
  | int j =>
    by_cases hj : 0 ≤ j
    · obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le hj
      rw [MathVal.lt_nat]
      by_cases hk : k < s.size
      · rw [strAt_nat, strAt_nat, Array.getElem?_append_left hk]
        simp [hk]
      · have e : MathVal.add (.int k) (MathVal.neg (.int s.size)) = .int ((k - s.size : Nat) : Int) := by
          simp only [MathVal.add, MathVal.neg]
          congr 1
          omega
        rw [e, strAt_nat, strAt_nat, Array.getElem?_append_right (Nat.le_of_not_lt hk)]
        simp [hk, MathVal.idx_nat]
    · have l : MathVal.lt (.int j) (.int s.size) = true := by
        simp only [MathVal.lt]
        exact decide_eq_true (by omega)
      simp [l, strAt_def, MathVal.idx, hj]
  | frac q hq =>
    have h1 : ∀ u : Array UInt16, Impl.strAt u (.frac q hq) = none := fun _ => rfl
    rw [h1, h1]
    split
    · rfl
    · rw [strAt_def]
      cases hi : MathVal.idx (MathVal.add (.frac q hq) (MathVal.neg (.int s.size))) with
      | none => rfl
      | some k => cases MathVal.sub_int_eq (MathVal.idx_some hi)

theorem strSub_len : ∀ (s : Array UInt16) (i j : Nat), i ≤ j → Impl.lt (Impl.strLen s) (Impl.ofNat j) = false →
    Impl.strLen (Impl.strSub s (Impl.ofNat i) (Impl.ofNat j)) = Impl.ofNat (j - i) := by
  intro s i j hij h
  have hj : j ≤ s.size := by
    have : MathVal.lt (.int s.size) (.int j) = false := h
    rw [MathVal.lt_nat] at this
    exact Nat.le_of_not_lt (of_decide_eq_false this)
  show MathVal.int ((s.extract i j).size : Nat) = MathVal.int ((j - i : Nat) : Int)
  rw [Array.size_extract, Nat.min_eq_left hj]

theorem strSub_at : ∀ (s : Array UInt16) (i j k : Nat), i ≤ j → Impl.lt (Impl.strLen s) (Impl.ofNat j) = false →
    k < j - i → Impl.strAt (Impl.strSub s (Impl.ofNat i) (Impl.ofNat j)) (Impl.ofNat k) =
      Impl.strAt s (Impl.ofNat (i + k)) := by
  intro s i j k hij h hk
  have hj : j ≤ s.size := by
    have : MathVal.lt (.int s.size) (.int j) = false := h
    rw [MathVal.lt_nat] at this
    exact Nat.le_of_not_lt (of_decide_eq_false this)
  show Impl.strAt (s.extract i j) (.int k) = Impl.strAt s (.int ((i + k : Nat) : Int))
  rw [strAt_nat, strAt_nat, Array.getElem?_extract]
  simp [Nat.min_eq_left hj, hk]

theorem toUInt16_toNat {n : Nat} (h : n < 65536) : (n.toUInt16).toNat = n := by
  simp [Nat.toUInt16, UInt16.toNat_ofNat', Nat.mod_eq_of_lt (show n < 2 ^ 16 from h)]

/-- One code point's code units, appended. -/
theorem utf16_step (a : Array UInt16) (c : Char) :
    (let v := c.val.toNat
     if v < 0x10000 then a.push v.toUInt16
     else (a.push (0xD800 + (v - 0x10000) / 0x400).toUInt16).push (0xDC00 + (v - 0x10000) % 0x400).toUInt16).toList.map
      (fun u => MathVal.int u.toNat) =
    a.toList.map (fun u => MathVal.int u.toNat) ++ (utf16Units c.toNat).map fun (n : Nat) => MathVal.int n := by
  have hv : c.val.toNat < 0x110000 := by
    have := c.valid
    simp only [UInt32.isValidChar, Nat.isValidChar] at this
    omega
  show (if c.toNat < 0x10000 then _ else _ : Array UInt16).toList.map _ = _
  have hv : c.toNat < 0x110000 := hv
  unfold utf16Units
  by_cases h : c.toNat < 0x10000
  · simp [h, toUInt16_toNat h]
  · have h1 : 0xD800 + (c.toNat - 0x10000) / 0x400 < 65536 := by omega
    have h2 : 0xDC00 + (c.toNat - 0x10000) % 0x400 < 65536 := by omega
    simp [h]
    omega

theorem strLit_units : ∀ t : String,
    seqList (M := Impl) (Impl.strUnits (Impl.strLit t)) = (strLitUnits t).map Impl.ofNat := by
  intro t
  show seqList (M := Impl) ((utf16 t).map fun u => MathVal.int u.toNat) = (strLitUnits t).map fun (n : Nat) => MathVal.int n
  rw [seqList_eq, Array.toList_map]
  unfold utf16 strLitUnits
  rw [String.foldl_eq_foldl_toList]
  have : ∀ (l : List Char) (a : Array UInt16),
      (l.foldl (fun a c =>
        let v := c.val.toNat
        if v < 0x10000 then a.push v.toUInt16
        else (a.push (0xD800 + (v - 0x10000) / 0x400).toUInt16).push (0xDC00 + (v - 0x10000) % 0x400).toUInt16) a).toList.map
        (fun u => MathVal.int u.toNat) =
      a.toList.map (fun u => MathVal.int u.toNat) ++ (l.flatMap fun c => utf16Units c.toNat).map fun (n : Nat) => MathVal.int n := by
    intro l
    induction l with
    | nil => intro a; simp
    | cons c cs ih =>
      intro a
      rw [List.foldl_cons, ih, utf16_step, List.flatMap_cons, List.map_append, List.append_assoc]
  simpa using this t.toList #[]

end Engine.Impl
