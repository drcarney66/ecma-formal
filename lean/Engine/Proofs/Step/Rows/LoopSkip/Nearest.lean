module

public import Engine.Proofs.Step.Rows.LoopSkip.Skip

@[expose] public section

namespace Engine.Machine

open Ecma Ecma.Machine Engine.Accel

/-! ## `nearestKey` -/

/-- A key an object has is among its hash index's keys. -/
theorem ls_mem_indexKeys (ps : F.Props (Val F)) (k : F.Str ⊕ F.Sym) (h : (F.propsGet ps k).isSome = true) :
    k ∈ indexKeys ps := by
  have h' : (Model.OMap.get ps.val k).isSome = true := h
  show k ∈ ps.val.index.keys
  rw [Std.HashMap.mem_keys, Std.HashMap.mem_iff_isSome_getElem?]
  unfold Model.OMap.get at h'
  cases hi : ps.val.index[k]? with
  | none => simp [hi] at h'
  | some i => rfl

/-- `nearestKey`'s update at a distance. -/
def lsNUpd (p : Nat) (d : Int) (acc : Option Nat) : Option Nat :=
  if p < d then some (match acc with
    | some e => min e d.toNat
    | none => d.toNat) else acc

/-- `nearestKey`'s step at a key. -/
def lsNStep (desc : Bool) (i p : Nat) (acc : Option Nat) (k : F.Str ⊕ F.Sym) : Option Nat :=
  match indexOf (M := F) k with
  | some (.int j) => lsNUpd p (if desc then (i : Int) - j else j - (i : Int)) acc
  | _ => acc

theorem ls_nearest_eq (ch : List (F.Props (Val F))) (desc : Bool) (i p : Nat) :
    nearestKey ch desc i p = ch.foldl (fun acc ps => (indexKeys ps).foldl (lsNStep desc i p) acc) none := rfl

theorem ls_nupd_inv (p : Nat) (d : Int) (acc : Option Nat) (h : ∀ e, acc = some e → p < e) :
    ∀ e, lsNUpd p d acc = some e → p < e := by
  intro e he
  unfold lsNUpd at he
  by_cases hpd : (p : Int) < d
  · rw [if_pos hpd] at he
    cases acc with
    | none =>
      have he' : d.toNat = e := Option.some.inj he
      omega
    | some e' =>
      have := h e' rfl
      have he' : min e' d.toNat = e := Option.some.inj he
      omega
  · rw [if_neg hpd] at he
    exact h e he

theorem ls_nupd_mono (p j : Nat) (d : Int) (acc : Option Nat) (h : ∃ e, acc = some e ∧ e ≤ j) :
    ∃ e, lsNUpd p d acc = some e ∧ e ≤ j := by
  obtain ⟨e, rfl, he⟩ := h
  unfold lsNUpd
  by_cases hpd : (p : Int) < d
  · rw [if_pos hpd]
    exact ⟨min e d.toNat, rfl, by omega⟩
  · rw [if_neg hpd]
    exact ⟨e, rfl, he⟩

theorem ls_nupd_hit (p j : Nat) (acc : Option Nat) (hp : p < j) : ∃ e, lsNUpd p (j : Int) acc = some e ∧ e ≤ j := by
  unfold lsNUpd
  rw [if_pos (by omega)]
  cases acc with
  | none => exact ⟨(j : Int).toNat, rfl, by omega⟩
  | some e => exact ⟨min e (j : Int).toNat, rfl, by omega⟩

theorem ls_nstep_inv (desc : Bool) (i p : Nat) (acc : Option Nat) (k : F.Str ⊕ F.Sym)
    (h : ∀ e, acc = some e → p < e) : ∀ e, lsNStep desc i p acc k = some e → p < e := by
  unfold lsNStep
  split
  · exact ls_nupd_inv p _ acc h
  · exact h

theorem ls_nstep_mono (desc : Bool) (i p j : Nat) (acc : Option Nat) (k : F.Str ⊕ F.Sym)
    (h : ∃ e, acc = some e ∧ e ≤ j) : ∃ e, lsNStep desc i p acc k = some e ∧ e ≤ j := by
  unfold lsNStep
  split
  · exact ls_nupd_mono p j _ acc h
  · exact h

theorem ls_nstep_hit (desc : Bool) (i p j : Nat) (acc : Option Nat) (k : F.Str ⊕ F.Sym) (J : Int)
    (hk : indexOf (M := F) k = some (.int J)) (hd : (if desc then (i : Int) - J else J - (i : Int)) = (j : Int))
    (hp : p < j) : ∃ e, lsNStep desc i p acc k = some e ∧ e ≤ j := by
  unfold lsNStep
  rw [hk]
  simp only [hd]
  exact ls_nupd_hit p j acc hp

theorem ls_foldl_keep {α β : Type} (f : β → α → β) (B : β → Prop) (hf : ∀ b a, B b → B (f b a)) :
    ∀ (l : List α) (b : β), B b → B (l.foldl f b) := by
  intro l
  induction l with
  | nil => intro b hb; exact hb
  | cons a l ih => intro b hb; exact ih _ (hf b a hb)

theorem ls_foldl_hit {α β : Type} (f : β → α → β) (B : β → Prop) (hf : ∀ b a, B b → B (f b a)) (a0 : α)
    (h0 : ∀ b, B (f b a0)) : ∀ (l : List α) (b : β), a0 ∈ l → B (l.foldl f b) := by
  intro l
  induction l with
  | nil => intro b hm; cases hm
  | cons a l ih =>
    intro b hm
    rcases List.mem_cons.mp hm with rfl | hm
    · exact ls_foldl_keep f B hf l _ (h0 b)
    · exact ih _ hm

/-- `nearestKey` is right, from the index of an index key's String. -/
theorem ls_nearest_of (hidx : ∀ n : Nat, indexOf (M := F) (indexKey n) = some (Model.MathVal.int n))
    (ch : List (F.Props (Val F))) (desc : Bool) (i : Nat) : LsNearest ch desc i := by
  refine ⟨?_, ?_⟩
  · rw [ls_nearest_eq]
    refine ls_foldl_keep _ (fun acc => ∀ e, acc = some e → probeLimit < e) ?_ ch none (fun e he => by cases he)
    intro acc ps hacc
    exact ls_foldl_keep _ (fun acc => ∀ e, acc = some e → probeLimit < e)
      (fun b a hb => ls_nstep_inv desc i probeLimit b a hb) _ acc hacc
  · intro j hj hdj hhas
    simp only [chainHas, List.any_eq_true] at hhas
    obtain ⟨ps, hps, hk⟩ := hhas
    have hmem := ls_mem_indexKeys ps _ hk
    rw [ls_nearest_eq]
    have inner : ∀ (ps' : F.Props (Val F)) (acc : Option Nat), (∃ e, acc = some e ∧ e ≤ j) →
        ∃ e, (indexKeys ps').foldl (lsNStep desc i probeLimit) acc = some e ∧ e ≤ j := fun ps' acc hacc =>
      ls_foldl_keep _ (fun acc => ∃ e, acc = some e ∧ e ≤ j)
        (fun b a hb => ls_nstep_mono desc i probeLimit j b a hb) _ acc hacc
    refine ls_foldl_hit _ (fun acc => ∃ e, acc = some e ∧ e ≤ j) (fun b a hb => inner a b hb) ps ?_ ch none hps
    intro acc
    refine ls_foldl_hit _ (fun acc => ∃ e, acc = some e ∧ e ≤ j)
      (fun b a hb => ls_nstep_mono desc i probeLimit j b a hb) _ ?_ _ acc hmem
    intro b
    refine ls_nstep_hit desc i probeLimit j b _ _ (hidx _) ?_ hj
    cases desc with
    | false => simp only [Bool.false_eq_true, ↓reduceIte]; omega
    | true =>
      have := hdj rfl
      simp only [↓reduceIte]
      omega


/-! ## The index of an index key -/

/-- The code units of the decimal digits of `n`, as mathematical values. -/
def lsW (n : Nat) : Array Model.MathVal := (Model.utf16 (toString n)).map fun u => Model.MathVal.int u.toNat

theorem ls_utf16_digits (n : Nat) : Model.utf16 (toString n) =
    (Nat.toDigits 10 n).foldl (fun (a : Array UInt16) c =>
      let v := c.val.toNat
      if v < 0x10000 then a.push v.toUInt16
      else (a.push (0xD800 + (v - 0x10000) / 0x400).toUInt16).push (0xDC00 + (v - 0x10000) % 0x400).toUInt16) #[] := by
  unfold Model.utf16
  rw [String.foldl_eq_foldl_toList, Nat.toString_eq_repr, Nat.toList_repr]

theorem ls_digit_unit (a : Array UInt16) (d : Nat) (hd : d < 10) :
    (let v := (Nat.digitChar d).val.toNat
      if v < 0x10000 then a.push v.toUInt16
      else (a.push (0xD800 + (v - 0x10000) / 0x400).toUInt16).push (0xDC00 + (v - 0x10000) % 0x400).toUInt16) =
    a.push (48 + d).toUInt16 := by
  have h : (Nat.digitChar d).val.toNat = 48 + d := Nat.toNat_digitChar_of_lt_ten hd
  simp only [h]
  rw [if_pos (by omega)]

theorem ls_W_lt (n : Nat) (h : n < 10) : lsW n = #[Model.MathVal.int ((48 + n : Nat) : Int)] := by
  unfold lsW
  rw [ls_utf16_digits, Nat.toDigits_of_lt_base h]
  simp only [List.foldl_cons, List.foldl_nil]
  rw [ls_digit_unit _ _ h]
  simp
  omega

theorem ls_W_ge (n : Nat) (h : 10 ≤ n) :
    lsW n = (lsW (n / 10)).push (Model.MathVal.int ((48 + n % 10 : Nat) : Int)) := by
  unfold lsW
  rw [ls_utf16_digits, ls_utf16_digits, Nat.toDigits_of_base_le (by omega) h, List.foldl_append]
  simp only [List.foldl_cons, List.foldl_nil]
  rw [ls_digit_unit _ _ (Nat.mod_lt _ (by omega))]
  simp
  have e : ((48 + (n : Int) % 10) % 65536) = 48 + (n : Int) % 10 := by omega
  rw [e]

theorem ls_W_size (n : Nat) : 0 < (lsW n).size := by
  by_cases h : n < 10
  · rw [ls_W_lt n h]; simp
  · rw [ls_W_ge n (by omega)]; simp

/-- The digits' fold of `indexOf`. -/
def lsFold (acc : Option Model.MathVal) (u : Model.MathVal) : Option Model.MathVal :=
  acc.bind fun a =>
    if !Model.MathVal.lt u (.int 48) && Model.MathVal.lt u (.int 58) then
      some (Model.MathVal.add (Model.MathVal.mul a (.int 10)) (Model.MathVal.add u (Model.MathVal.neg (.int 48))))
    else none

theorem ls_fold_digit (a d : Nat) (hd : d < 10) :
    lsFold (some (.int a)) (.int ((48 + d : Nat) : Int)) = some (.int ((a * 10 + d : Nat) : Int)) := by
  simp [lsFold, Model.MathVal.lt, Model.MathVal.add, Model.MathVal.mul, Model.MathVal.neg]
  omega

theorem ls_W_fold : ∀ (f n : Nat), n < f → (lsW n).foldl lsFold (some (.int 0)) = some (.int (n : Int)) := by
  intro f
  induction f with
  | zero => intro n h; omega
  | succ f ih =>
    intro n hn
    by_cases h : n < 10
    · rw [ls_W_lt n h]
      have := ls_fold_digit 0 n h
      simpa using this
    · rw [ls_W_ge n (by omega), Array.foldl_push, ih (n / 10) (by omega)]
      have := ls_fold_digit (n / 10) (n % 10) (Nat.mod_lt _ (by omega))
      rw [this]
      congr 2
      omega

theorem ls_W_first : ∀ (f n : Nat), n < f → 0 < n → ∃ u : Int, (lsW n)[0]? = some (.int u) ∧ u ≠ 48 := by
  intro f
  induction f with
  | zero => intro n h; omega
  | succ f ih =>
    intro n hn h0
    by_cases h : n < 10
    · rw [ls_W_lt n h]
      exact ⟨((48 + n : Nat) : Int), by simp, by omega⟩
    · obtain ⟨u, hu, hne⟩ := ih (n / 10) (by omega) (by omega)
      rw [ls_W_ge n (by omega)]
      refine ⟨u, ?_, hne⟩
      rw [Array.getElem?_push]
      have := ls_W_size (n / 10)
      rw [if_neg (by omega)]
      exact hu

/-- The index of the key ToString(𝔽(n)). -/
theorem ls_indexOf (n : Nat) : indexOf (M := F) (indexKey n) = some (Model.MathVal.int n) := by
  show (if Model.MathVal.eq (.int (lsW n).size) (.int 0) then none
    else if Model.MathVal.lt (.int 1) (.int (lsW n).size) &&
        ((Model.MathVal.idx (.int 0)).bind fun k => (lsW n)[k]?).any (Model.MathVal.eq · (.int 48)) then none
    else (lsW n).foldl lsFold (some (.int 0))) = _
  have hs := ls_W_size n
  have hs' : ¬ ((lsW n).size : Int) = 0 := by omega
  rw [if_neg (by simpa [Model.MathVal.eq] using hs'), ls_W_fold (n + 1) n (by omega)]
  by_cases h : n < 10
  · rw [if_neg]
    rw [ls_W_lt n h]
    simp [Model.MathVal.lt]
  · obtain ⟨u, hu, hne⟩ := ls_W_first (n + 1) n (by omega) (by omega)
    rw [if_neg]
    simp [Model.MathVal.idx, hu, Model.MathVal.eq, hne]

/-- `nearestKey` is right. -/
theorem ls_nearest (ch : List (F.Props (Val F))) (desc : Bool) (i : Nat) : LsNearest ch desc i :=
  ls_nearest_of ls_indexOf ch desc i

end Engine.Machine
