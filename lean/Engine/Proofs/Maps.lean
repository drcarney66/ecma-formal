module

public import Engine.Proofs.Seq

@[expose] public section

/-!
# The laws of Records, property tables and the store at the engine's model

A Record's fields and an object's properties are well-formed maps in creation order (`WMap`), whose laws are
`OMap.WF`'s; the store is an array of cells, an address an index of it.
-/

namespace Engine.Impl
open Ecma Engine.Model

variable {α : Type}

/-- A property key. -/
abbrev PKey := Array UInt16 ⊕ (Nat × Option (Array UInt16))

/-! Maps, at any key with a lawful `==`. -/

section
variable {K : Type} [BEq K] [Hashable K] [LawfulBEq K]
set_option linter.unusedSectionVars false

theorem wget_empty (k : K) : (WMap.empty : WMap K α).get k = none := by
  show (OMap.empty : OMap K α).get k = none
  simp [OMap.get, OMap.empty]

theorem wget_put [DecidableEq K] (m : WMap K α) (k : K) (a : α) (g : K) :
    (m.put k a).get g = if g = k then some a else m.get g := m.property.get_put k a g

theorem wget_del [DecidableEq K] (m : WMap K α) (k g : K) :
    (m.del k).get g = if g = k then none else m.get g := m.property.get_del k g

theorem wkeys_mem (m : WMap K α) (k : K) :
    (m.get k).isSome = true ↔ ∃ i, Impl.seqGet m.keys i = some k := by
  rw [show m.get k = m.val.get k from rfl, m.property.mem_keys k]
  constructor
  · rintro ⟨p, hp⟩
    exact ⟨.int p, by rw [seqGet_nat]; exact hp⟩
  · rintro ⟨i, hi⟩
    obtain ⟨p, _, _, hp⟩ := seqGet_idx hi
    exact ⟨p, hp⟩

theorem wkeys_once (m : WMap K α) (k : K) (i j : MathVal) (hi : Impl.seqGet m.keys i = some k)
    (hj : Impl.seqGet m.keys j = some k) : i = j := by
  obtain ⟨p, rfl, _, hp⟩ := seqGet_idx hi
  obtain ⟨q, rfl, _, hq⟩ := seqGet_idx hj
  rw [m.property.keys_once hp hq]

theorem wkeys_put_new (m : WMap K α) (k : K) (a : α) (h : m.get k = none) : (m.put k a).keys = m.keys.push k :=
  m.property.keys_put_new a h

theorem wkeys_put_old (m : WMap K α) (k : K) (a : α) (h : (m.get k).isSome = true) : (m.put k a).keys = m.keys :=
  m.property.keys_put_old a h

theorem wkeys_del (m : WMap K α) (k : K) (i : MathVal) (h : Impl.seqGet m.keys i = some k) :
    (m.del k).keys = Impl.seqRemove m.keys i := by
  obtain ⟨p, rfl, _, hp⟩ := seqGet_idx h
  rw [seqRemove_nat]
  exact m.property.keys_del hp

theorem wdel_absent (m : WMap K α) (k : K) (h : m.get k = none) : m.del k = m :=
  Subtype.ext (m.property.del_absent h)

end

/-! §6.2.1's Records. -/

theorem recGet_empty : ∀ (f : FieldId), Impl.recGet (Impl.recEmpty (α := α)) f = none := wget_empty

theorem recGet_set : ∀ (r : WMap FieldId α) (f : FieldId) (a : α) (g : FieldId),
    Impl.recGet (Impl.recSet r f a) g = if g = f then some a else Impl.recGet r g := wget_put

theorem recGet_del : ∀ (r : WMap FieldId α) (f g : FieldId),
    Impl.recGet (Impl.recDel r f) g = if g = f then none else Impl.recGet r g := wget_del

theorem recKeys_mem : ∀ (r : WMap FieldId α) (f : FieldId),
    (Impl.recGet r f).isSome = true ↔ ∃ i, Impl.seqGet (Impl.recKeys r) i = some f := wkeys_mem

theorem recKeys_once : ∀ (r : WMap FieldId α) (f : FieldId) (i j : MathVal),
    Impl.seqGet (Impl.recKeys r) i = some f → Impl.seqGet (Impl.recKeys r) j = some f → i = j := wkeys_once

/-! §6.1.7's property tables. -/

theorem propsGet_empty : ∀ (k : PKey), Impl.propsGet (Impl.propsEmpty (α := α)) k = none := wget_empty

theorem propsGet_put_self : ∀ (p : WMap PKey α) (k : PKey) (a : α), Impl.propsGet (Impl.propsPut p k a) k = some a := by
  intro p k a
  classical
  exact (wget_put p k a k).trans (if_pos rfl)

theorem propsGet_put_other : ∀ (p : WMap PKey α) (k : PKey) (a : α) (k' : PKey), k' ≠ k →
    Impl.propsGet (Impl.propsPut p k a) k' = Impl.propsGet p k' := by
  intro p k a k' h
  classical
  exact (wget_put p k a k').trans (if_neg h)

theorem propsGet_del_self : ∀ (p : WMap PKey α) (k : PKey), Impl.propsGet (Impl.propsDel p k) k = none := by
  intro p k
  classical
  exact (wget_del p k k).trans (if_pos rfl)

theorem propsGet_del_other : ∀ (p : WMap PKey α) (k k' : PKey), k' ≠ k →
    Impl.propsGet (Impl.propsDel p k) k' = Impl.propsGet p k' := by
  intro p k k' h
  classical
  exact (wget_del p k k').trans (if_neg h)

theorem propsKeys_mem : ∀ (p : WMap PKey α) (k : PKey),
    (Impl.propsGet p k).isSome = true ↔ ∃ i, Impl.seqGet (Impl.propsKeys p) i = some k := wkeys_mem

theorem propsKeys_once : ∀ (p : WMap PKey α) (k : PKey) (i j : MathVal),
    Impl.seqGet (Impl.propsKeys p) i = some k → Impl.seqGet (Impl.propsKeys p) j = some k → i = j := wkeys_once

theorem propsKeys_put_new : ∀ (p : WMap PKey α) (k : PKey) (a : α), Impl.propsGet p k = none →
    Impl.propsKeys (Impl.propsPut p k a) = Impl.seqPush (Impl.propsKeys p) k := wkeys_put_new

theorem propsKeys_put_old : ∀ (p : WMap PKey α) (k : PKey) (a : α), (Impl.propsGet p k).isSome = true →
    Impl.propsKeys (Impl.propsPut p k a) = Impl.propsKeys p := wkeys_put_old

theorem propsKeys_del : ∀ (p : WMap PKey α) (k : PKey) (i : MathVal), Impl.seqGet (Impl.propsKeys p) i = some k →
    Impl.propsKeys (Impl.propsDel p k) = Impl.seqRemove (Impl.propsKeys p) i := wkeys_del

theorem propsDel_absent : ∀ (p : WMap PKey α) (k : PKey), Impl.propsGet p k = none → Impl.propsDel p k = p :=
  wdel_absent

/-! §6.1.7's store. -/

theorem heapGet_empty : ∀ (a : Nat), Impl.heapGet (Impl.heapEmpty (α := α)) a = none := by
  intro a
  show (#[] : Array α)[a]? = none
  simp

theorem heapAlloc_fresh : ∀ (h : Array α) (v : α), Impl.heapGet h (Impl.heapAlloc h v).1 = none := by
  intro h v
  show h[h.size]? = none
  simp

theorem heapAlloc_get_self : ∀ (h : Array α) (v : α),
    Impl.heapGet (Impl.heapAlloc h v).2 (Impl.heapAlloc h v).1 = some v := by
  intro h v
  show (h.push v)[h.size]? = some v
  simp

theorem heapAlloc_get_other : ∀ (h : Array α) (v : α) (a : Nat), a ≠ (Impl.heapAlloc h v).1 →
    Impl.heapGet (Impl.heapAlloc h v).2 a = Impl.heapGet h a := by
  intro h v a ha
  have ha : a ≠ h.size := ha
  show (h.push v)[a]? = h[a]?
  rw [Array.getElem?_push]
  simp [ha]

theorem heapGet_set_self : ∀ (h : Array α) (a : Nat) (v : α), (Impl.heapGet h a).isSome = true →
    Impl.heapGet (Impl.heapSet h a v) a = some v := by
  intro h a v hs
  have hs : (h[a]?).isSome = true := hs
  show (h.setIfInBounds a v)[a]? = some v
  have : a < h.size := by simpa using hs
  simp [this]

theorem heapGet_set_other : ∀ (h : Array α) (a : Nat) (v : α) (b : Nat), b ≠ a →
    Impl.heapGet (Impl.heapSet h a v) b = Impl.heapGet h b := by
  intro h a v b hb
  show (h.setIfInBounds a v)[b]? = h[b]?
  rw [Array.getElem?_setIfInBounds]
  simp [Ne.symm hb]

theorem heapSet_none : ∀ (h : Array α) (a : Nat) (v : α), Impl.heapGet h a = none → Impl.heapSet h a v = h := by
  intro h a v hn
  have hn : h[a]? = none := hn
  show h.setIfInBounds a v = h
  have : h.size ≤ a := by simpa using hn
  simp only [Array.setIfInBounds]
  rw [dif_neg (by omega)]

end Engine.Impl
