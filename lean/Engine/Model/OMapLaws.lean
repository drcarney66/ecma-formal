module

public import Engine.Model.Bare

@[expose] public section

/-!
# The engine's maps, well-formed

`OMap.WF m`: the index and the entries agree, each position the index holds for a key an entry of
that key and each entry's key indexed at its position. `empty` is well-formed and `put` and `del`
keep it. On a well-formed map `get` reads over `put` and `del`, `keys` lists each present key once,
`put` appends a new key and keeps the keys for a present one, `del` removes its key from them, and
`del` of an absent key is the identity. The laws over the index ask a lawful `==`. `WMap` is the
well-formed maps: the engine's Records and property tables.
-/

namespace Engine.Model.OMap

variable {K α : Type}

/-! The keys of a list of entries. -/

/-- A listed key is the key of an entry. -/
theorem mem_keysL {l : List (Option (K × α))} {k : K} :
    k ∈ l.filterMap (fun e => e.map Prod.fst) ↔ ∃ a, some (k, a) ∈ l := by
  simp only [List.mem_filterMap, Option.map_eq_some_iff]
  constructor
  · rintro ⟨_, hx, ⟨_, a⟩, rfl, rfl⟩
    exact ⟨a, hx⟩
  · rintro ⟨a, h⟩
    exact ⟨_, h, (k, a), rfl, rfl⟩

/-- The key at a position of the keys is an entry's, after as many keyed entries. -/
theorem keysL_pos {l : List (Option (K × α))} {p : Nat} {k : K}
    (h : (l.filterMap (fun e => e.map Prod.fst))[p]? = some k) :
    ∃ i a, l[i]? = some (some (k, a)) ∧ ((l.take i).filterMap (fun e => e.map Prod.fst)).length = p := by
  induction l generalizing p with
  | nil => simp at h
  | cons x t ih =>
    cases x with
    | none =>
      simp only [List.filterMap_cons, Option.map_none] at h
      obtain ⟨i, a, hi, hl⟩ := ih (p := p) h
      exact ⟨i + 1, a, by simpa using hi, by simpa using hl⟩
    | some e =>
      obtain ⟨k', b⟩ := e
      simp only [List.filterMap_cons, Option.map_some] at h
      cases p with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at h
        subst h
        exact ⟨0, b, by simp, by simp⟩
      | succ p =>
        simp only [List.getElem?_cons_succ] at h
        obtain ⟨i, a, hi, hl⟩ := ih (p := p) h
        exact ⟨i + 1, a, by simpa using hi, by simpa using hl⟩

/-- A key of a single entry is listed once. -/
theorem keysL_once {l : List (Option (K × α))} {k : K}
    (hu : ∀ (i j : Nat) (a b : α), l[i]? = some (some (k, a)) → l[j]? = some (some (k, b)) → i = j) {p q : Nat}
    (hp : (l.filterMap (fun e => e.map Prod.fst))[p]? = some k)
    (hq : (l.filterMap (fun e => e.map Prod.fst))[q]? = some k) : p = q := by
  obtain ⟨i, a, hi, rfl⟩ := keysL_pos hp
  obtain ⟨j, b, hj, rfl⟩ := keysL_pos hq
  rw [hu i j a b hi hj]

/-- Replacing an entry by one of the same key keeps the keys. -/
theorem keysL_set {l : List (Option (K × α))} {i : Nat} {y : Option (K × α)}
    (h : ∀ x, l[i]? = some x → x.map Prod.fst = y.map Prod.fst) :
    (l.set i y).filterMap (fun e => e.map Prod.fst) = l.filterMap (fun e => e.map Prod.fst) := by
  induction l generalizing i with
  | nil => simp
  | cons x t ih =>
    cases i with
    | zero =>
      have hx := h x (by simp)
      simp only [List.set_cons_zero, List.filterMap_cons, hx]
    | succ i =>
      simp only [List.set_cons_succ, List.filterMap_cons, ih (i := i) fun x' hx' => h x' (by simpa using hx')]

/-- Removing the one entry of a key removes it from the keys. -/
theorem keysL_del {l : List (Option (K × α))} {k : K} {j p : Nat}
    (hu : ∀ (i : Nat) (a : α), l[i]? = some (some (k, a)) → i = j)
    (hp : (l.filterMap (fun e => e.map Prod.fst))[p]? = some k) :
    (l.set j none).filterMap (fun e => e.map Prod.fst) = (l.filterMap (fun e => e.map Prod.fst)).eraseIdx p := by
  induction l generalizing j p with
  | nil => simp at hp
  | cons x t ih =>
    have tl : ∀ q : Nat, (t.filterMap (fun e => e.map Prod.fst))[q]? = some k → ∃ i, i + 1 = j := fun q hq => by
      obtain ⟨i, a, hi, -⟩ := keysL_pos hq
      exact ⟨i, hu (i + 1) a (by simpa using hi)⟩
    cases j with
    | zero =>
      cases x with
      | none =>
        simp only [List.filterMap_cons, Option.map_none] at hp
        obtain ⟨i, hi⟩ := tl p hp
        omega
      | some e =>
        obtain ⟨k', b⟩ := e
        simp only [List.filterMap_cons, Option.map_some] at hp
        cases p with
        | zero => simp
        | succ p =>
          simp only [List.getElem?_cons_succ] at hp
          obtain ⟨i, hi⟩ := tl p hp
          omega
    | succ j =>
      have hu' : ∀ (i : Nat) (a : α), t[i]? = some (some (k, a)) → i = j := fun i a hi => by
        have := hu (i + 1) a (by simpa using hi)
        omega
      cases x with
      | none =>
        simp only [List.filterMap_cons, Option.map_none] at hp
        simp only [List.set_cons_succ, List.filterMap_cons, Option.map_none]
        exact ih (j := j) (p := p) hu' hp
      | some e =>
        obtain ⟨k', b⟩ := e
        simp only [List.filterMap_cons, Option.map_some] at hp
        cases p with
        | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hp
          subst hp
          have := hu 0 b (by simp)
          omega
        | succ p =>
          simp only [List.getElem?_cons_succ] at hp
          simp only [List.set_cons_succ, List.filterMap_cons, Option.map_some, List.eraseIdx_cons_succ]
          rw [ih (j := j) (p := p) hu' hp]

/-! Well-formed maps. -/

variable [BEq K] [Hashable K]

/-- The index and the entries agree. -/
structure WF (m : OMap K α) : Prop where
  /-- Every position the index holds for a key is an entry of that key. -/
  index_entry : ∀ (k : K) (i : Nat), m.index[k]? = some i → ∃ a, m.entries[i]? = some (some (k, a))
  /-- Every entry's key is indexed at its position. -/
  entry_index : ∀ (i : Nat) (k : K) (a : α), m.entries[i]? = some (some (k, a)) → m.index[k]? = some i

/-- The keys, as a list over the entries. -/
theorem getElem?_keys (m : OMap K α) (p : Nat) :
    m.keys[p]? = (m.entries.toList.filterMap (fun e => e.map Prod.fst))[p]? := by
  rw [← Array.getElem?_toList, keys, Array.toList_filterMap]

/-- The empty map is well-formed. -/
theorem wf_empty : WF (empty : OMap K α) where
  index_entry k i h := by simp [empty] at h
  entry_index i k a h := by simp [empty] at h

namespace WF

variable {m : OMap K α}

/-- Two entries of a key are one. -/
theorem entry_unique (h : WF m) {i j : Nat} {k : K} {a b : α} (hi : m.entries[i]? = some (some (k, a)))
    (hj : m.entries[j]? = some (some (k, b))) : i = j := by
  have e := h.entry_index i k a hi
  rw [h.entry_index j k b hj] at e
  exact (Option.some.inj e).symm

/-- An indexed key reads as its entry. -/
theorem get_of_index (h : WF m) {k : K} {i : Nat} (hi : m.index[k]? = some i) :
    ∃ a, m.entries[i]? = some (some (k, a)) ∧ m.get k = some a := by
  obtain ⟨a, ha⟩ := h.index_entry k i hi
  exact ⟨a, ha, by simp [get, hi, ha]⟩

/-- A key is absent exactly when it is not indexed. -/
theorem get_eq_none (h : WF m) (k : K) : m.get k = none ↔ m.index[k]? = none := by
  cases hi : m.index[k]? with
  | none => simp [get, hi]
  | some i =>
    obtain ⟨a, -, hg⟩ := h.get_of_index hi
    simp [hg]

/-- Putting keeps a map well-formed. -/
theorem put [LawfulBEq K] (h : WF m) (k : K) (x : α) : WF (m.put k x) := by
  cases hk : m.index[k]? with
  | some i =>
    obtain ⟨b, hb⟩ := h.index_entry k i hk
    have hlt := (Array.getElem?_eq_some_iff.mp hb).1
    simp only [OMap.put, hk]
    constructor
    · intro g j hg
      dsimp only at hg ⊢
      obtain ⟨c, hc⟩ := h.index_entry g j hg
      by_cases hij : i = j
      · subst hij
        rw [hb] at hc
        cases hc
        exact ⟨x, Array.getElem?_setIfInBounds_self_of_lt hlt⟩
      · exact ⟨c, by rw [Array.getElem?_setIfInBounds_ne hij]; exact hc⟩
    · intro j g c hj
      dsimp only at hj ⊢
      by_cases hij : i = j
      · subst hij
        rw [Array.getElem?_setIfInBounds_self_of_lt hlt] at hj
        cases hj
        exact hk
      · rw [Array.getElem?_setIfInBounds_ne hij] at hj
        exact h.entry_index j g c hj
  | none =>
    simp only [OMap.put, hk]
    constructor
    · intro g j hg
      dsimp only at hg ⊢
      rw [Std.HashMap.getElem?_insert] at hg
      by_cases hkg : k = g
      · subst hkg
        simp at hg
        subst hg
        exact ⟨x, Array.getElem?_push_size⟩
      · rw [if_neg (by simpa using hkg)] at hg
        obtain ⟨c, hc⟩ := h.index_entry g j hg
        have hlt := (Array.getElem?_eq_some_iff.mp hc).1
        exact ⟨c, by rw [Array.getElem?_push, if_neg (Nat.ne_of_lt hlt)]; exact hc⟩
    · intro j g c hj
      dsimp only at hj ⊢
      rw [Std.HashMap.getElem?_insert]
      rw [Array.getElem?_push] at hj
      by_cases hjs : j = m.entries.size
      · rw [if_pos hjs] at hj
        cases hj
        simp [hjs]
      · rw [if_neg hjs] at hj
        have hg := h.entry_index j g c hj
        have hkg : k ≠ g := by
          rintro rfl
          rw [hk] at hg
          cases hg
        rw [if_neg (by simpa using hkg)]
        exact hg

/-- Deleting keeps a map well-formed. -/
theorem del [LawfulBEq K] (h : WF m) (k : K) : WF (m.del k) := by
  cases hk : m.index[k]? with
  | none =>
    simp only [OMap.del, hk]
    exact h
  | some i =>
    obtain ⟨b, hb⟩ := h.index_entry k i hk
    have hlt := (Array.getElem?_eq_some_iff.mp hb).1
    simp only [OMap.del, hk]
    constructor
    · intro g j hg
      dsimp only at hg ⊢
      rw [Std.HashMap.getElem?_erase] at hg
      have hkg : k ≠ g := by
        rintro rfl
        simp at hg
      rw [if_neg (by simpa using hkg)] at hg
      obtain ⟨c, hc⟩ := h.index_entry g j hg
      have hij : i ≠ j := by
        rintro rfl
        rw [hb] at hc
        cases hc
        exact hkg rfl
      exact ⟨c, by rw [Array.getElem?_setIfInBounds_ne hij]; exact hc⟩
    · intro j g c hj
      dsimp only at hj ⊢
      by_cases hij : i = j
      · subst hij
        rw [Array.getElem?_setIfInBounds_self_of_lt hlt] at hj
        cases hj
      · rw [Array.getElem?_setIfInBounds_ne hij] at hj
        have hg := h.entry_index j g c hj
        have hkg : k ≠ g := by
          rintro rfl
          rw [hk] at hg
          cases hg
          exact hij rfl
        rw [Std.HashMap.getElem?_erase, if_neg (by simpa using hkg)]
        exact hg

/-- Putting reads back (read-over-write). -/
theorem get_put [LawfulBEq K] [DecidableEq K] (h : WF m) (k : K) (x : α) (g : K) :
    (m.put k x).get g = if g = k then some x else m.get g := by
  cases hk : m.index[k]? with
  | some i =>
    obtain ⟨b, hb⟩ := h.index_entry k i hk
    have hlt := (Array.getElem?_eq_some_iff.mp hb).1
    simp only [OMap.put, hk]
    by_cases hgk : g = k
    · subst hgk
      simp [get, hk, Array.getElem?_setIfInBounds_self_of_lt hlt]
    · rw [if_neg hgk]
      simp only [get]
      cases hg : m.index[g]? with
      | none => rfl
      | some j =>
        have hij : i ≠ j := by
          rintro rfl
          obtain ⟨c, hc⟩ := h.index_entry g i hg
          rw [hb] at hc
          cases hc
          exact hgk rfl
        simp only [Array.getElem?_setIfInBounds_ne hij]
  | none =>
    simp only [OMap.put, hk]
    by_cases hgk : g = k
    · subst hgk
      simp [get]
    · rw [if_neg hgk]
      have hkg : ¬k = g := fun e => hgk e.symm
      simp only [get, Std.HashMap.getElem?_insert, beq_iff_eq, hkg, ↓reduceIte]
      cases hg : m.index[g]? with
      | none => rfl
      | some j =>
        obtain ⟨c, hc⟩ := h.index_entry g j hg
        have hlt := (Array.getElem?_eq_some_iff.mp hc).1
        simp only [Array.getElem?_push, Nat.ne_of_lt hlt, ↓reduceIte]

/-- Deleting removes the key and leaves the others. -/
theorem get_del [LawfulBEq K] [DecidableEq K] (h : WF m) (k g : K) :
    (m.del k).get g = if g = k then none else m.get g := by
  cases hk : m.index[k]? with
  | none =>
    simp only [OMap.del, hk]
    by_cases hgk : g = k
    · subst hgk
      rw [if_pos rfl]
      exact (h.get_eq_none g).mpr hk
    · rw [if_neg hgk]
  | some i =>
    obtain ⟨b, hb⟩ := h.index_entry k i hk
    simp only [OMap.del, hk]
    by_cases hgk : g = k
    · subst hgk
      simp [get]
    · rw [if_neg hgk]
      have hkg : ¬k = g := fun e => hgk e.symm
      simp only [get, Std.HashMap.getElem?_erase, beq_iff_eq, hkg, ↓reduceIte]
      cases hg : m.index[g]? with
      | none => rfl
      | some j =>
        have hij : i ≠ j := by
          rintro rfl
          obtain ⟨c, hc⟩ := h.index_entry g i hg
          rw [hb] at hc
          cases hc
          exact hgk rfl
        simp only [Array.getElem?_setIfInBounds_ne hij]

/-- Deleting an absent key changes nothing. -/
theorem del_absent (h : WF m) {k : K} (hk : m.get k = none) : m.del k = m := by
  simp only [OMap.del, (h.get_eq_none k).mp hk]

/-- The listed keys are the present ones. -/
theorem mem_keys (h : WF m) (k : K) : (m.get k).isSome = true ↔ ∃ p : Nat, m.keys[p]? = some k := by
  have e : (∃ p : Nat, m.keys[p]? = some k) ↔ ∃ (a : α) (i : Nat), m.entries[i]? = some (some (k, a)) := by
    simp only [getElem?_keys]
    rw [← List.mem_iff_getElem?, mem_keysL]
    simp only [List.mem_iff_getElem?, Array.getElem?_toList]
  rw [e]
  constructor
  · intro hs
    cases hi : m.index[k]? with
    | none =>
      rw [(h.get_eq_none k).mpr hi] at hs
      simp at hs
    | some i =>
      obtain ⟨a, ha⟩ := h.index_entry k i hi
      exact ⟨a, i, ha⟩
  · rintro ⟨a, i, ha⟩
    obtain ⟨b, -, hg⟩ := h.get_of_index (h.entry_index i k a ha)
    simp [hg]

/-- Each key is listed once. -/
theorem keys_once (h : WF m) {k : K} {p q : Nat} (hp : m.keys[p]? = some k) (hq : m.keys[q]? = some k) :
    p = q := by
  rw [getElem?_keys] at hp hq
  exact keysL_once (fun i j a b hi hj => h.entry_unique (by rwa [Array.getElem?_toList] at hi)
    (by rwa [Array.getElem?_toList] at hj)) hp hq

/-- Putting a new key appends it to the keys. -/
theorem keys_put_new (h : WF m) {k : K} (x : α) (hk : m.get k = none) : (m.put k x).keys = m.keys.push k := by
  simp only [OMap.put, (h.get_eq_none k).mp hk, keys]
  apply Array.ext'
  simp

/-- Putting a present key keeps the keys. -/
theorem keys_put_old (h : WF m) {k : K} (x : α) (hk : (m.get k).isSome = true) : (m.put k x).keys = m.keys := by
  cases hi : m.index[k]? with
  | none =>
    rw [(h.get_eq_none k).mpr hi] at hk
    simp at hk
  | some i =>
    obtain ⟨b, hb⟩ := h.index_entry k i hi
    simp only [OMap.put, hi, keys]
    apply Array.ext'
    rw [Array.toList_filterMap, Array.toList_filterMap, Array.toList_setIfInBounds]
    exact keysL_set fun e he => by
      rw [Array.getElem?_toList, hb] at he
      cases he
      rfl

/-- Deleting a listed key removes it from the keys. -/
theorem keys_del (h : WF m) {k : K} {p : Nat} (hp : m.keys[p]? = some k) :
    (m.del k).keys = m.keys.eraseIdxIfInBounds p := by
  rw [getElem?_keys] at hp
  obtain ⟨i, a, hi, -⟩ := keysL_pos hp
  rw [Array.getElem?_toList] at hi
  simp only [OMap.del, h.entry_index i k a hi, keys]
  apply Array.ext'
  rw [Array.toList_filterMap, Array.toList_eraseIdxIfInBounds, Array.toList_filterMap, Array.toList_setIfInBounds]
  exact keysL_del (fun j b hj => h.entry_unique (by rwa [Array.getElem?_toList] at hj) hi) hp

end WF

end Engine.Model.OMap

namespace Engine.Model

instance : LawfulBEq (Array UInt16 ⊕ (Nat × Option (Array UInt16))) where
  rfl {a} := by
    cases a with
    | inl s => exact beq_self_eq_true s
    | inr s => exact beq_self_eq_true s
  eq_of_beq {a b} h := by
    cases a with
    | inl s =>
      cases b with
      | inl t => exact congrArg Sum.inl (eq_of_beq (a := s) (b := t) h)
      | inr t => cases h
    | inr s =>
      cases b with
      | inl t => cases h
      | inr t => exact congrArg Sum.inr (eq_of_beq (a := s) (b := t) h)

/-- A map in creation order whose index and entries agree: a Record's fields, an object's properties. -/
def WMap (K : Type) [BEq K] [Hashable K] (α : Type) : Type := { m : OMap K α // m.WF }

namespace WMap
variable {K α : Type} [BEq K] [Hashable K]

/-- The map's entries, in creation order (a removed one leaves `none`). -/
@[inline] def entries (m : WMap K α) : Array (Option (K × α)) := m.val.entries

/-- The positions of the map's keys. -/
@[inline] def index (m : WMap K α) : Std.HashMap K Nat := m.val.index

@[inline] def empty : WMap K α := ⟨OMap.empty, OMap.wf_empty⟩

@[inline] def get (m : WMap K α) (k : K) : Option α := m.val.get k

@[inline] def keys (m : WMap K α) : Array K := m.val.keys

variable [LawfulBEq K]

@[inline] def put (m : WMap K α) (k : K) (a : α) : WMap K α := ⟨m.val.put k a, m.property.put k a⟩

@[inline] def del (m : WMap K α) (k : K) : WMap K α := ⟨m.val.del k, m.property.del k⟩

end WMap

end Engine.Model
