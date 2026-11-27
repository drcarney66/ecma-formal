module

@[expose] public section

/-!
# Chunked non-moving heap (`ChunkedHeap`)

A store of cells indexed by monotonic `Nat` addresses that never reuses addresses:
- `next` is the next fresh address (`alloc` hands out `next` and increments `next` and `live`).
- `live` is the count of present cells (`alloc` increments it; `sweep` recomputes it after dropping
  unmarked slots and empty chunks).
- `chunks` partitions addresses into 4,096-slot chunks (`a / 4096` and `a % 4096`); an empty swept
  chunk is `none` (zero heap allocation).

Every law of `Ecma.Model.Laws` on `Heap` holds unconditionally for every `ChunkedHeap α` without a
well-formedness subtype, and `alloc`/`set` update uniquely-owned chunks in place.
-/

namespace Engine.Model

/-- Slots per chunk (`2^12 = 4096`). -/
abbrev chunkSize : Nat := 4096

/-- A non-moving chunked store with monotonic allocation counter `next` and live count `live`. -/
structure ChunkedHeap (α : Type) where
  next : Nat := 0
  live : Nat := 0
  chunks : Array (Option (Array (Option α))) := #[]

namespace ChunkedHeap

/-- The empty store. -/
def empty {α : Type} : ChunkedHeap α := ⟨0, 0, #[]⟩

instance {α : Type} : Inhabited (ChunkedHeap α) := ⟨empty⟩

/-- Read `(ci, oi)` from `chunks`. -/
@[inline] def rawGet {α : Type} (chunks : @& Array (Option (Array (Option α)))) (ci oi : Nat) : Option α :=
  match chunks[ci]?.join with
  | some c => c[oi]?.join
  | none => none

/-- Read address `a` where `a < h.next`. -/
@[inline] def get {α : Type} (h : @& ChunkedHeap α) (a : Nat) : Option α :=
  if a < h.next then rawGet h.chunks (a / chunkSize) (a % chunkSize) else none

/-- Write `val` at `oi` in chunk `c`, growing `c` when needed. -/
@[inline] def chunkPut {α : Type} (c : Array (Option α)) (oi : Nat) (val : Option α) : Array (Option α) :=
  if oi < c.size then c.setIfInBounds oi val
  else if oi == c.size then c.push val
  else (c ++ Array.replicate (oi - c.size) none).push val

/-- Write `val` at `(ci, oi)` in `chunks`, clearing `chunks[ci]` first so an existing chunk has
reference count 1 when `chunks` does. -/
@[inline] def rawPut {α : Type} (chunks : Array (Option (Array (Option α)))) (ci oi : Nat) (val : Option α) :
    Array (Option (Array (Option α))) :=
  if h : ci < chunks.size then
    let cur := chunks[ci]
    let chunks := chunks.setIfInBounds ci none
    let c := cur.getD (Array.mkEmpty chunkSize)
    chunks.setIfInBounds ci (some (chunkPut c oi val))
  else if ci == chunks.size then
    chunks.push (some (chunkPut (Array.mkEmpty chunkSize) oi val))
  else
    (chunks ++ Array.replicate (ci - chunks.size) none).push (some (chunkPut (Array.mkEmpty chunkSize) oi val))

/-- Allocate `v` at `h.next`. -/
@[inline] def alloc {α : Type} (h : ChunkedHeap α) (v : α) : Nat × ChunkedHeap α :=
  let ⟨next, live, chunks⟩ := h
  (next, ⟨next + 1, live + 1, rawPut chunks (next / chunkSize) (next % chunkSize) (some v)⟩)

/-- Push `v` at `h.next`, returning the updated heap. -/
@[inline] def push {α : Type} (h : ChunkedHeap α) (v : α) : ChunkedHeap α := (h.alloc v).2

/-- Push every element of `xs` in order. -/
def pushMany {α : Type} (h : ChunkedHeap α) (xs : Array α) : ChunkedHeap α :=
  xs.foldl ChunkedHeap.push h

/-- Replace the cell at `a` when present; leave `h` unchanged when `h.get a = none`. -/
@[inline] def set {α : Type} (h : ChunkedHeap α) (a : Nat) (v : α) : ChunkedHeap α :=
  if (h.get a).isNone then h
  else
    let ⟨next, live, chunks⟩ := h
    ⟨next, live, rawPut chunks (a / chunkSize) (a % chunkSize) (some v)⟩

/-- Fold `f` over all live cells below `h.next`, in ascending address order. -/
def foldLive {α β : Type} (f : β → Nat → α → β) (init : β) (h : @& ChunkedHeap α) : β := Id.run do
  let mut acc := init
  let numChunks := (h.next + chunkSize - 1) / chunkSize
  let lim := min numChunks h.chunks.size
  for ci in [0:lim] do
    if let some (some c) := h.chunks[ci]? then
      let base := ci * chunkSize
      let oLim := min c.size (h.next - base)
      for oi in [0:oLim] do
        if let some (some v) := c[oi]? then
          acc := f acc (base + oi) v
  return acc

/-- Sweep unmarked cells (`keep[a]? != some true`), freeing empty chunks and returning `(collected, h')`. -/
def sweep {α : Type} (keep : @& Array Bool) (h : ChunkedHeap α) : Nat × ChunkedHeap α := Id.run do
  let ⟨next, oldLive, chunks0⟩ := h
  let mut chunks := chunks0
  let mut newLive := 0
  for ci in [0:chunks.size] do
    if let some (some c0) := chunks[ci]? then
      chunks := chunks.setIfInBounds ci none
      let base := ci * chunkSize
      let mut c := c0
      let mut chunkLive := 0
      for oi in [0:c.size] do
        let addr := base + oi
        if addr < next then
          if let some (some _) := c[oi]? then
            if keep[addr]? == some true then
              chunkLive := chunkLive + 1
            else
              c := c.setIfInBounds oi none
        else
          c := c.setIfInBounds oi none
      if chunkLive > 0 then
        newLive := newLive + chunkLive
        chunks := chunks.setIfInBounds ci (some c)
  return (oldLive - newLive, ⟨next, newLive, chunks⟩)

/-! ## Algebraic laws -/

private theorem div_mod_eq {a b : Nat} : a / chunkSize = b / chunkSize ∧ a % chunkSize = b % chunkSize ↔ a = b := by
  unfold chunkSize; omega

private theorem setIfInBounds_push_end {β : Type} (xs : Array β) (x y : β) :
    (xs.push x).setIfInBounds xs.size y = xs.push y := by
  apply Array.ext_getElem?
  intro i
  rw [Array.getElem?_setIfInBounds, Array.getElem?_push, Array.getElem?_push]
  by_cases hi : i = xs.size
  · subst hi; simp
  · have hi' : xs.size ≠ i := Ne.symm hi
    simp [hi, hi']

private theorem setIfInBounds_setIfInBounds_self {β : Type} (xs : Array β) (i : Nat) (x y : β) :
    (xs.setIfInBounds i x).setIfInBounds i y = xs.setIfInBounds i y := by
  apply Array.ext_getElem?
  intro k
  simp only [Array.getElem?_setIfInBounds, Array.size_setIfInBounds]
  by_cases hk : i = k <;> simp [hk]

private theorem rawPut_of_lt {α : Type} (chunks : Array (Option (Array (Option α)))) {ci : Nat}
    (hlt : ci < chunks.size) (oi : Nat) (val : Option α) :
    rawPut chunks ci oi val =
      chunks.setIfInBounds ci (some (chunkPut ((chunks[ci]'hlt).getD (Array.mkEmpty chunkSize)) oi val)) := by
  unfold rawPut
  simp only [hlt, ↓reduceDIte, setIfInBounds_setIfInBounds_self]

theorem chunkPut_get_self {α : Type} (c : Array (Option α)) (oi : Nat) (val : Option α) :
    ((chunkPut c oi val)[oi]?).join = val := by
  unfold chunkPut
  split
  · simp [‹oi < c.size›]
  · split
    · rename_i h1 h2
      have heq : oi = c.size := beq_iff_eq.mp h2
      subst heq
      simp
    · rename_i h1 h2
      have hgt : c.size < oi := by simp at h2; omega
      have hsz : (c ++ Array.replicate (oi - c.size) (none : Option α)).size = oi := by simp; omega
      rw [Array.getElem?_push]
      simp [hsz]

theorem chunkPut_get_other {α : Type} (c : Array (Option α)) (oi oi' : Nat) (val : Option α) (hne : oi' ≠ oi) :
    ((chunkPut c oi val)[oi']?).join = (c[oi']?).join := by
  unfold chunkPut
  split
  · rw [Array.getElem?_setIfInBounds]
    simp [Ne.symm hne]
  · split
    · rename_i h1 h2
      have heq : oi = c.size := beq_iff_eq.mp h2
      subst heq
      rw [Array.getElem?_push]
      simp [hne]
    · rename_i h1 h2
      have hgt : c.size < oi := by simp at h2; omega
      have hsz : (c ++ Array.replicate (oi - c.size) (none : Option α)).size = oi := by simp; omega
      rw [Array.getElem?_push]
      simp only [hsz, hne, ↓reduceIte, Array.getElem?_append]
      split
      · rfl
      · rename_i hge
        have hcnone : c[oi']? = none := Array.getElem?_eq_none (by omega)
        rw [hcnone, Array.getElem?_replicate]
        split <;> rfl

private theorem rawPut_join {α : Type} (chunks : Array (Option (Array (Option α)))) (ci oi k : Nat) (val : Option α) :
    (rawPut chunks ci oi val)[k]?.join =
      if ci = k then some (chunkPut ((chunks[ci]?.join).getD (Array.mkEmpty chunkSize)) oi val)
      else chunks[k]?.join := by
  by_cases hlt : ci < chunks.size
  · rw [rawPut_of_lt chunks hlt, Array.getElem?_setIfInBounds, Array.getElem?_eq_getElem hlt]
    by_cases hk : ci = k
    · subst hk; simp [hlt]
    · simp [hk]
  · unfold rawPut
    simp only [hlt, ↓reduceDIte]
    have hnone : chunks[ci]? = none := Array.getElem?_eq_none (by omega)
    rw [hnone]
    split
    · rename_i heq
      have hce : ci = chunks.size := beq_iff_eq.mp heq
      subst hce
      rw [Array.getElem?_push]
      by_cases hk : chunks.size = k
      · subst hk; simp
      · have hk' : k ≠ chunks.size := Ne.symm hk
        simp [hk, hk']
    · rename_i hne_sz
      have hgt : chunks.size < ci := by simp at hne_sz; omega
      have hsz : (chunks ++ Array.replicate (ci - chunks.size) (none : Option (Array (Option α)))).size = ci := by
        simp; omega
      rw [Array.getElem?_push]
      by_cases hk : ci = k
      · subst hk; simp [hsz]
      · have hk' : k ≠ ci := Ne.symm hk
        simp only [hsz, hk, hk', ↓reduceIte, Array.getElem?_append]
        split
        · rfl
        · rename_i hge
          have hknone : chunks[k]? = none := Array.getElem?_eq_none (by omega)
          rw [hknone, Array.getElem?_replicate]
          split <;> rfl

theorem rawGet_rawPut_self {α : Type} (chunks : Array (Option (Array (Option α)))) (ci oi : Nat) (val : Option α) :
    rawGet (rawPut chunks ci oi val) ci oi = val := by
  simp [rawGet, rawPut_join, chunkPut_get_self]

theorem rawGet_rawPut_other {α : Type} (chunks : Array (Option (Array (Option α)))) (ci oi ci' oi' : Nat)
    (val : Option α) (hne : ¬(ci' = ci ∧ oi' = oi)) :
    rawGet (rawPut chunks ci oi val) ci' oi' = rawGet chunks ci' oi' := by
  simp only [rawGet, rawPut_join]
  by_cases hci : ci = ci'
  · subst hci
    have hoi : oi' ≠ oi := fun h => hne ⟨rfl, h⟩
    simp only [↓reduceIte]
    cases hc : chunks[ci]?.join with
    | some c => simp [chunkPut_get_other c oi oi' val hoi]
    | none => simp [chunkPut_get_other #[] oi oi' val hoi]
  · simp [hci]

theorem get_empty {α : Type} (a : Nat) : (empty : ChunkedHeap α).get a = none := by
  simp [empty, get]

@[simp] theorem alloc_fst {α : Type} (h : ChunkedHeap α) (v : α) : (h.alloc v).1 = h.next := rfl

@[simp] theorem push_next {α : Type} (h : ChunkedHeap α) (v : α) : (h.push v).next = h.next + 1 := rfl

@[simp] theorem set_next {α : Type} (h : ChunkedHeap α) (a : Nat) (v : α) : (h.set a v).next = h.next := by
  unfold set; split <;> rfl

theorem get_lt_next {α : Type} {h : ChunkedHeap α} {a : Nat} {v : α} (hg : h.get a = some v) : a < h.next := by
  unfold get at hg
  split at hg
  · assumption
  · cases hg

theorem get_isSome_lt_next {α : Type} {h : ChunkedHeap α} {a : Nat} (hg : (h.get a).isSome = true) : a < h.next := by
  cases he : h.get a with
  | none => rw [he] at hg; cases hg
  | some v => exact get_lt_next he

private theorem set_of_isNone_false {α : Type} (h : ChunkedHeap α) (a : Nat) (v : α)
    (hno : (h.get a).isNone = false) :
    h.set a v = ⟨h.next, h.live, rawPut h.chunks (a / chunkSize) (a % chunkSize) (some v)⟩ := by
  unfold set
  rw [hno]
  rcases h with ⟨next, live, chunks⟩
  rfl

private theorem set_of_isSome {α : Type} (h : ChunkedHeap α) (a : Nat) (v : α)
    (hs : (h.get a).isSome = true) :
    h.set a v = ⟨h.next, h.live, rawPut h.chunks (a / chunkSize) (a % chunkSize) (some v)⟩ := by
  have hno : (h.get a).isNone = false := by cases he : h.get a <;> simp_all
  exact set_of_isNone_false h a v hno

theorem alloc_fresh {α : Type} (h : ChunkedHeap α) (v : α) : h.get (h.alloc v).1 = none := by
  simp [get]

theorem alloc_get_self {α : Type} (h : ChunkedHeap α) (v : α) : (h.alloc v).2.get (h.alloc v).1 = some v := by
  rcases h with ⟨next, live, chunks⟩
  simp [alloc, get, rawGet_rawPut_self]

theorem alloc_get_other {α : Type} (h : ChunkedHeap α) (v : α) (a : Nat) (ha : a ≠ (h.alloc v).1) :
    (h.alloc v).2.get a = h.get a := by
  rcases h with ⟨next, live, chunks⟩
  have ha' : a ≠ next := ha
  simp only [alloc, get]
  by_cases hlt : a < next
  · have hlt' : a < next + 1 := by omega
    have hne : ¬(a / chunkSize = next / chunkSize ∧ a % chunkSize = next % chunkSize) :=
      fun h => ha' (div_mod_eq.mp h)
    simp [hlt, hlt', rawGet_rawPut_other chunks _ _ _ _ _ hne]
  · have hlt' : ¬(a < next + 1) := by omega
    simp [hlt, hlt']

theorem set_none {α : Type} (h : ChunkedHeap α) (a : Nat) (v : α) (hn : h.get a = none) : h.set a v = h := by
  simp [set, hn]

theorem get_set_self {α : Type} (h : ChunkedHeap α) (a : Nat) (v : α) (hs : (h.get a).isSome = true) :
    (h.set a v).get a = some v := by
  have hlt : a < h.next := get_isSome_lt_next hs
  rw [set_of_isSome h a v hs]
  simp [get, hlt, rawGet_rawPut_self]

theorem get_set_other {α : Type} (h : ChunkedHeap α) (a : Nat) (v : α) (b : Nat) (hb : b ≠ a) :
    (h.set a v).get b = h.get b := by
  cases he : h.get a with
  | none => rw [set_none h a v he]
  | some _ =>
    have hs : (h.get a).isSome = true := by rw [he]; rfl
    rw [set_of_isSome h a v hs]
    simp only [get]
    split
    · have hne : ¬(b / chunkSize = a / chunkSize ∧ b % chunkSize = a % chunkSize) :=
        fun h => hb (div_mod_eq.mp h)
      exact rawGet_rawPut_other h.chunks _ _ _ _ _ hne
    · rfl

/-! ## Strict equality lemmas for in-place updates and batch scans -/

theorem chunkPut_chunkPut_self {α : Type} (c : Array (Option α)) (oi : Nat) (v₁ v₂ : Option α) :
    chunkPut (chunkPut c oi v₁) oi v₂ = chunkPut c oi v₂ := by
  unfold chunkPut
  split
  · rename_i hlt
    have hlt' : oi < (c.setIfInBounds oi v₁).size := by simp [hlt]
    simp only [hlt', ↓reduceIte, setIfInBounds_setIfInBounds_self]
  · split
    · rename_i h1 h2
      have heq : oi = c.size := beq_iff_eq.mp h2
      subst heq
      have hlt' : c.size < (c.push v₁).size := by simp
      simp only [hlt', ↓reduceIte, setIfInBounds_push_end]
    · rename_i h1 h2
      have hgt : c.size < oi := by simp at h2; omega
      generalize hp_eq : c ++ Array.replicate (oi - c.size) (none : Option α) = p
      have hp : p.size = oi := by subst hp_eq; simp; omega
      have hlt' : oi < (p.push v₁).size := by simp [hp]
      simp only [hlt', ↓reduceIte]
      simpa [hp] using setIfInBounds_push_end p v₁ v₂

theorem rawPut_rawPut_self {α : Type} (chunks : Array (Option (Array (Option α)))) (ci oi : Nat) (v₁ v₂ : Option α) :
    rawPut (rawPut chunks ci oi v₁) ci oi v₂ = rawPut chunks ci oi v₂ := by
  by_cases hlt : ci < chunks.size
  · rw [rawPut_of_lt chunks hlt, rawPut_of_lt chunks hlt]
    let c₀ := (chunks[ci]'hlt).getD (Array.mkEmpty chunkSize)
    have hlt2 : ci < (chunks.setIfInBounds ci (some (chunkPut c₀ oi v₁))).size := by simp [hlt]
    rw [rawPut_of_lt _ hlt2]
    have hget : (chunks.setIfInBounds ci (some (chunkPut c₀ oi v₁)))[ci]'hlt2 = some (chunkPut c₀ oi v₁) := by
      have : (chunks.setIfInBounds ci (some (chunkPut c₀ oi v₁)))[ci]? = some (some (chunkPut c₀ oi v₁)) := by
        simp [hlt]
      exact Option.some.inj ((Array.getElem?_eq_getElem hlt2).symm.trans this)
    simp only [hget, Option.getD_some, chunkPut_chunkPut_self, setIfInBounds_setIfInBounds_self]
    rfl
  · unfold rawPut
    simp only [hlt, ↓reduceDIte]
    split
    · rename_i heq
      have hce : ci = chunks.size := beq_iff_eq.mp heq
      subst hce
      let c₁ := chunkPut (Array.mkEmpty chunkSize) oi v₁
      have hlt2 : chunks.size < (chunks.push (some c₁)).size := by simp
      have hget : (chunks.push (some c₁))[chunks.size]'hlt2 = some c₁ := by simp
      simp only [c₁, hlt2, ↓reduceDIte, hget, Option.getD_some, chunkPut_chunkPut_self,
        setIfInBounds_push_end]
    · rename_i hne_sz
      have hgt : chunks.size < ci := by simp at hne_sz; omega
      generalize hp_eq : chunks ++ Array.replicate (ci - chunks.size) (none : Option (Array (Option α))) = p
      have hp : p.size = ci := by subst hp_eq; simp; omega
      let c₁ := chunkPut (Array.mkEmpty chunkSize) oi v₁
      have hlt2 : ci < (p.push (some c₁)).size := by simp [hp]
      have hget : (p.push (some c₁))[ci]'hlt2 = some c₁ := by simp [← hp]
      simp only [c₁, hlt2, ↓reduceDIte, hget, Option.getD_some, chunkPut_chunkPut_self,
        setIfInBounds_setIfInBounds_self]
      rw [← hp]
      exact setIfInBounds_push_end p _ _

theorem set_set_self {α : Type} (h : ChunkedHeap α) (a : Nat) (v₁ v₂ : α) (hs : (h.get a).isSome = true) :
    (h.set a v₁).set a v₂ = h.set a v₂ := by
  have hs2 : ((h.set a v₁).get a).isSome = true := by rw [get_set_self h a v₁ hs]; rfl
  rw [set_of_isSome (h.set a v₁) a v₂ hs2, set_of_isSome h a v₁ hs, set_of_isSome h a v₂ hs]
  simp [rawPut_rawPut_self]

theorem set_push_self {α : Type} (h : ChunkedHeap α) (c d : α) :
    (h.push c).set h.next d = h.push d := by
  have hs : ((h.push c).get h.next).isSome = true := by
    have hg : (h.push c).get h.next = some c := alloc_get_self h c
    rw [hg]; rfl
  rw [set_of_isSome (h.push c) h.next d hs]
  rcases h with ⟨next, live, chunks⟩
  simp [push, alloc, rawPut_rawPut_self]

private theorem rawGet_some_bounds {α : Type} {chunks : Array (Option (Array (Option α)))} {ci oi : Nat} {v : α}
    (hg : rawGet chunks ci oi = some v) :
    ∃ (hlt : ci < chunks.size) (c : Array (Option α)), chunks[ci]'hlt = some c ∧ oi < c.size := by
  unfold rawGet at hg
  cases h1 : chunks[ci]? with
  | none => rw [h1] at hg; cases hg
  | some oc =>
    rw [h1] at hg
    obtain ⟨hlt, hci⟩ := Array.getElem?_eq_some_iff.mp h1
    cases oc with
    | none => cases hg
    | some c =>
      simp only [Option.join, Option.bind_some, id_eq] at hg
      cases h2 : c[oi]? with
      | none => rw [h2] at hg; cases hg
      | some ov =>
        obtain ⟨holt, _⟩ := Array.getElem?_eq_some_iff.mp h2
        exact ⟨hlt, c, hci, holt⟩

private theorem chunkPut_set_comm {α : Type} (c : Array (Option α)) {oi₁ oi₂ : Nat} (hol : oi₁ < c.size)
    (hne : oi₁ ≠ oi₂) (v₁ v₂ : Option α) :
    (chunkPut c oi₂ v₂).setIfInBounds oi₁ v₁ = chunkPut (c.setIfInBounds oi₁ v₁) oi₂ v₂ := by
  unfold chunkPut
  have hsz : (c.setIfInBounds oi₁ v₁).size = c.size := by simp
  by_cases h2 : oi₂ < c.size
  · have h2' : oi₂ < (c.setIfInBounds oi₁ v₁).size := by omega
    simp only [h2, h2', ↓reduceIte]
    apply Array.ext_getElem?
    intro k
    simp only [Array.getElem?_setIfInBounds, Array.size_setIfInBounds]
    by_cases hk1 : oi₁ = k
    · subst hk1; simp [Ne.symm hne, hol]
    · by_cases hk2 : oi₂ = k
      · subst hk2; simp [hk1, h2]
      · simp [hk1, hk2]
  · simp only [h2, hsz, ↓reduceIte]
    split
    · apply Array.ext_getElem?
      intro k
      simp only [Array.getElem?_setIfInBounds, Array.getElem?_push, Array.size_push, Array.size_setIfInBounds]
      by_cases hk1 : oi₁ = k
      · subst hk1
        have hlt_p : oi₁ < c.size + 1 := by omega
        have hk_ne' : oi₁ ≠ c.size := by omega
        simp [hlt_p, hol, hk_ne']
      · simp [hk1]
    · apply Array.ext_getElem?
      intro k
      simp only [Array.getElem?_setIfInBounds, Array.getElem?_push, Array.getElem?_append,
        Array.size_push, Array.size_append, Array.size_setIfInBounds, Array.size_replicate]
      by_cases hk1 : oi₁ = k
      · subst hk1
        have hgt2 : c.size < oi₂ := by rename_i h3; simp at h3; omega
        have hlt_p : oi₁ < c.size + (oi₂ - c.size) + 1 := by omega
        have hk_ne' : oi₁ ≠ c.size + (oi₂ - c.size) := by omega
        simp [hlt_p, hol, hk_ne']
      · simp [hk1]

private theorem rawPut_comm_of_some {α : Type} (chunks : Array (Option (Array (Option α))))
    {ci₁ oi₁ ci₂ oi₂ : Nat} {c : Array (Option α)} (hci : ci₁ < chunks.size)
    (hc_eq : chunks[ci₁]'hci = some c) (hoi : oi₁ < c.size) (hne : ¬(ci₁ = ci₂ ∧ oi₁ = oi₂))
    (v r : α) :
    rawPut (rawPut chunks ci₂ oi₂ (some r)) ci₁ oi₁ (some v) =
      rawPut (rawPut chunks ci₁ oi₁ (some v)) ci₂ oi₂ (some r) := by
  rw [rawPut_of_lt chunks hci, hc_eq, Option.getD_some]
  by_cases hsame : ci₁ = ci₂
  · have hoi_ne : oi₁ ≠ oi₂ := fun ho => hne ⟨hsame, ho⟩
    subst hsame
    rw [rawPut_of_lt chunks hci, hc_eq, Option.getD_some]
    have hci_s1 : ci₁ < (chunks.setIfInBounds ci₁ (some (chunkPut c oi₂ (some r)))).size := by simp [hci]
    have hci_s2 : ci₁ < (chunks.setIfInBounds ci₁ (some (chunkPut c oi₁ (some v)))).size := by simp [hci]
    rw [rawPut_of_lt _ hci_s1, rawPut_of_lt _ hci_s2]
    have hg1 : (chunks.setIfInBounds ci₁ (some (chunkPut c oi₂ (some r))))[ci₁]'hci_s1 =
        some (chunkPut c oi₂ (some r)) := by
      have : (chunks.setIfInBounds ci₁ (some (chunkPut c oi₂ (some r))))[ci₁]? =
          some (some (chunkPut c oi₂ (some r))) := by simp [hci]
      exact Option.some.inj ((Array.getElem?_eq_getElem hci_s1).symm.trans this)
    have hg2 : (chunks.setIfInBounds ci₁ (some (chunkPut c oi₁ (some v))))[ci₁]'hci_s2 =
        some (chunkPut c oi₁ (some v)) := by
      have : (chunks.setIfInBounds ci₁ (some (chunkPut c oi₁ (some v))))[ci₁]? =
          some (some (chunkPut c oi₁ (some v))) := by simp [hci]
      exact Option.some.inj ((Array.getElem?_eq_getElem hci_s2).symm.trans this)
    rw [hg1, hg2]
    dsimp only [Option.getD]
    have hc_eq2 : chunkPut (chunkPut c oi₂ (some r)) oi₁ (some v) = chunkPut (chunkPut c oi₁ (some v)) oi₂ (some r) := by
      let cr := chunkPut c oi₂ (some r)
      have hoi_lt2 : oi₁ < cr.size := by
        dsimp only [cr]; unfold chunkPut
        split
        · simp [hoi]
        · split <;> (simp; omega)
      have lhs : chunkPut cr oi₁ (some v) = cr.setIfInBounds oi₁ (some v) := by
        unfold chunkPut
        simp only [hoi_lt2, ↓reduceIte]
      have rhs : chunkPut (chunkPut c oi₁ (some v)) oi₂ (some r) = chunkPut (c.setIfInBounds oi₁ (some v)) oi₂ (some r) := by
        congr 1
        unfold chunkPut
        simp only [hoi, ↓reduceIte]
      rw [show chunkPut (chunkPut c oi₂ (some r)) oi₁ (some v) = chunkPut cr oi₁ (some v) from rfl, lhs, rhs]
      exact chunkPut_set_comm c hoi hoi_ne (some v) (some r)
    rw [hc_eq2, setIfInBounds_setIfInBounds_self, setIfInBounds_setIfInBounds_self]
  · let c' := chunkPut c oi₁ (some v)
    let chunks' := chunks.setIfInBounds ci₁ (some c')
    have hsz' : chunks'.size = chunks.size := by simp [chunks']
    have hlt_ci1 : ci₁ < (rawPut chunks ci₂ oi₂ (some r)).size := by
      unfold rawPut
      split
      · simp [hci]
      · split <;> (simp; omega)
    have hget_ci1 : (rawPut chunks ci₂ oi₂ (some r))[ci₁]'hlt_ci1 = some c := by
      have : (rawPut chunks ci₂ oi₂ (some r))[ci₁]? = some (some c) := by
        by_cases hci2 : ci₂ < chunks.size
        · rw [rawPut_of_lt chunks hci2, Array.getElem?_setIfInBounds]
          simp [Ne.symm hsame, Array.getElem?_eq_getElem hci, hc_eq]
        · unfold rawPut
          simp only [hci2, ↓reduceDIte]
          split
          · rename_i heq
            have hce : ci₂ = chunks.size := beq_iff_eq.mp heq
            rw [Array.getElem?_push]
            have hne2 : ci₁ ≠ chunks.size := by omega
            simp [hne2, Array.getElem?_eq_getElem hci, hc_eq]
          · rename_i hne_sz
            have hgt2 : chunks.size < ci₂ := by simp at hne_sz; omega
            have hsz_p : (chunks ++ Array.replicate (ci₂ - chunks.size) (none : Option (Array (Option α)))).size = ci₂ := by
              simp; omega
            rw [Array.getElem?_push]
            simp [hsz_p, hsame, Array.getElem?_append, hci, hc_eq]
      exact Option.some.inj ((Array.getElem?_eq_getElem hlt_ci1).symm.trans this)
    rw [rawPut_of_lt _ hlt_ci1, hget_ci1, Option.getD_some]
    change (rawPut chunks ci₂ oi₂ (some r)).setIfInBounds ci₁ (some c') = rawPut chunks' ci₂ oi₂ (some r)
    by_cases hci2 : ci₂ < chunks.size
    · have hci2' : ci₂ < chunks'.size := by rw [hsz']; exact hci2
      have hget2 : chunks'[ci₂]'hci2' = chunks[ci₂]'hci2 := by
        have : chunks'[ci₂]? = chunks[ci₂]? := by simp [chunks', hsame]
        exact Option.some.inj ((Array.getElem?_eq_getElem hci2').symm.trans (this.trans (Array.getElem?_eq_getElem hci2)))
      rw [rawPut_of_lt chunks hci2, rawPut_of_lt chunks' hci2', hget2]
      apply Array.ext_getElem?
      intro k
      simp only [Array.getElem?_setIfInBounds, Array.size_setIfInBounds, chunks', hsz']
      by_cases hk1 : ci₁ = k
      · subst hk1; simp [Ne.symm hsame, hci]
      · by_cases hk2 : ci₂ = k
        · subst hk2; simp [hk1, hci2]
        · simp [hk1, hk2]
    · by_cases heq2 : ci₂ == chunks.size
      · have hce : ci₂ = chunks.size := beq_iff_eq.mp heq2
        subst hce
        unfold rawPut
        simp only [hci2, hsz', beq_self_eq_true, ↓reduceDIte, ↓reduceIte]
        apply Array.ext_getElem?
        intro k
        rw [Array.getElem?_setIfInBounds, Array.getElem?_push, Array.getElem?_push]
        simp only [Array.size_push, hsz', chunks', Array.getElem?_setIfInBounds]
        by_cases hk1 : ci₁ = k
        · subst hk1
          have hlt1 : ci₁ < chunks.size + 1 := by omega
          have hne1 : ci₁ ≠ chunks.size := by omega
          simp [hlt1, hci, hne1]
        · simp [hk1]
      · have hgt2 : chunks.size < ci₂ := by simp at heq2; omega
        unfold rawPut
        simp only [hci2, hsz', heq2, Bool.false_eq_true, ↓reduceDIte, ↓reduceIte]
        generalize hp1 : chunks ++ Array.replicate (ci₂ - chunks.size) (none : Option (Array (Option α))) = p₁
        generalize hp2 : chunks' ++ Array.replicate (ci₂ - chunks.size) (none : Option (Array (Option α))) = p₂
        have hp1_sz : p₁.size = ci₂ := by subst hp1; simp; omega
        have hp2_sz : p₂.size = ci₂ := by subst hp2; simp [hsz']; omega
        apply Array.ext_getElem?
        intro k
        rw [Array.getElem?_setIfInBounds, Array.getElem?_push, Array.getElem?_push]
        simp only [Array.size_push, hp1_sz, hp2_sz]
        by_cases hk1 : ci₁ = k
        · subst hk1
          have hlt1 : ci₁ < ci₂ + 1 := by omega
          have hne1 : ci₁ ≠ ci₂ := by omega
          simp only [↓reduceIte, hlt1, hne1]
          subst hp2
          simp [Array.getElem?_append, chunks', hsz', hci]
        · simp only [hk1, ↓reduceIte]
          by_cases hk2 : k = ci₂
          · subst hk2; simp
          · simp only [hk2, ↓reduceIte]
            subst hp1 hp2
            simp [Array.getElem?_append, chunks', hsz', hk1]

theorem set_push_other {α : Type} (h : ChunkedHeap α) (a : Nat) (v r : α) (hs : (h.get a).isSome = true) :
    (h.push r).set a v = (h.set a v).push r := by
  obtain ⟨w, hw⟩ := Option.isSome_iff_exists.mp hs
  have ha_lt : a < h.next := get_lt_next hw
  have hne : a ≠ h.next := by omega
  have hs2 : ((h.push r).get a).isSome = true := by
    rw [show (h.push r).get a = h.get a from alloc_get_other h r a hne, hw]; rfl
  rw [set_of_isSome (h.push r) a v hs2, set_of_isSome h a v hs]
  rcases h with ⟨next, live, chunks⟩
  have hraw : rawGet chunks (a / chunkSize) (a % chunkSize) = some w := by
    simpa [get, ha_lt] using hw
  obtain ⟨hci, c, hc_eq, hoi⟩ := rawGet_some_bounds hraw
  have hne_pair : ¬(a / chunkSize = next / chunkSize ∧ a % chunkSize = next % chunkSize) :=
    fun hp => hne (div_mod_eq.mp hp)
  simp only [push, alloc, ChunkedHeap.mk.injEq, true_and]
  exact rawPut_comm_of_some chunks hci hc_eq hoi hne_pair v r

@[simp] theorem pushMany_empty {α : Type} (h : ChunkedHeap α) : h.pushMany #[] = h := rfl

theorem pushMany_push {α : Type} (h : ChunkedHeap α) (xs : Array α) (x : α) :
    h.pushMany (xs.push x) = (h.pushMany xs).push x := Array.foldl_push

theorem pushMany_next {α : Type} (h : ChunkedHeap α) (xs : Array α) :
    (h.pushMany xs).next = h.next + xs.size := by
  unfold pushMany
  rw [← Array.foldl_toList, ← Array.length_toList]
  induction xs.toList generalizing h with
  | nil => simp
  | cons x l ih =>
    simp only [List.foldl_cons, List.length_cons]
    rw [ih (h.push x), push_next]
    omega

theorem pushMany_keeps {α : Type} (h : ChunkedHeap α) (xs : Array α) {a : Nat} {v : α}
    (hg : h.get a = some v) : (h.pushMany xs).get a = some v := by
  unfold pushMany
  rw [← Array.foldl_toList]
  induction xs.toList generalizing h with
  | nil => exact hg
  | cons x l ih =>
    simp only [List.foldl_cons]
    refine ih (h.push x) ?_
    have hlt := get_lt_next hg
    have hne : a ≠ (h.alloc x).1 := by simp only [alloc_fst]; omega
    rw [show (h.push x).get a = h.get a from alloc_get_other h x a hne]
    exact hg

theorem set_pushMany_other {α : Type} (h : ChunkedHeap α) (xs : Array α) (a : Nat) (v : α)
    (hs : (h.get a).isSome = true) :
    (h.pushMany xs).set a v = (h.set a v).pushMany xs := by
  unfold pushMany
  rw [← Array.foldl_toList, ← Array.foldl_toList]
  induction xs.toList generalizing h with
  | nil => rfl
  | cons x l ih =>
    simp only [List.foldl_cons]
    have hs' : ((h.push x).get a).isSome = true := by
      obtain ⟨w, hw⟩ := Option.isSome_iff_exists.mp hs
      have hlt := get_lt_next hw
      have hne : a ≠ (h.alloc x).1 := by simp only [alloc_fst]; omega
      rw [show (h.push x).get a = h.get a from alloc_get_other h x a hne, hw]; rfl
    rw [ih (h.push x) hs', set_push_other h a v x hs]

end ChunkedHeap

end Engine.Model
