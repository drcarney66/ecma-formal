module

public import Ecma.Host.Laws
public import Engine.Host.Strategy

@[expose] public section

/-!
# SortStep's strategy meets its laws

`sortStepBy_law`: at the state and result a sort reaches, `sortStepBy`'s answer is a call on two indices less
than _n_, or a permutation that meets every consistent comparator's conditions given the calls made;
`sortStepBy_ends`: a sort by it makes finitely many calls. The binary insertion sort's facts: its state is a
search for `x`'s place among the indices below it (`BinSort.Ok`), and under a consistent comparator's order those
indices are sorted and the search's range brackets the place (`BinSort.Sorted`).
-/

namespace Ecma

variable {M : Model}

/-- An order on the indices less than `n` meets a consistent comparator's requirements (§23.1.3.30.1). -/
structure OrdOk (n : Nat) (O : Nat → Nat → Ordering) : Prop where
  refl : ∀ a, a < n → O a a = .eq
  symm : ∀ a b, a < n → b < n → O a b = .eq → O b a = .eq
  trans : ∀ p a b d, a < n → b < n → d < n → O a b = p → O b d = p → O a d = p

/-- `a` may stand before `b`: `b` is not less than `a`, and if they are equal, `a` came first. -/
def SortR (O : Nat → Nat → Ordering) (a b : Nat) : Prop := O b a ≠ .lt ∧ (O b a = .eq → a < b)

theorem OrdOk.swap_lt {n O} (H : OrdOk n O) {a b} (ha : a < n) (hb : b < n) (h : O a b = .lt) :
    O b a = .gt := by
  cases hba : O b a
  · have := H.trans .lt a b a ha hb ha h hba; rw [H.refl a ha] at this; cases this
  · rw [H.symm b a hb ha hba] at h; cases h
  · rfl

theorem OrdOk.swap_gt {n O} (H : OrdOk n O) {a b} (ha : a < n) (hb : b < n) (h : O a b = .gt) :
    O b a = .lt := by
  cases hba : O b a
  · rfl
  · rw [H.symm b a hb ha hba] at h; cases h
  · have := H.trans .gt a b a ha hb ha h hba; rw [H.refl a ha] at this; cases this

theorem OrdOk.lt_eq {n O} (H : OrdOk n O) {a b d} (ha : a < n) (hb : b < n) (hd : d < n)
    (h1 : O a b = .lt) (h2 : O b d = .eq) : O a d = .lt := by
  cases had : O a d
  · rfl
  · have := H.trans .eq b d a hb hd ha h2 (H.symm a d ha hd had)
    rw [H.symm b a hb ha this] at h1; cases h1
  · have hda := H.swap_gt ha hd had
    have := H.trans .lt d a b hd ha hb hda h1
    rw [H.symm b d hb hd h2] at this; cases this

/-- Where `x` goes before `y`, it goes before every element `y` may stand before. -/
theorem OrdOk.lt_R {n O} (H : OrdOk n O) {x y a} (hx : x < n) (hy : y < n) (ha : a < n)
    (h : O x y = .lt) (hr : SortR O y a) : O x a = .lt := by
  cases hay : O a y
  · exact absurd hay hr.1
  · exact H.lt_eq hx hy ha h (H.symm a y ha hy hay)
  · exact H.trans .lt x y a hx hy ha h (H.swap_gt ha hy hay)

theorem pairwise_idxOf {R : Nat → Nat → Prop} : ∀ {l : List Nat} {j k}, l.Pairwise R → j ∈ l → k ∈ l → j ≠ k →
    l.idxOf j < l.idxOf k ∨ R k j
  | [], _, _, _, hj, _, _ => by simp at hj
  | x :: xs, j, k, hp, hj, hk, hne => by
    have hp' := List.pairwise_cons.1 hp
    by_cases hxj : x = j
    · subst hxj; left
      have : (x == k) = false := by simpa using hne
      simp [List.idxOf_cons, this]
    by_cases hxk : x = k
    · subst hxk; right
      exact hp'.1 j ((List.mem_cons.1 hj).resolve_left (Ne.symm hxj))
    · have hj' := (List.mem_cons.1 hj).resolve_left (Ne.symm hxj)
      have hk' := (List.mem_cons.1 hk).resolve_left (Ne.symm hxk)
      rcases pairwise_idxOf hp'.2 hj' hk' hne with h | h
      · left
        have e1 : (x == j) = false := by simpa using hxj
        have e2 : (x == k) = false := by simpa using hxk
        simp [List.idxOf_cons, e1, e2, h]
      · exact .inr h

/-- An order sorted by a consistent comparator's order meets the conditions (§23.1.3.30.1). -/
theorem sorted_ok {n : Nat} {O : Nat → Nat → Ordering} {σ : List Nat} (H : OrdOk n O) (hperm : σ.Perm (List.range n)) (hs : σ.Pairwise (SortR O)) :
    ∀ j k, j < n → k < n →
      (O j k = .lt → σ.idxOf j < σ.idxOf k) ∧ (j < k → O j k = .eq → σ.idxOf j < σ.idxOf k) := by
  refine fun j k hj hk => ⟨fun hlt => ?_, fun hjk heq => ?_⟩
  · have hne : j ≠ k := by rintro rfl; rw [H.refl j hj] at hlt; cases hlt
    rcases pairwise_idxOf (j := j) (k := k) hs (hperm.mem_iff.2 (by simpa)) (hperm.mem_iff.2 (by simpa)) hne with h | h
    · exact h
    · exact absurd hlt h.1
  · rcases pairwise_idxOf (j := j) (k := k) hs (hperm.mem_iff.2 (by simpa)) (hperm.mem_iff.2 (by simpa)) (by omega) with h | h
    · exact h
    · have := h.2 heq; omega

/-! The binary insertion sort's states. -/

/-- A state of a sort of `n` elements mid-search: `x` below `n`, `xs` the indices below `x`, the range a
non-empty part of `xs`. -/
structure BinSort.Ok (n : Nat) (b : BinSort) : Prop where
  x_lt : b.x < n
  perm : b.xs.Perm (List.range b.x)
  lo_lt : b.lo < b.hi
  hi_le : b.hi ≤ b.xs.length

/-- `BinSort.Ok` but for a range that may be empty: a state `settle` is given. -/
structure BinSort.Pre (n : Nat) (b : BinSort) : Prop where
  x_lt : b.x < n
  perm : b.xs.Perm (List.range b.x)
  lo_le : b.lo ≤ b.hi
  hi_le : b.hi ≤ b.xs.length

/-- The search's facts under an order `O`: `xs` sorted (`SortR`), `x` not less than the elements before `lo`, and
less than those from `hi`. -/
def BinSort.Sorted (O : Nat → Nat → Ordering) (b : BinSort) : Prop :=
  b.xs.Pairwise (SortR O) ∧ (∀ a ∈ b.xs.take b.lo, O b.x a ≠ .lt) ∧ ∀ a ∈ b.xs.drop b.hi, O b.x a = .lt

theorem BinSort.Pre.mem_lt {n b} (h : BinSort.Pre n b) {a} (ha : a ∈ b.xs) : a < b.x := by
  simpa using h.perm.mem_iff.1 ha

theorem BinSort.Ok.pre {n b} (h : BinSort.Ok n b) : BinSort.Pre n b :=
  ⟨h.x_lt, h.perm, Nat.le_of_lt h.lo_lt, h.hi_le⟩

theorem BinSort.mid_lt {b : BinSort} (h : b.lo < b.hi) : b.lo ≤ b.mid ∧ b.mid < b.hi := by
  unfold BinSort.mid; omega

/-- The range narrowed by the order of `x` and the middle element. -/
abbrev BinSort.narrow (b : BinSort) (o : Ordering) : BinSort :=
  if o = .lt then { b with hi := b.mid } else { b with lo := b.mid + 1 }

theorem BinSort.step_eq (n : Nat) (b : BinSort) (o : Ordering) : b.step n o = BinSort.settle n (b.narrow o) := rfl

/-- `x` inserted at `lo` of `xs`, the indices below `x`, gives the indices below `x + 1`. -/
theorem insert_perm {xs : List Nat} {x lo} (h : xs.Perm (List.range x)) :
    (xs.take lo ++ x :: xs.drop lo).Perm (List.range (x + 1)) := by
  refine List.perm_middle.trans ?_
  rw [List.take_append_drop, List.range_succ]
  exact (h.cons x).trans (List.perm_append_singleton _ _).symm

/-- What `settle` gives from a state `Pre` admits: a state `Ok` admits and its call on `x` and the middle element,
or an order of the indices below `n`. -/
theorem BinSort.settle_pre {n b} (h : BinSort.Pre n b) :
    (∀ j k b', BinSort.settle n b = .inl (j, k, b') → BinSort.Ok n b' ∧ j = b'.x ∧ k = b'.xs.getD b'.mid 0) ∧
    ∀ σ, BinSort.settle n b = .inr σ → σ.Perm (List.range n) := by
  unfold BinSort.settle
  by_cases hlh : b.lo < b.hi
  · simp only [hlh, ite_true]
    refine ⟨fun j k b' e => ?_, fun _ e => (by cases e)⟩
    cases e
    exact ⟨⟨h.x_lt, h.perm, hlh, h.hi_le⟩, rfl, rfl⟩
  · simp only [hlh, ite_false]
    have hp := insert_perm (lo := b.lo) h.perm
    have hlen := hp.length_eq
    simp only [List.length_range] at hlen
    by_cases hn : b.x + 1 < n
    · simp only [hn, ite_true]
      refine ⟨fun j k b' e => ?_, fun _ e => (by cases e)⟩
      cases e
      exact ⟨⟨hn, hp, by simp [hlen], by simp⟩, rfl, rfl⟩
    · simp only [hn, ite_false]
      refine ⟨fun _ _ _ e => (by cases e), fun σ e => ?_⟩
      cases e
      have : b.x + 1 = n := by have := h.x_lt; omega
      rw [← this]; exact hp

/-- A call `settle` gives is the state itself, its range not empty, or the search for the next index. -/
theorem BinSort.settle_next {n b j k b'} (e : BinSort.settle n b = .inl (j, k, b')) :
    b.lo < b.hi ∧ b' = b ∨ b'.x = b.x + 1 ∧ b.x + 1 < n := by
  unfold BinSort.settle at e
  by_cases hlh : b.lo < b.hi
  · simp only [hlh, ite_true] at e; cases e; exact .inl ⟨hlh, rfl⟩
  · simp only [hlh, ite_false] at e
    by_cases hn : b.x + 1 < n
    · simp only [hn, ite_true] at e; cases e; exact .inr ⟨rfl, hn⟩
    · simp only [hn, ite_false] at e; cases e

/-- `settle` keeps the search's facts under a consistent comparator's order, and an order it gives is sorted. -/
theorem BinSort.settle_sorted {n O b} (H : OrdOk n O) (h : BinSort.Pre n b) (hs : b.Sorted O) :
    (∀ j k b', BinSort.settle n b = .inl (j, k, b') → b'.Sorted O) ∧
    ∀ σ, BinSort.settle n b = .inr σ → σ.Pairwise (SortR O) := by
  have hxn := h.x_lt
  have hlt : ∀ a ∈ b.xs, a < n := fun a ha => by have := h.mem_lt ha; omega
  -- `x` inserted at `lo` keeps `xs` sorted where the range is empty
  have hins : ¬ b.lo < b.hi → (b.xs.take b.lo ++ b.x :: b.xs.drop b.lo).Pairwise (SortR O) := by
    intro hlh
    have heq : b.lo = b.hi := by have := h.lo_le; omega
    have hxs := hs.1
    rw [← List.take_append_drop b.lo b.xs] at hxs
    obtain ⟨h1, h2, h3⟩ := List.pairwise_append.1 hxs
    refine List.pairwise_append.2 ⟨h1, List.pairwise_cons.2 ⟨fun a ha => ?_, h2⟩, fun a ha c hc => ?_⟩
    · have han : a ∈ b.xs := List.mem_of_mem_drop ha
      have hxa : O b.x a = .lt := hs.2.2 a (heq ▸ ha)
      have := H.swap_lt hxn (hlt a han) hxa
      exact ⟨by rw [this]; decide, by rw [this]; intro e; cases e⟩
    · have han : a ∈ b.xs := List.mem_of_mem_take ha
      rcases List.mem_cons.1 hc with rfl | hc
      · exact ⟨hs.2.1 a ha, fun _ => h.mem_lt han⟩
      · exact h3 a ha c hc
  unfold BinSort.settle
  by_cases hlh : b.lo < b.hi
  · simp only [hlh, ite_true]
    exact ⟨fun j k b' e => by cases e; exact hs, fun _ e => (by cases e)⟩
  · simp only [hlh, ite_false]
    by_cases hn : b.x + 1 < n
    · simp only [hn, ite_true]
      refine ⟨fun j k b' e => ?_, fun _ e => (by cases e)⟩
      cases e
      refine ⟨hins hlh, fun a ha => ?_, fun a ha => ?_⟩
      · dsimp only at ha; rw [List.take_zero] at ha; cases ha
      · dsimp only at ha; rw [List.drop_length] at ha; cases ha
    · simp only [hn, ite_false]
      exact ⟨fun _ _ _ e => (by cases e), fun σ e => (by cases e; exact hins hlh)⟩

/-- The narrowed range is a state `settle` is given. -/
theorem BinSort.narrow_pre {n b} (h : BinSort.Ok n b) (o : Ordering) : BinSort.Pre n (b.narrow o) := by
  have hm := BinSort.mid_lt h.lo_lt
  have := h.hi_le
  unfold BinSort.narrow
  split
  · exact ⟨h.x_lt, h.perm, hm.1, by simp; omega⟩
  · exact ⟨h.x_lt, h.perm, by simp; omega, h.hi_le⟩

/-- The narrowed range is smaller, for the same `x`. -/
theorem BinSort.narrow_lt {n b} (h : BinSort.Ok n b) (o : Ordering) :
    (b.narrow o).x = b.x ∧ (b.narrow o).hi - (b.narrow o).lo < b.hi - b.lo := by
  have hm := BinSort.mid_lt h.lo_lt
  unfold BinSort.narrow
  split <;> exact ⟨rfl, by simp; omega⟩

/-- The narrowed range keeps the search's facts where `o` is the order of `x` and the middle element. -/
theorem BinSort.narrow_sorted {n O b o} (H : OrdOk n O) (h : BinSort.Ok n b) (hs : b.Sorted O)
    (ho : O b.x (b.xs.getD b.mid 0) = o) : (b.narrow o).Sorted O := by
  have hm := BinSort.mid_lt h.lo_lt
  have hml : b.mid < b.xs.length := by have := h.hi_le; omega
  have hxn := h.x_lt
  have hlt : ∀ a ∈ b.xs, a < n := fun a ha => by have := h.pre.mem_lt ha; omega
  have hy : b.xs.getD b.mid 0 = b.xs[b.mid] := by simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hml]
  rw [hy] at ho
  have hyn : b.xs[b.mid] < n := hlt _ (List.getElem_mem hml)
  -- `xs` around its middle element
  have hpw := hs.1
  rw [← List.take_append_drop b.mid b.xs, List.drop_eq_getElem_cons hml] at hpw
  obtain ⟨-, hpw2, hpw3⟩ := List.pairwise_append.1 hpw
  unfold BinSort.narrow
  split
  · rename_i hlt'
    subst hlt'
    refine ⟨hs.1, hs.2.1, fun a ha => ?_⟩
    simp only at ha
    rw [List.drop_eq_getElem_cons hml] at ha
    rcases List.mem_cons.1 ha with rfl | ha
    · exact ho
    · exact H.lt_R hxn hyn (hlt a (List.mem_of_mem_drop ha)) ho ((List.pairwise_cons.1 hpw2).1 a ha)
  · rename_i hne
    refine ⟨hs.1, fun a ha => ?_, hs.2.2⟩
    simp only at ha
    rw [List.take_add_one, List.getElem?_eq_getElem hml] at ha
    simp only [Option.toList_some] at ha
    rcases List.mem_append.1 ha with ha | ha
    · intro hxa
      exact hne (ho ▸ H.lt_R hxn (hlt a (List.mem_of_mem_take ha)) hyn hxa
        (hpw3 a ha _ (List.mem_cons_self ..)))
    · rw [List.mem_singleton.1 ha, ho]; exact hne

/-- The start of a sort: a state `Ok` admits, sorted under any order, with its call, or an order of the indices
below `n`, sorted under any consistent comparator's order. -/
theorem binStart_ok {n : Nat} :
    (∀ j k b', binStart n = .inl (j, k, b') → BinSort.Ok n b' ∧ j = b'.x ∧ k = b'.xs.getD b'.mid 0 ∧
      ∀ O, b'.Sorted O) ∧
    ∀ σ, binStart n = .inr σ → σ.Perm (List.range n) ∧ ∀ O, σ.Pairwise (SortR O) := by
  unfold binStart
  by_cases hn : n ≤ 1
  · simp only [hn, ite_true]
    refine ⟨fun _ _ _ e => (by cases e), fun σ e => ?_⟩
    cases e
    refine ⟨.refl _, fun O => ?_⟩
    rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hn with rfl | rfl <;> simp
  · simp only [hn, ite_false]
    have e1 : BinSort.settle n ⟨[0], 1, 0, 1⟩ = .inl (1, 0, ⟨[0], 1, 0, 1⟩) := by
      simp [BinSort.settle, BinSort.mid]
    rw [e1]
    refine ⟨fun j k b' e => ?_, fun σ e => (by cases e)⟩
    cases e
    refine ⟨⟨by show 1 < n; omega, by simp, by simp, by simp⟩, rfl, rfl, fun O => ⟨by simp, ?_, ?_⟩⟩
    · intro a ha; simp at ha
    · intro a ha; simp at ha

/-! SortStep's answers by `sortStepBy`. -/

/-- The naturals read back from their values. -/
theorem natsOf_map {ix : M.Math → Option Nat} (hix : ∀ n, ix (M.ofNat n) = some n) (xs : List Nat) :
    natsOf ix (xs.map fun i => (.math (M.ofNat i) : Val M)) = some xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [natsOf, hix, ih]

/-- A state read back from its value is itself. -/
theorem binOf_val {ix : M.Math → Option Nat} (hix : ∀ n, ix (M.ofNat n) = some n) (b : BinSort) :
    binOf ix (b.val : Val M) = some b := by
  simp [binOf, BinSort.val, natsOf_map hix, hix]

/-- SortStep's answer by `sortStepBy` at `n`, the state `st` and the result `res`: `binNext`'s step. -/
theorem sortStepBy_inv {ix : M.Math → Option Nat} (hix : ∀ n, ix (M.ofNat n) = some n) {n st res} {s : State M}
    {r s'} (h : sortStepBy ix [.math (M.ofNat n), st, res] s = .ok r s') :
    ∃ a, binNext ix n st res = some a ∧ sortAnswer a s = .ok r s' := by
  cases ha : binNext ix n st res with
  | none => simp [sortStepBy, hix, ha, Run.stop] at h
  | some a => exact ⟨a, rfl, by simpa [sortStepBy, hix, ha] using h⟩

/-- `binNext` is the start at ~empty~, else a step from a state read back from `st` by a Number's order. -/
theorem binNext_inv {ix : M.Math → Option Nat} {n} {st res : Val M} {a} (h : binNext ix n st res = some a) :
    isEmptyV st = true ∧ a = binStart n ∨
      ∃ b x, binOf ix st = some b ∧ res = .num x ∧ a = b.step n (sortOrd x) := by
  unfold binNext at h
  split at h
  · rename_i he; cases h; exact .inl ⟨he, rfl⟩
  · split at h
    · rename_i b x hb; cases h; exact .inr ⟨b, x, hb, rfl, rfl⟩
    · cases h

/-- ~empty~ reads back as no state. -/
theorem binOf_empty {ix : M.Math → Option Nat} {st : Val M} (h : isEmptyV st = true) : binOf ix st = none := by
  cases st <;> first | rfl | simp [isEmptyV] at h

/-- The sort's order of a result is the one `cmpOrder` gives, where it gives one. -/
theorem sortOrd_of {r : M.Num} {p} (h : cmpOrder r = some p) : sortOrd r = p := by
  unfold cmpOrder at h
  unfold sortOrd
  cases hv : M.numView r <;> simp only [hv] at h ⊢ <;> first | exact Option.some.inj h | cases h

/-- A comparator's order on two indices; =C where `cmpOrder` gives none. -/
def cmpOrd (c : Nat → Nat → M.Num) (a b : Nat) : Ordering := (cmpOrder (c a b)).getD .eq

theorem cmpOrd_some {n} {c : Nat → Nat → M.Num} (hc : consistentCmp n c) {a b} (ha : a < n) (hb : b < n) :
    cmpOrder (c a b) = some (cmpOrd c a b) := by
  obtain ⟨p, hp⟩ := Option.ne_none_iff_exists'.1 (hc.1 a b ha hb)
  simp [cmpOrd, hp]

theorem cmpOrd_ok {n} {c : Nat → Nat → M.Num} (hc : consistentCmp n c) : OrdOk n (cmpOrd c) := by
  refine ⟨fun a ha => ?_, fun a b ha hb h => ?_, fun p a b d ha hb hd h1 h2 => ?_⟩
  · simpa [hc.2.1 a ha] using (cmpOrd_some hc ha ha).symm
  · have := hc.2.2.1 a b ha hb (by rw [cmpOrd_some hc ha hb, h])
    rw [cmpOrd_some hc hb ha] at this; exact Option.some.inj this
  · have := hc.2.2.2 p a b d ha hb hd (by rw [cmpOrd_some hc ha hb, h1]) (by rw [cmpOrd_some hc hb hd, h2])
    rw [cmpOrd_some hc ha hd] at this; exact Option.some.inj this

/-- SortReach for a host whose SortStep is another's. -/
theorem SortReach.congr {H H' : Host M} (e : ∀ vs, H.choice Known.pSortStep vs = H'.choice Known.pSortStep vs)
    {n st res h} (hr : SortReach H n st res h) : SortReach H' n st res h := by
  induction hr with
  | start => exact .start
  | call x _ hs ih =>
    obtain ⟨s, r, s', hc, hcl⟩ := hs
    exact .call x ih ⟨s, r, s', by rwa [← e], hcl⟩

/-- `sortNext` for a host whose SortStep is another's. -/
theorem sortNext_congr {H H' : Host M} (e : ∀ vs, H.choice Known.pSortStep vs = H'.choice Known.pSortStep vs)
    (n : Nat) : sortNext H n = sortNext H' n := by
  have step : ∀ {H H' : Host M}, (∀ vs, H.choice Known.pSortStep vs = H'.choice Known.pSortStep vs) →
      ∀ {st res st' j k}, sortCallStep H n st res st' j k → sortCallStep H' n st res st' j k :=
    fun e _ _ _ _ _ ⟨s, r, s', hc, hcl⟩ => ⟨s, r, s', by rwa [← e], hcl⟩
  funext a b
  apply propext
  constructor
  · rintro ⟨⟨h, hr⟩, j, k, x, hs, hx⟩; exact ⟨⟨h, hr.congr e⟩, j, k, x, step e hs, hx⟩
  · rintro ⟨⟨h, hr⟩, j, k, x, hs, hx⟩
    exact ⟨⟨h, hr.congr fun vs => (e vs).symm⟩, j, k, x, step (fun vs => (e vs).symm) hs, hx⟩

section Ix

variable {ix : M.Math → Option Nat} (hix : ∀ n, ix (M.ofNat n) = some n)
include hix

/-- What a sort reaches, by the binary insertion sort: ~empty~ at the start; else a state that `BinSort.Ok` admits,
read back from its value, after the call on its `x` and middle element, which returned the last result; and,
under every consistent comparator giving the calls' results, the state's search facts. -/
def SortInv (n : Nat) (st res : Val M) (h : List (Nat × Nat × M.Num)) : Prop :=
  st = .enum Known.eEmpty ∧ h = [] ∨
    ∃ b x, binOf ix st = some b ∧ b.Ok n ∧ res = .num x ∧ h.getLast? = some (b.x, b.xs.getD b.mid 0, x) ∧
      ∀ c, consistentCmp n c → (∀ e ∈ h, c e.1 e.2.1 = e.2.2) → b.Sorted (cmpOrd c)

omit hix in
/-- What the sort's next step gives from what it reaches: a call from a state `Ok` admits, sorted under every
consistent comparator giving the results so far; or a sorted order of the indices below `n`. -/
theorem binNext_ok {n st res h a} (hi : SortInv (ix := ix) n st res h) (ha : binNext ix n st res = some a) :
    (∀ j k b, a = .inl (j, k, b) → b.Ok n ∧ j = b.x ∧ k = b.xs.getD b.mid 0 ∧
      ∀ c, consistentCmp n c → (∀ e ∈ h, c e.1 e.2.1 = e.2.2) → b.Sorted (cmpOrd c)) ∧
    ∀ σ, a = .inr σ → σ.Perm (List.range n) ∧
      ∀ c, consistentCmp n c → (∀ e ∈ h, c e.1 e.2.1 = e.2.2) → σ.Pairwise (SortR (cmpOrd c)) := by
  rcases binNext_inv ha with ⟨_, rfl⟩ | ⟨b0, x0, hb0, rfl, rfl⟩
  · refine ⟨fun j k b e => ?_, fun σ e => ?_⟩
    · obtain ⟨h1, h2, h3, h4⟩ := binStart_ok.1 j k b e
      exact ⟨h1, h2, h3, fun c _ _ => h4 _⟩
    · obtain ⟨h1, h2⟩ := binStart_ok.2 σ e
      exact ⟨h1, fun c _ _ => h2 _⟩
  · rcases hi with ⟨rfl, -⟩ | ⟨b1, x1, hb1, hok, hx1, hlast, hs⟩
    · simp [binOf] at hb0
    · rw [hb0] at hb1; cases hb1
      cases hx1
      have hpre := BinSort.narrow_pre hok (sortOrd x0)
      have hsort : ∀ c, consistentCmp n c → (∀ e ∈ h, c e.1 e.2.1 = e.2.2) →
          (b0.narrow (sortOrd x0)).Sorted (cmpOrd c) := by
        intro c hc hag
        have hm := BinSort.mid_lt hok.lo_lt
        have hml : b0.mid < b0.xs.length := by have := hok.hi_le; omega
        have hyn : b0.xs.getD b0.mid 0 < n := by
          have : b0.xs.getD b0.mid 0 ∈ b0.xs := by
            simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hml]
          have := hok.pre.mem_lt this; have := hok.x_lt; omega
        have hcx := hag _ (List.mem_of_getLast? hlast)
        simp only at hcx
        have ho : cmpOrd c b0.x (b0.xs.getD b0.mid 0) = sortOrd x0 := by
          rw [← hcx, sortOrd_of (cmpOrd_some hc hok.x_lt hyn)]
        exact BinSort.narrow_sorted (cmpOrd_ok hc) hok (hs c hc hag) ho
      refine ⟨fun j k b e => ?_, fun σ e => ?_⟩
      · obtain ⟨h1, h2, h3⟩ := (BinSort.settle_pre hpre).1 j k b e
        exact ⟨h1, h2, h3, fun c hc hag =>
          (BinSort.settle_sorted (cmpOrd_ok hc) hpre (hsort c hc hag)).1 j k b e⟩
      · exact ⟨(BinSort.settle_pre hpre).2 σ e, fun c hc hag =>
          (BinSort.settle_sorted (cmpOrd_ok hc) hpre (hsort c hc hag)).2 σ e⟩

/-- Where SortStep is `sortStepBy`, a call a sort's step asks for is `binNext`'s, with its state's value. -/
theorem sortCallStep_inv {H : Host M} (hH : ∀ vs, H.choice Known.pSortStep vs = sortStepBy ix vs)
    (hcall : ∀ {j k st j' k' st' s r s'}, sortCall (M := M) j k st s = .ok r s' → sortCall j' k' st' s = .ok r s' →
      j = j' ∧ k = k' ∧ st = st')
    (hdone : ∀ {σ j k st s r s'}, sortDone (M := M) σ s = .ok r s' → sortCall j k st s = .ok r s' → False)
    {n st res st' j k} (h : sortCallStep H n st res st' j k) :
    ∃ b, binNext ix n st res = some (.inl (j, k, b)) ∧ st' = b.val := by
  obtain ⟨s, r, s', hc, hcl⟩ := h
  rw [hH] at hc
  obtain ⟨a, ha, hans⟩ := sortStepBy_inv hix hc
  match a, ha, hans with
  | .inl (j0, k0, b0), ha, hans =>
    obtain ⟨rfl, rfl, rfl⟩ := hcall hans hcl
    exact ⟨b0, ha, rfl⟩
  | .inr σ, _, hans => exact (hdone hans hcl).elim

/-- What a sort by `sortStepBy` reaches meets `SortInv`. -/
theorem sortReach_inv {H : Host M} (hH : ∀ vs, H.choice Known.pSortStep vs = sortStepBy ix vs)
    (hcall : ∀ {j k st j' k' st' s r s'}, sortCall (M := M) j k st s = .ok r s' → sortCall j' k' st' s = .ok r s' →
      j = j' ∧ k = k' ∧ st = st')
    (hdone : ∀ {σ j k st s r s'}, sortDone (M := M) σ s = .ok r s' → sortCall j k st s = .ok r s' → False)
    {n st res h} (hr : SortReach H n st res h) : SortInv (ix := ix) n st res h := by
  induction hr with
  | start => exact .inl ⟨rfl, rfl⟩
  | @call st res h st' j k x _ hs ih =>
    obtain ⟨b, hb, rfl⟩ := sortCallStep_inv hix hH hcall hdone hs
    obtain ⟨h1, h2, h3, h4⟩ := (binNext_ok ih hb).1 j k b rfl
    subst h2; subst h3
    refine .inr ⟨b, x, binOf_val hix b, h1, rfl, by simp, fun c hc hag => h4 c hc fun e he => ?_⟩
    exact hag e (List.mem_append_left _ he)

/-- SortStep by `sortStepBy` meets its law (§23.1.3.30.1): at what a sort reaches, a call on two indices less than
_n_, or an order that is a permutation meeting every consistent comparator's conditions given the calls made. -/
theorem sortStepBy_law {H : Host M} (hH : ∀ vs, H.choice Known.pSortStep vs = sortStepBy ix vs)
    (hcall : ∀ {j k st j' k' st' s r s'}, sortCall (M := M) j k st s = .ok r s' → sortCall j' k' st' s = .ok r s' →
      j = j' ∧ k = k' ∧ st = st')
    (hdone : ∀ {σ j k st s r s'}, sortDone (M := M) σ s = .ok r s' → sortCall j k st s = .ok r s' → False)
    {n st res h} {s : State M} {r s'} (hr : SortReach H n st res h)
    (hc : sortStepBy ix [.math (M.ofNat n), st, res] s = .ok r s') :
    (∃ j k st', j < n ∧ k < n ∧ sortCall j k st' s = .ok r s') ∨
    ∃ σ, σ.Perm (List.range n) ∧
      (∀ c, consistentCmp n c → (∀ e ∈ h, c e.1 e.2.1 = e.2.2) → sortOrderOk n c σ) ∧ sortDone σ s = .ok r s' := by
  have hi := sortReach_inv hix hH hcall hdone hr
  obtain ⟨a, ha, hans⟩ := sortStepBy_inv hix hc
  have hk := binNext_ok hi ha
  match a, hk, hans with
  | .inl (j, k, b), hk, hans =>
    obtain ⟨hok, rfl, rfl, -⟩ := hk.1 j k b rfl
    have hm := BinSort.mid_lt hok.lo_lt
    have hml : b.mid < b.xs.length := by have := hok.hi_le; omega
    have hyx : b.xs.getD b.mid 0 < b.x := hok.pre.mem_lt (by
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hml])
    exact .inl ⟨b.x, _, b.val, hok.x_lt, by have := hok.x_lt; omega, hans⟩
  | .inr σ, hk, hans =>
    obtain ⟨hperm, hsorted⟩ := hk.2 σ rfl
    refine .inr ⟨σ, hperm, fun c hc hag => ?_, hans⟩
    have hok := sorted_ok (cmpOrd_ok hc) hperm (hsorted c hc hag)
    intro j k hj hk'
    refine ⟨fun hl => (hok j k hj hk').1 ?_, fun hjk he => (hok j k hj hk').2 hjk ?_⟩
    · rw [cmpOrd_some hc hj hk'] at hl; exact Option.some.inj hl
    · rw [cmpOrd_some hc hj hk'] at he; exact Option.some.inj he

/-- info: 'Ecma.sortStepBy_law' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms sortStepBy_law

/-- The measure a sort's call lowers: how many indices are left to insert, then the size of the range; the start
above both. -/
def sortMeasure (n : Nat) (p : Val M × Val M) : Nat × Nat :=
  match binOf ix p.1 with
  | some b => (n - b.x, b.hi - b.lo)
  | none => (n + 1, 0)

/-- A sort by `sortStepBy` makes finitely many calls. -/
theorem sortStepBy_ends {H : Host M} (hH : ∀ vs, H.choice Known.pSortStep vs = sortStepBy ix vs)
    (hcall : ∀ {j k st j' k' st' s r s'}, sortCall (M := M) j k st s = .ok r s' → sortCall j' k' st' s = .ok r s' →
      j = j' ∧ k = k' ∧ st = st')
    (hdone : ∀ {σ j k st s r s'}, sortDone (M := M) σ s = .ok r s' → sortCall j k st s = .ok r s' → False)
    (n : Nat) : WellFounded (sortNext H n) := by
  refine Subrelation.wf (r := InvImage (Prod.Lex (· < ·) (· < ·)) (sortMeasure (ix := ix) n)) (fun {a p} hn => ?_)
    (InvImage.wf _ (Prod.lex Nat.lt_wfRel Nat.lt_wfRel).wf)
  obtain ⟨⟨h, hr⟩, j, k, x, hs, -⟩ := hn
  obtain ⟨b, hb, he⟩ := sortCallStep_inv hix hH hcall hdone hs
  have hok := ((binNext_ok (sortReach_inv hix hH hcall hdone hr) hb).1 j k b rfl).1
  show Prod.Lex _ _ (sortMeasure n a) (sortMeasure n p)
  unfold sortMeasure
  rw [he, binOf_val hix b]
  rcases binNext_inv hb with ⟨hemp, -⟩ | ⟨b0, x0, hb0, -, e⟩
  · rw [binOf_empty hemp]
    exact .left _ _ (by omega)
  · rw [hb0]
    have hi := sortReach_inv hix hH hcall hdone hr
    rcases hi with ⟨hst, -⟩ | ⟨b1, -, hb1, hok0, -⟩
    · rw [hst] at hb0; simp [binOf] at hb0
    rw [hb0] at hb1; cases hb1
    rw [BinSort.step_eq] at e
    obtain ⟨hx0, hlt⟩ := BinSort.narrow_lt hok0 (sortOrd x0)
    rcases BinSort.settle_next e.symm with ⟨-, rfl⟩ | ⟨hx, hxn⟩
    · dsimp only
      rw [hx0]; exact .right _ hlt
    · rw [hx0] at hx hxn
      dsimp only
      rw [hx]
      exact .left _ _ (by omega)

/-- info: 'Ecma.sortStepBy_ends' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms sortStepBy_ends

end Ix

end Ecma
