module

public import Engine.Proofs.CharSet.Ranges

@[expose] public section

/-!
# Normalized CharSets for `Engine.Impl`

A `CharSet` represents a mathematical set of `CharSetElement`s canonically as:
* `ranges`: sorted disjoint normalized intervals `(lo, hi)` (`rangeListOk 0 ranges.toList = true`);
* `strings`: `WMap (List Nat) Unit` holding sequences of length `≠ 1` with code points `≤ 0x10FFFF`.

Both invariants (`hr`, `hs`) are erased `Prop` fields with zero runtime overhead.
-/

namespace Engine.Model

/-- Canonical `CharSet` with erased range and string invariants. -/
structure CharSet where
  ranges : Array (Nat × Nat)
  strings : StrMap
  hr : rangeListOk 0 ranges.toList = true
  hs : stringsWf strings

instance : BEq CharSet where
  beq a b :=
    a.ranges == b.ranges &&
    a.strings.keys.size == b.strings.keys.size &&
    a.strings.keys.all fun k => (b.strings.get k).isSome

def csEmpty : CharSet where
  ranges := #[]
  strings := WMap.empty
  hr := rfl
  hs := wmap_empty_wf

instance : Inhabited CharSet where
  default := csEmpty

@[inline] def csHasChar (cs : CharSet) (c : Nat) : Bool :=
  _root_.Unicode.inRangesA cs.ranges c

private theorem mapM_point_le : ∀ (l : List MathVal) (pts : List Nat),
    l.mapM point? = some pts → ∀ c ∈ pts, c ≤ maxCodePoint
  | [], _, hm, c, hc => by change some [] = some _ at hm; cases hm; cases hc
  | x :: r, _, hm, c, hc => by
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at hm
    obtain ⟨d, hd, ts, hts, rfl⟩ := hm
    rcases List.mem_cons.1 hc with rfl | hc'
    · cases x with
      | frac _ _ => simp [point?] at hd
      | int j => simp [point?] at hd; omega
    · exact mapM_point_le r ts hts c hc'

def csAdd (cs : CharSet) (s : Array MathVal) : CharSet :=
  match hm : s.toList.mapM point? with
  | none => cs
  | some pts =>
    match pts with
    | [] =>
      { ranges := cs.ranges
        strings := cs.strings.put [] ()
        hr := cs.hr
        hs := by
          intro t ht
          rw [show (cs.strings.put [] ()).get t = if t = [] then some () else cs.strings.get t from
            cs.strings.property.get_put [] () t] at ht
          split at ht
          · rename_i hEq; subst hEq; exact ⟨by simp, fun _ h => by cases h⟩
          · exact cs.hs t ht }
    | [c] =>
      let h1 : rangeListOk 0 #[(c, c)].toList = true := by
        have hcLe : c ≤ maxCodePoint := mapM_point_le s.toList [c] hm c (by simp)
        simp [rangeListOk, hcLe]
      { ranges := unionRanges cs.ranges #[(c, c)]
        strings := cs.strings
        hr := (unionRanges_ok cs.ranges #[(c, c)] cs.hr h1).1
        hs := cs.hs }
    | a :: b :: r =>
      let pts := a :: b :: r
      { ranges := cs.ranges
        strings := cs.strings.put pts ()
        hr := cs.hr
        hs := by
          intro t ht
          rw [show (cs.strings.put pts ()).get t = if t = pts then some () else cs.strings.get t from
            cs.strings.property.get_put pts () t] at ht
          split at ht
          · rename_i hEq; subst hEq; exact ⟨by simp [pts], mapM_point_le s.toList pts hm⟩
          · exact cs.hs t ht }

def csInterval (lo hi : MathVal) : CharSet :=
  match hl : point? lo, hh : point? hi with
  | some l, some h =>
    if hle : l ≤ h then
      have hok : rangeListOk 0 #[(l, h)].toList = true := by
        have hhi : h ≤ maxCodePoint := by
          cases hi with | frac _ _ => simp [point?] at hh | int j => simp [point?] at hh; omega
        simp [rangeListOk, hle, hhi]
      ⟨#[(l, h)], WMap.empty, hok, wmap_empty_wf⟩
    else csEmpty
  | _, _ => csEmpty

def csUnion (a b : CharSet) : CharSet where
  ranges := unionRanges a.ranges b.ranges
  strings := b.strings.keys.foldl (fun m k => m.put k ()) a.strings
  hr := (unionRanges_ok a.ranges b.ranges a.hr b.hr).1
  hs := by
    intro s hs'
    rw [← Array.foldl_toList, wmap_foldl_put] at hs'
    rcases hs' with ha | hb
    · exact a.hs s ha
    · exact b.hs s ((wmap_mem_keys b.strings s).1 hb)

def csInter (a b : CharSet) : CharSet where
  ranges := interRanges a.ranges b.ranges
  strings := a.strings.keys.foldl (fun m k => if (b.strings.get k).isSome then m.put k () else m) WMap.empty
  hr := (interRanges_ok a.ranges b.ranges a.hr b.hr).1
  hs := by
    intro s hs'
    rw [← Array.foldl_toList, wmap_foldl_inter] at hs'
    rcases hs' with hemp | ⟨ha, _⟩
    · simp [WMap.get, WMap.empty, OMap.get, OMap.empty] at hemp
    · exact a.hs s ((wmap_mem_keys a.strings s).1 ha)

def csDiff (a b : CharSet) : CharSet where
  ranges := diffRanges a.ranges b.ranges
  strings := b.strings.keys.foldl (fun m k => m.del k) a.strings
  hr := (diffRanges_ok a.ranges b.ranges a.hr b.hr).1
  hs := by
    intro s hs'
    rw [← Array.foldl_toList, wmap_foldl_del] at hs'
    exact a.hs s hs'.1

def csHas (cs : CharSet) (s : Array MathVal) : Bool :=
  match s.toList.mapM point? with
  | none => false
  | some [c] => csHasChar cs c
  | some pts => (cs.strings.get pts).isSome

def csSize (cs : CharSet) : MathVal :=
  .int (rangesCount cs.ranges + cs.strings.keys.size)

def csGet (cs : CharSet) (idx : MathVal) : Option (Array MathVal) := do
  let k ← MathVal.idx idx
  let rc := rangesCount cs.ranges
  if k < rc then
    let c ← rangesGet cs.ranges k
    return #[.int c]
  else
    let s ← cs.strings.keys[k - rc]?
    return (s.map fun (c : Nat) => MathVal.int c).toArray

@[inline] def csAllSingle (cs : CharSet) : Bool :=
  cs.strings.keys.isEmpty

def csSingles (cs : CharSet) : CharSet where
  ranges := cs.ranges
  strings := WMap.empty
  hr := cs.hr
  hs := wmap_empty_wf

def csFromProp (p v : Array MathVal) : Option CharSet := do
  let nat : MathVal → Option Nat := fun | .int i => if 0 ≤ i then some i.toNat else none | _ => none
  let pn ← p.toList.mapM nat
  let vn ← v.toList.mapM nat
  let (rs0, ss0) ← Engine.Model.Unicode.propertyValue? pn vn
  let rs := rs0.mergeSort fun x y => x.1 ≤ y.1
  let ss := ss0.mergeSort fun x y => PropSets.key x ≤ PropSets.key y
  if hguard : PropSets.rangesOk rs && PropSets.stringsOk ss then
    have ⟨hrok, hsok⟩ : PropSets.rangesOk rs = true ∧ PropSets.stringsOk ss = true := by
      simpa [Bool.and_eq_true] using hguard
    have ⟨_, hsAll⟩ := PropSets.strings_ok hsok
    some {
      ranges := coalesceRanges rs
      strings := ss.foldl (fun m s => m.put s ()) WMap.empty
      hr := (coalesceRanges_ok rs hrok).1
      hs := by
        intro s hs'
        rw [wmap_foldl_put] at hs'
        rcases hs' with hemp | hmem
        · simp [WMap.get, WMap.empty, OMap.get, OMap.empty] at hemp
        · have ⟨h2, hle⟩ := hsAll s hmem
          exact ⟨by omega, hle⟩ }
  else none

/-! ### `csNoScf`, `csCanonExtra`, `csHasCanon` -/

def pairsListOk : Nat → List (Nat × Nat) → Bool
  | _, [] => true
  | minC, (c, _) :: r => minC ≤ c && c ≤ maxCodePoint && pairsListOk (c + 1) r

theorem scfPairs_listOk : pairsListOk 0 scfPairsList = true := by decide +kernel
theorem nonUCanonPairs_listOk : pairsListOk 0 nonUCanonPairsList = true := by decide +kernel

theorem pairsListOk_spec : ∀ (minC : Nat) (l : List (Nat × Nat)), pairsListOk minC l = true →
    (∀ p ∈ l, minC ≤ p.1 ∧ p.1 ≤ maxCodePoint) ∧ l.Pairwise (fun a b => a.1 < b.1) := by
  intro minC l
  induction l generalizing minC with
  | nil => intro _; simp
  | cons p r ih =>
    rcases p with ⟨c, d⟩
    simp only [pairsListOk, Bool.and_eq_true, decide_eq_true_eq]
    intro h
    have ⟨ih1, ih2⟩ := ih (c + 1) h.2
    refine ⟨?_, ?_⟩
    · intro x hx
      rcases List.mem_cons.1 hx with rfl | hx
      · exact h.1
      · exact ⟨by have := (ih1 x hx).1; omega, (ih1 x hx).2⟩
    · exact List.pairwise_cons.2 ⟨fun y hy => by have := (ih1 y hy).1; omega, ih2⟩

theorem scfDomainRanges_ok : rangeListOk 0 scfDomainRanges.toList = true :=
  have ⟨h1, h2⟩ := pairsListOk_spec 0 scfPairsList scfPairs_listOk
  (coalescePoints_ok _ (List.pairwise_map.2 h2) (fun c hc => by
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hc; exact (h1 p hp).2)).1

def csNoScf : CharSet where
  ranges := complRanges scfDomainRanges
  strings := WMap.empty
  hr := (complRanges_ok scfDomainRanges scfDomainRanges_ok).1
  hs := wmap_empty_wf

theorem foldl_filter_pushRange_ok (cs : CharSet) (l : List (Nat × Nat)) (acc : List (Nat × Nat))
    (minC : Nat) (hl : pairsListOk minC l = true) (hacc : RevOk acc) (hord : revHeadLo acc ≤ minC) :
    RevOk (l.foldl (fun a (c, d) => if !csHasChar cs c && csHasChar cs d then pushRange a c c else a) acc) ∧
      ∀ c, MemRanges (l.foldl (fun a (c, d) => if !csHasChar cs c && csHasChar cs d then pushRange a c c else a) acc) c ↔
        MemRanges acc c ∨ ∃ d, (c, d) ∈ l ∧ csHasChar cs c = false ∧ csHasChar cs d = true := by
  induction l generalizing minC acc with
  | nil => simp [hacc]
  | cons p r ih =>
    rcases p with ⟨c, d⟩
    simp only [pairsListOk, Bool.and_eq_true, decide_eq_true_eq] at hl
    have hstep : RevOk (if !csHasChar cs c && csHasChar cs d then pushRange acc c c else acc) ∧
        revHeadLo (if !csHasChar cs c && csHasChar cs d then pushRange acc c c else acc) ≤ c + 1 ∧
        ∀ c', MemRanges (if !csHasChar cs c && csHasChar cs d then pushRange acc c c else acc) c' ↔
          MemRanges acc c' ∨ (c' = c ∧ csHasChar cs c = false ∧ csHasChar cs d = true) := by
      by_cases hc0 : csHasChar cs c = false <;> by_cases hd1 : csHasChar cs d = true
      · simp only [hc0, hd1, Bool.not_false, Bool.true_and, ↓reduceIte]
        have ⟨hok', hord', hmem'⟩ := pushRange_ok hacc (Nat.le_refl _) hl.1.2 (Nat.le_trans hord hl.1.1)
        refine ⟨hok', by omega, fun c' => ?_⟩
        rw [hmem' c']
        constructor
        · rintro (h | ⟨h1, h2⟩); exact .inl h; exact .inr ⟨by omega, trivial, trivial⟩
        · rintro (h | ⟨rfl, _⟩); exact .inl h; exact .inr ⟨Nat.le_refl _, Nat.le_refl _⟩
      all_goals
        have hf : (!csHasChar cs c && csHasChar cs d) = false := by cases h1 : csHasChar cs c <;> cases h2 : csHasChar cs d <;> simp_all
        simp only [hf, Bool.false_eq_true, ↓reduceIte]
        refine ⟨hacc, Nat.le_trans hord (by omega), fun c' => ?_⟩
        constructor
        · intro h; exact .inl h
        · rintro (h | ⟨rfl, _⟩); exact h; simp_all
    have ⟨hokF, hmemF⟩ := ih _ (c + 1) hl.2 hstep.1 hstep.2.1
    refine ⟨hokF, fun c' => ?_⟩
    rw [List.foldl_cons, hmemF c', hstep.2.2 c']
    simp only [List.mem_cons]
    constructor
    · rintro ((h | ⟨rfl, hc0, hd1⟩) | ⟨d', hdm, hc0, hd1⟩)
      · exact .inl h
      · exact .inr ⟨d, .inl rfl, hc0, hd1⟩
      · exact .inr ⟨d', .inr hdm, hc0, hd1⟩
    · rintro (h | ⟨d', heq | hdm, hc0, hd1⟩)
      · exact .inl (.inl h)
      · cases heq; exact .inl (.inr ⟨rfl, hc0, hd1⟩)
      · exact .inr ⟨d', hdm, hc0, hd1⟩

def csCanonExtra (cs : CharSet) (u : Bool) : CharSet where
  ranges :=
    let pairs := if u then scfPairs else nonUCanonPairs
    (pairs.foldl (fun acc (c, d) =>
      if !csHasChar cs c && csHasChar cs d then pushRange acc c c else acc) []).reverse.toArray
  strings := WMap.empty
  hr := by
    have hok : pairsListOk 0 (if u then scfPairs else nonUCanonPairs).toList = true := by
      cases u <;> simp [scfPairs, nonUCanonPairs, scfPairs_listOk, nonUCanonPairs_listOk]
    dsimp only
    rw [← Array.foldl_toList]
    exact (revOk_reverse (foldl_filter_pushRange_ok cs _ [] 0 hok trivial (Nat.zero_le _)).1).1
  hs := wmap_empty_wf

def csHasCanon (cs : CharSet) (cc : MathVal) (u ic : Bool) : Bool :=
  match point? cc with
  | none => false
  | some c =>
    if !ic then csHasChar cs c
    else
      let (pre, dom) := if u then (scfPreimages, scfDomainRanges) else (nonUCanonPreimages, nonUCanonDomainRanges)
      (match _root_.Unicode.lookupSortedA pre c with
        | some as => as.any (csHasChar cs)
        | none => false) ||
      (!_root_.Unicode.inRangesA dom c && csHasChar cs c)

end Engine.Model
