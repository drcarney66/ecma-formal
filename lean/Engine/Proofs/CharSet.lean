module

public import Engine.Proofs.CharSet.Base
public import Engine.Proofs.CharSet.Case

@[expose] public section

/-!
# `Engine.Impl` satisfies the structural, indexing, and property `CharSet` laws
-/

namespace Engine.Impl

open Ecma Engine.Model

theorem csEmpty_law (e : Array MathVal) : Impl.csHas Impl.csEmpty e = false := by
  change Engine.Model.csHas Engine.Model.csEmpty e = false
  unfold Engine.Model.csHas
  cases h : e.toList.mapM point? with
  | none => rfl
  | some pts =>
    cases pts with
    | nil => simp [csEmpty, wmap_empty_get]
    | cons _ r =>
      cases r with
      | nil => simp [csEmpty, csHasChar, _root_.Unicode.inRangesA, _root_.Unicode.lastLE, _root_.Unicode.bisect]
      | cons _ _ => simp [csEmpty, wmap_empty_get]

theorem csAdd_law (cs : CharSet) (s e : Array MathVal)
    (hs : Model.allPoints Impl s) (he : Model.allPoints Impl e) :
    Impl.csHas (Impl.csAdd cs s) e = true ↔ Impl.csHas cs e = true ∨ seqList (M := Impl) e = seqList (M := Impl) s := by
  obtain ⟨sPts, hsMap⟩ := (allPoints_iff s).1 hs
  obtain ⟨ePts, heMap⟩ := (allPoints_iff e).1 he
  have ⟨hsList, hsLe⟩ := mapM_point?_eq hsMap
  have ⟨heList, heLe⟩ := mapM_point?_eq heMap
  have hseqEq : (seqList (M := Impl) e = seqList (M := Impl) s) ↔ ePts = sPts := by
    rw [seqList_eq, seqList_eq, hsList, heList]; exact ⟨int_map_inj, fun h => h ▸ rfl⟩
  rw [hseqEq, csHas_iff_mem cs ePts heLe heList]
  change Engine.Model.csHas (Engine.Model.csAdd cs s) e = true ↔ _
  unfold Engine.Model.csAdd
  split
  · rename_i hnone; simp [hsMap] at hnone
  · rename_i pts hsome
    rw [hsMap] at hsome; cases hsome
    cases sPts with
    | nil =>
      rw [csHas_iff_mem _ ePts heLe heList]
      simp only [show (cs.strings.put [] ()).get ePts = if ePts = [] then some () else cs.strings.get ePts from
        cs.strings.property.get_put [] () ePts]
      by_cases h0 : ePts = [] <;> simp [h0]
    | cons c r =>
      cases r with
      | nil =>
        rw [csHas_iff_mem _ ePts heLe heList]
        have h1 : rangeListOk 0 #[(c, c)].toList = true := by simp [rangeListOk, hsLe c (by simp)]
        have ⟨_, hmem⟩ := unionRanges_ok cs.ranges #[(c, c)] cs.hr h1
        dsimp only
        simp only [hmem, memRanges_cons, memRanges_nil, or_false]
        constructor
        · rintro (⟨d, rfl, hd | ⟨h1', h2'⟩⟩ | h); exact .inl (.inl ⟨d, rfl, hd⟩); exact .inr (by simp; omega); exact .inl (.inr h)
        · rintro ((⟨d, rfl, hd⟩ | h) | rfl); exact .inl ⟨d, rfl, .inl hd⟩; exact .inr h; exact .inl ⟨c, rfl, .inr ⟨Nat.le_refl _, Nat.le_refl _⟩⟩
      | cons d r' =>
        rw [csHas_iff_mem _ ePts heLe heList]
        simp only [show (cs.strings.put (c :: d :: r') ()).get ePts =
            if ePts = c :: d :: r' then some () else cs.strings.get ePts from
          cs.strings.property.get_put (c :: d :: r') () ePts]
        by_cases h0 : ePts = c :: d :: r' <;> simp [h0]

theorem csInterval_law (lo hi : MathVal) (e : Array MathVal) (hlo : Model.isPoint Impl lo) (hhi : Model.isPoint Impl hi)
    (he : Model.allPoints Impl e) :
    Impl.csHas (Impl.csInterval lo hi) e = true ↔
      ∃ c, seqList (M := Impl) e = [c] ∧ Model.isPoint Impl c ∧ ¬ Impl.lt c lo ∧ ¬ Impl.lt hi c := by
  obtain ⟨l, hl, rfl⟩ := (isPoint_iff lo).1 hlo
  obtain ⟨h, hh, rfl⟩ := (isPoint_iff hi).1 hhi
  obtain ⟨ePts, heMap⟩ := (allPoints_iff e).1 he
  have ⟨heList, heLe⟩ := mapM_point?_eq heMap
  change Impl.csHas (csInterval (.int l) (.int h)) e = true ↔ _
  unfold csInterval
  split
  · rename_i l' h' hl' hh'
    rw [(point?_eq_some (.int l) l).2 ⟨hl, rfl⟩] at hl'; injection hl' with hlEq; subst hlEq
    rw [(point?_eq_some (.int h) h).2 ⟨hh, rfl⟩] at hh'; injection hh' with hhEq; subst hhEq
    by_cases hle : l ≤ h
    · simp only [hle, ↓reduceDIte]
      rw [csHas_iff_mem _ ePts heLe heList]
      rw [show #[(l, h)].toList = [(l, h)] from rfl]
      simp only [memRanges_cons, memRanges_nil, or_false,
        wmap_empty_get, Option.isSome_none, Bool.false_eq_true, and_false, or_false, seqList_eq, heList]
      constructor
      · rintro ⟨c, rfl, hc1, hc2⟩
        exact ⟨.int c, rfl, nat_isPoint c (heLe c (by simp)),
          by show ¬ decide ((c : Int) < l) = true; simp [hc1], by show ¬ decide ((h : Int) < c) = true; simp [hc2]⟩
      · rintro ⟨c, hce, hcPt, hnl, hnh⟩
        obtain ⟨cn, _, rfl⟩ := (isPoint_iff c).1 hcPt
        have hePts : ePts = [cn] := int_map_inj (by simpa using hce)
        subst hePts
        have h1 : l ≤ cn := Classical.byContradiction fun hlt => hnl (by change decide ((cn : Int) < l) = true; exact decide_eq_true (by omega))
        have h2 : cn ≤ h := Classical.byContradiction fun hlt => hnh (by change decide ((h : Int) < cn) = true; exact decide_eq_true (by omega))
        exact ⟨cn, rfl, h1, h2⟩
    · simp only [hle, ↓reduceDIte]
      constructor
      · intro hf; change Impl.csHas Impl.csEmpty e = true at hf; rw [csEmpty_law e] at hf; cases hf
      · rintro ⟨c, _, hcPt, hnl, hnh⟩
        obtain ⟨cn, _, rfl⟩ := (isPoint_iff c).1 hcPt
        have : ¬ (cn : Int) < l := fun ht => hnl (by change decide ((cn : Int) < l) = true; exact decide_eq_true ht)
        have : ¬ (h : Int) < cn := fun ht => hnh (by change decide ((h : Int) < cn) = true; exact decide_eq_true ht)
        omega
  · rename_i hnot
    exfalso
    exact hnot l h ((point?_eq_some (.int l) l).2 ⟨hl, rfl⟩) ((point?_eq_some (.int h) h).2 ⟨hh, rfl⟩)

theorem csUnion_law (a b : CharSet) (e : Array MathVal) (he : Model.allPoints Impl e) :
    Impl.csHas (Impl.csUnion a b) e = true ↔ Impl.csHas a e = true ∨ Impl.csHas b e = true := by
  obtain ⟨pts, hmap⟩ := (allPoints_iff e).1 he
  have ⟨hl, hle⟩ := mapM_point?_eq hmap
  have ⟨_, hrMem⟩ := unionRanges_ok a.ranges b.ranges a.hr b.hr
  rw [csHas_iff_mem _ pts hle hl, csHas_iff_mem a pts hle hl, csHas_iff_mem b pts hle hl]
  simp only [csUnion, hrMem, ← Array.foldl_toList, wmap_foldl_put, wmap_mem_keys]
  constructor
  · rintro (⟨c, rfl, h1 | h2⟩ | ⟨hn, h1 | h2⟩); exact .inl (.inl ⟨c, rfl, h1⟩); exact .inr (.inl ⟨c, rfl, h2⟩); exact .inl (.inr ⟨hn, h1⟩); exact .inr (.inr ⟨hn, h2⟩)
  · rintro ((⟨c, rfl, h⟩ | ⟨hn, h⟩) | (⟨c, rfl, h⟩ | ⟨hn, h⟩)); exact .inl ⟨c, rfl, .inl h⟩; exact .inr ⟨hn, .inl h⟩; exact .inl ⟨c, rfl, .inr h⟩; exact .inr ⟨hn, .inr h⟩

theorem csInter_law (a b : CharSet) (e : Array MathVal) (he : Model.allPoints Impl e) :
    Impl.csHas (Impl.csInter a b) e = true ↔ Impl.csHas a e = true ∧ Impl.csHas b e = true := by
  obtain ⟨pts, hmap⟩ := (allPoints_iff e).1 he
  have ⟨hl, hle⟩ := mapM_point?_eq hmap
  have ⟨_, hrMem⟩ := interRanges_ok a.ranges b.ranges a.hr b.hr
  rw [csHas_iff_mem _ pts hle hl, csHas_iff_mem a pts hle hl, csHas_iff_mem b pts hle hl]
  simp only [csInter, hrMem, ← Array.foldl_toList, wmap_foldl_inter, wmap_mem_keys,
    wmap_empty_get, Option.isSome_none, Bool.false_eq_true, false_or]
  constructor
  · rintro (⟨c, rfl, h1, h2⟩ | ⟨hn, h1, h2⟩); exact ⟨.inl ⟨c, rfl, h1⟩, .inl ⟨c, rfl, h2⟩⟩; exact ⟨.inr ⟨hn, h1⟩, .inr ⟨hn, h2⟩⟩
  · rintro ⟨⟨c, rfl, h1⟩ | ⟨hn, h1⟩, ⟨c2, h2eq, h2⟩ | ⟨hn2, h2⟩⟩
    · injection h2eq with hcc; subst hcc; exact .inl ⟨c, rfl, h1, h2⟩
    · simp at hn2
    · subst h2eq; simp at hn
    · exact .inr ⟨hn, h1, h2⟩

theorem csDiff_law (a b : CharSet) (e : Array MathVal) (he : Model.allPoints Impl e) :
    Impl.csHas (Impl.csDiff a b) e = true ↔ Impl.csHas a e = true ∧ Impl.csHas b e = false := by
  obtain ⟨pts, hmap⟩ := (allPoints_iff e).1 he
  have ⟨hl, hle⟩ := mapM_point?_eq hmap
  have ⟨_, hrMem⟩ := diffRanges_ok a.ranges b.ranges a.hr b.hr
  rw [csHas_iff_mem _ pts hle hl, csHas_iff_mem a pts hle hl, Bool.eq_false_iff]
  simp only [ne_eq, csHas_iff_mem b pts hle hl]
  simp only [csDiff, hrMem, ← Array.foldl_toList, wmap_foldl_del, wmap_mem_keys]
  constructor
  · rintro (⟨c, rfl, h1, h2⟩ | ⟨hn, h1, h2⟩)
    · exact ⟨.inl ⟨c, rfl, h1⟩, fun h => by rcases h with ⟨c', hc', hm⟩ | ⟨hn', _⟩; injection hc' with heq; subst heq; exact h2 hm; simp at hn'⟩
    · exact ⟨.inr ⟨hn, h1⟩, fun h => by rcases h with ⟨c', hc', _⟩ | ⟨_, hm⟩; subst hc'; simp at hn; exact h2 hm⟩
  · rintro ⟨⟨c, rfl, h1⟩ | ⟨hn, h1⟩, hnb⟩
    · exact .inl ⟨c, rfl, h1, fun hm => hnb (.inl ⟨c, rfl, hm⟩)⟩
    · exact .inr ⟨hn, h1, fun hm => hnb (.inr ⟨hn, hm⟩)⟩

theorem csSize_nat_law (cs : CharSet) :
    Impl.isInt (Impl.csSize cs) = true ∧ ¬ Impl.lt (Impl.csSize cs) (Impl.ofNat 0) := by
  refine ⟨rfl, ?_⟩
  change ¬ decide (((rangesCount cs.ranges + cs.strings.keys.size : Nat) : Int) < 0) = true
  rw [decide_eq_false (by omega)]; exact Bool.false_ne_true

theorem parseGet {cs : CharSet} {idx : MathVal} {res : Array MathVal} (hg : csGet cs idx = some res) :
    ∃ k : Nat, idx = .int k ∧
      ((k < rangesCount cs.ranges ∧ ∃ c, rangesGet cs.ranges k = some c ∧ res = #[.int c]) ∨
       (rangesCount cs.ranges ≤ k ∧ ∃ s, cs.strings.keys[k - rangesCount cs.ranges]? = some s ∧
          res = (s.map (fun c : Nat => MathVal.int c)).toArray)) := by
  unfold csGet at hg
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def] at hg
  obtain ⟨k, hk, hrest⟩ := hg
  have hidx : idx = .int k := by
    cases idx with
    | frac _ _ => simp [MathVal.idx] at hk
    | int j => simp only [MathVal.idx] at hk; split at hk; cases hk; congr 1; exact (Int.toNat_of_nonneg ‹_›).symm; cases hk
  refine ⟨k, hidx, ?_⟩
  split at hrest
  · rename_i hlt; simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at hrest
    obtain ⟨c, hc, rfl⟩ := hrest; exact .inl ⟨hlt, c, hc, rfl⟩
  · rename_i hge; simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at hrest
    obtain ⟨s, hs', rfl⟩ := hrest; exact .inr ⟨Nat.le_of_not_lt hge, s, hs', rfl⟩

theorem csGet_some_law (cs : CharSet) (i : MathVal) (e : Array MathVal) (h : Impl.csGet cs i = some e) :
    Impl.isInt i = true ∧ ¬ Impl.lt i (Impl.ofNat 0) ∧ Impl.lt i (Impl.csSize cs) = true ∧
      Model.allPoints Impl e ∧ Impl.csHas cs e = true := by
  obtain ⟨hs, _, _, _⟩ := rangeListGet_spec cs.hr
  obtain ⟨k, rfl, ⟨hkLt, c, hc, rfl⟩ | ⟨hkGe, s, hsGet, rfl⟩⟩ := parseGet h
  · rw [rangesGet_eq] at hc; have ⟨_, hcLe, hcMem⟩ := hs k c hc
    have hltSize : Impl.lt (.int k) (Impl.csSize cs) = true := by
      show decide ((k : Int) < ((rangesCount cs.ranges + cs.strings.keys.size : Nat) : Int)) = true
      have := rangesCount_eq cs.ranges; exact decide_eq_true (by omega)
    exact ⟨rfl, by show ¬ decide ((k : Int) < 0) = true; simp, hltSize,
      by simpa using points_isPoint [c] (fun _ hm => by simp at hm; subst hm; exact hcLe),
      (csHas_iff_mem cs [c] (fun _ hm => by simp at hm; subst hm; exact hcLe) rfl).2 (.inl ⟨c, rfl, hcMem⟩)⟩
  · obtain ⟨hidx, hsEq⟩ := Array.getElem?_eq_some_iff.1 hsGet
    have hm := (wmap_mem_keys cs.strings s).1 (Array.mem_toList_iff.2 (hsEq ▸ Array.getElem_mem hidx))
    obtain ⟨hne1, hsLe⟩ := cs.hs s hm
    have hltSize : Impl.lt (.int k) (Impl.csSize cs) = true := by
      show decide ((k : Int) < ((rangesCount cs.ranges + cs.strings.keys.size : Nat) : Int)) = true
      exact decide_eq_true (by omega)
    exact ⟨rfl, by show ¬ decide ((k : Int) < 0) = true; simp, hltSize,
      by simpa using points_isPoint s hsLe,
      (csHas_iff_mem cs s hsLe (by simp)).2 (.inr ⟨hne1, hm⟩)⟩

theorem csGet_lt_law (cs : CharSet) (i : MathVal) (hi : Impl.isInt i = true)
    (h0 : ¬ Impl.lt i (Impl.ofNat 0)) (hlt : Impl.lt i (Impl.csSize cs) = true) :
    (Impl.csGet cs i).isSome = true := by
  obtain ⟨_, hl, _, _⟩ := rangeListGet_spec cs.hr
  cases i with
  | frac _ _ => cases hi
  | int j =>
    have hj0 : 0 ≤ j := Classical.byContradiction fun hlt0 =>
      h0 (by change decide (j < (0 : Int)) = true; exact decide_eq_true (Int.not_le.1 hlt0))
    have hltNat : j.toNat < rangesCount cs.ranges + cs.strings.keys.size := by
      have : decide (j < ((rangesCount cs.ranges + cs.strings.keys.size : Nat) : Int)) = true := hlt
      have := of_decide_eq_true this; omega
    change (csGet cs (.int j)).isSome = true
    unfold csGet; simp only [MathVal.idx, hj0, ↓reduceIte, Option.bind_eq_bind, Option.bind_some, Option.pure_def]
    split
    · rename_i hkLt; rw [rangesCount_eq] at hkLt; rw [rangesGet_eq]
      have hsm := hl j.toNat hkLt; cases hrg : rangeListGet cs.ranges.toList j.toNat <;> simp_all
    · rename_i hkGe
      have hjLt : j.toNat - rangesCount cs.ranges < cs.strings.keys.size := by omega
      rw [Array.getElem?_eq_getElem hjLt]; rfl

theorem csGet_distinct_law (cs : CharSet) (i j : MathVal) (e f : Array MathVal)
    (hi : Impl.csGet cs i = some e) (hj : Impl.csGet cs j = some f)
    (heq : seqList (M := Impl) e = seqList (M := Impl) f) : i = j := by
  obtain ⟨_, _, hinj, _⟩ := rangeListGet_spec cs.hr
  rw [seqList_eq, seqList_eq] at heq
  obtain ⟨ki, rfl, hiCases⟩ := parseGet hi
  obtain ⟨kj, rfl, hjCases⟩ := parseGet hj
  rcases hiCases with ⟨_, ci, hci, rfl⟩ | ⟨hiGe, si, hsi, rfl⟩ <;>
    rcases hjCases with ⟨_, cj, hcj, rfl⟩ | ⟨hjGe, sj, hsj, rfl⟩
  · have : ci = cj := by
      have h1 : ([MathVal.int ci] : List MathVal) = [MathVal.int cj] := by simpa using heq
      exact Int.ofNat.inj (MathVal.int.inj (List.cons.inj h1).1)
    subst this; rw [rangesGet_eq] at hci hcj; rw [hinj ki kj ci hci hcj]
  · exfalso
    obtain ⟨hjIdx, hjEq⟩ := Array.getElem?_eq_some_iff.1 hsj
    have hm := (wmap_mem_keys cs.strings sj).1 (Array.mem_toList_iff.2 (hjEq ▸ Array.getElem_mem hjIdx))
    have hsz := (cs.hs sj hm).1; have hlen := congrArg List.length heq; simp at hlen; omega
  · exfalso
    obtain ⟨hiIdx, hiEq⟩ := Array.getElem?_eq_some_iff.1 hsi
    have hm := (wmap_mem_keys cs.strings si).1 (Array.mem_toList_iff.2 (hiEq ▸ Array.getElem_mem hiIdx))
    have hsz := (cs.hs si hm).1; have hlen := congrArg List.length heq; simp at hlen; omega
  · have hsEq : si = sj := int_map_inj (by simpa using heq)
    subst hsEq
    have := cs.strings.property.keys_once hsi hsj
    congr 1; omega

theorem csHas_exists_law (cs : CharSet) (e : Array MathVal) (he : Model.allPoints Impl e)
    (h : Impl.csHas cs e = true) :
    ∃ i e', Impl.csGet cs i = some e' ∧ seqList (M := Impl) e' = seqList (M := Impl) e := by
  obtain ⟨hs, _, _, hex⟩ := rangeListGet_spec cs.hr
  obtain ⟨pts, hmap⟩ := (allPoints_iff e).1 he
  have ⟨hl, hle⟩ := mapM_point?_eq hmap
  rcases (csHas_iff_mem cs pts hle hl).1 h with ⟨c, rfl, hcMem⟩ | ⟨_, hm⟩
  · obtain ⟨k, hk⟩ := hex c hcMem
    have hkLt : k < rangesCount cs.ranges := by rw [rangesCount_eq]; exact (hs k c hk).1
    refine ⟨.int k, #[.int c], ?_, by simp [seqList_eq, hl]⟩
    change csGet cs (.int k) = some #[.int c]; unfold csGet; simp [MathVal.idx, hkLt, rangesGet_eq, hk]
  · obtain ⟨idx, hidx⟩ := cs.strings.property.mem_keys pts |>.1 hm
    let k := rangesCount cs.ranges + idx
    have hnot : ¬ k < rangesCount cs.ranges := by omega
    refine ⟨.int k, (pts.map (fun c : Nat => MathVal.int c)).toArray, ?_, by simp [seqList_eq, hl]⟩
    change csGet cs (.int k) = some _; unfold csGet
    simp only [MathVal.idx, Int.natCast_nonneg, ↓reduceIte, Option.bind_eq_bind, Option.bind_some, Option.pure_def]
    dsimp only [WMap.keys]
    simp [hnot, show k - rangesCount cs.ranges = idx by omega, hidx]

theorem csAllSingle_iff_law (cs : CharSet) :
    Impl.csAllSingle cs = true ↔ ∀ i e, Impl.csGet cs i = some e → Impl.seqLen e = Impl.ofNat 1 := by
  change csAllSingle cs = true ↔ ∀ i e, csGet cs i = some e → MathVal.int e.size = .int 1
  unfold csAllSingle
  constructor
  · intro hempty i e hg
    have hemp : cs.strings.keys.size = 0 := by simpa [Array.isEmpty] using hempty
    obtain ⟨_, _, ⟨_, _, _, rfl⟩ | ⟨_, _, hs, _⟩⟩ := parseGet hg
    · rfl
    · have := (Array.getElem?_eq_some_iff.1 hs).1; omega
  · intro hlen
    exact Classical.byContradiction fun hne => by
      have hne0 : cs.strings.keys.size ≠ 0 := fun hz => hne (by simp [Array.isEmpty, hz])
      have hpos : 0 < cs.strings.keys.size := Nat.pos_of_ne_zero hne0
      let s := cs.strings.keys[0]
      have hsGet : cs.strings.keys[0]? = some s := Array.getElem?_eq_getElem hpos
      have hm := (wmap_mem_keys cs.strings s).1 (Array.mem_toList_iff.2 (Array.getElem_mem hpos))
      have hsne1 := (cs.hs s hm).1
      let k := rangesCount cs.ranges
      have hg : csGet cs (.int k) = some (s.map (fun c : Nat => MathVal.int c)).toArray := by
        unfold csGet; dsimp only [WMap.keys] at hsGet ⊢
        simp [MathVal.idx, show k - rangesCount cs.ranges = 0 from Nat.sub_self _,
          show ¬ k < rangesCount cs.ranges from Nat.lt_irrefl _, hsGet]
      have h1 := hlen (.int k) _ hg
      simp at h1; exact hsne1 (by omega)

theorem csHas_singles_law (cs : CharSet) (e : Array MathVal) (he : Model.allPoints Impl e) :
    Impl.csHas (Impl.csSingles cs) e = true ↔ Impl.csHas cs e = true ∧ Impl.seqLen e = Impl.ofNat 1 := by
  obtain ⟨pts, hmap⟩ := (allPoints_iff e).1 he
  have ⟨hl, hle⟩ := mapM_point?_eq hmap
  rw [csHas_iff_mem _ pts hle hl, csHas_iff_mem cs pts hle hl]
  have hlen : (Impl.seqLen e = Impl.ofNat 1) ↔ pts.length = 1 := by
    change MathVal.int e.size = .int 1 ↔ _
    have := congrArg List.length hl; simp only [Array.length_toList, List.length_map] at this
    exact ⟨fun h => by have := MathVal.int.inj h; omega, fun h => by congr 1; omega⟩
  rw [hlen]
  simp only [csSingles, wmap_empty_get, Option.isSome_none, Bool.false_eq_true, and_false, or_false]
  constructor
  · rintro ⟨c, rfl, hm⟩; exact ⟨.inl ⟨c, rfl, hm⟩, rfl⟩
  · rintro ⟨⟨c, rfl, hm⟩ | ⟨hne, _⟩, hl1⟩; exact ⟨c, rfl, hm⟩; exact absurd hl1 hne

private theorem mapM_nat_congr {l : List MathVal} {r : List Nat} (f g : MathVal → Option Nat)
    (hf : ∀ x, f x = match x with | .int i => if 0 ≤ i then some i.toNat else none | _ => none)
    (hg : ∀ x, g x = match x with | .int i => if 0 ≤ i then some i.toNat else none | _ => none)
    (h : l.mapM f = some r) : l.mapM g = some r := by
  have hfg : f = g := funext fun x => (hf x).trans (hg x).symm
  exact hfg ▸ h

theorem csFromProp_some_law (p v : Array MathVal) :
    (Impl.csFromProp p v).isSome = (Impl.propSet p v).isSome := by
  have isS : ∀ {α} (o : Option α), o.isSome = true ↔ ∃ x, o = some x := fun o => by cases o <;> simp
  apply Bool.eq_iff_iff.2
  rw [isS, isS]
  constructor
  · rintro ⟨cs, h⟩
    change csFromProp p v = some cs at h; unfold csFromProp at h
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨pn, hp, vn, hv, ⟨rs0, ss0⟩, hpv, hif⟩ := h
    let rs := rs0.mergeSort fun x y => x.1 ≤ y.1
    let ss := ss0.mergeSort fun x y => PropSets.key x ≤ PropSets.key y
    have hguard : (PropSets.rangesOk rs && PropSets.stringsOk ss) = true := by
      split at hif
      · rename_i hg; exact hg
      · cases hif
    refine ⟨(((PropSets.expand rs).map ([·]) ++ ss).map fun e => (e.map fun (n : Nat) => MathVal.int n).toArray).toArray, ?_⟩
    change (do
      let nat : MathVal → Option Nat := fun | .int i => if 0 ≤ i then some i.toNat else none | _ => none
      let es ← PropSets.elements (← p.toList.mapM nat) (← v.toList.mapM nat)
      return (es.map fun e => (e.map fun (n : Nat) => MathVal.int n).toArray).toArray) = some _
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq]
    refine ⟨pn, mapM_nat_congr _ _ (fun x => by cases x <;> rfl) (fun x => by cases x <;> rfl) hp,
      vn, mapM_nat_congr _ _ (fun x => by cases x <;> rfl) (fun x => by cases x <;> rfl) hv,
      (PropSets.expand rs).map ([·]) ++ ss, ?_, rfl⟩
    simpa [PropSets.elements, hpv, rs, ss, Bool.and_eq_true] using hguard
  · rintro ⟨es, h⟩
    change (do
      let nat : MathVal → Option Nat := fun | .int i => if 0 ≤ i then some i.toNat else none | _ => none
      let es' ← PropSets.elements (← p.toList.mapM nat) (← v.toList.mapM nat)
      return (es'.map fun e => (e.map fun (n : Nat) => MathVal.int n).toArray).toArray) = some es at h
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at h
    obtain ⟨pn, hp, vn, hv, res, hpe, rfl⟩ := h
    unfold PropSets.elements at hpe
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at hpe
    obtain ⟨⟨rs0, ss0⟩, hpv, hif⟩ := hpe
    let rs := rs0.mergeSort fun x y => x.1 ≤ y.1
    let ss := ss0.mergeSort fun x y => PropSets.key x ≤ PropSets.key y
    have hguard : (PropSets.rangesOk rs && PropSets.stringsOk ss) = true := by
      split at hif
      · rename_i hg; exact hg
      · cases hif
    have ⟨hrok, hsok⟩ : PropSets.rangesOk rs = true ∧ PropSets.stringsOk ss = true := by simpa [Bool.and_eq_true] using hguard
    have ⟨_, hsAll⟩ := PropSets.strings_ok hsok
    refine ⟨{
      ranges := coalesceRanges rs
      strings := ss.foldl (fun m s => m.put s ()) WMap.empty
      hr := (coalesceRanges_ok rs hrok).1
      hs := by
        intro s hs'
        rw [wmap_foldl_put] at hs'
        rcases hs' with hemp | hmem
        · simp [WMap.get, WMap.empty, OMap.get, OMap.empty] at hemp
        · have ⟨h2, hle⟩ := hsAll s hmem
          exact ⟨by omega, hle⟩ }, ?_⟩
    change csFromProp p v = some _
    unfold csFromProp
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff]
    refine ⟨pn, mapM_nat_congr _ _ (fun x => by cases x <;> rfl) (fun x => by cases x <;> rfl) hp,
      vn, mapM_nat_congr _ _ (fun x => by cases x <;> rfl) (fun x => by cases x <;> rfl) hv,
      (rs0, ss0), hpv, ?_⟩
    simp [rs, ss, hguard]

theorem csHas_fromProp_law (p v : Array MathVal) (cs : CharSet) (e : Array MathVal)
    (h : Impl.csFromProp p v = some cs) (he : Model.allPoints Impl e) :
    Impl.csHas cs e = true ↔
      ∃ es i e', Impl.propSet p v = some es ∧ Impl.seqGet es i = some e' ∧
        seqList (M := Impl) e' = seqList (M := Impl) e := by
  obtain ⟨pts, hmap⟩ := (allPoints_iff e).1 he
  have ⟨hl, hle⟩ := mapM_point?_eq hmap
  change csFromProp p v = some cs at h; unfold csFromProp at h
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨pn, hp, vn, hv, ⟨rs0, ss0⟩, hpv, hif⟩ := h
  let rs := rs0.mergeSort fun x y => x.1 ≤ y.1
  let ss := ss0.mergeSort fun x y => PropSets.key x ≤ PropSets.key y
  have ⟨hguard, hcs1, hcs2⟩ : (PropSets.rangesOk rs && PropSets.stringsOk ss) = true ∧
      cs.ranges = coalesceRanges rs ∧
      cs.strings = ss.foldl (fun m s => m.put s ()) WMap.empty := by
    change (if h : PropSets.rangesOk rs && PropSets.stringsOk ss then some _ else none) = some cs at hif
    split at hif
    · rename_i hg; cases hif; exact ⟨hg, rfl, rfl⟩
    · cases hif
  have ⟨hrok, hsok⟩ : PropSets.rangesOk rs = true ∧ PropSets.stringsOk ss = true := by simpa [Bool.and_eq_true] using hguard
  have ⟨_, hcMem⟩ := coalesceRanges_ok rs hrok
  have ⟨_, hsAll⟩ := PropSets.strings_ok hsok
  have hps : Impl.propSet p v = some (((PropSets.expand rs).map ([·]) ++ ss).map (fun x => (x.map (fun n : Nat => MathVal.int n)).toArray)).toArray := by
    change (do
      let nat : MathVal → Option Nat := fun | .int i => if 0 ≤ i then some i.toNat else none | _ => none
      let es ← PropSets.elements (← p.toList.mapM nat) (← v.toList.mapM nat)
      return (es.map fun e => (e.map fun (n : Nat) => MathVal.int n).toArray).toArray) = some _
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff]
    refine ⟨pn, mapM_nat_congr _ _ (fun x => by cases x <;> rfl) (fun x => by cases x <;> rfl) hp,
      vn, mapM_nat_congr _ _ (fun x => by cases x <;> rfl) (fun x => by cases x <;> rfl) hv,
      (PropSets.expand rs).map ([·]) ++ ss, ?_, rfl⟩
    simp [PropSets.elements, hpv, rs, ss, hrok, hsok]
  rw [csHas_iff_mem _ pts hle hl, hcs1, hcs2, hps]
  simp only [hcMem, wmap_foldl_put, wmap_empty_get, Option.isSome_none, Bool.false_eq_true, false_or]
  constructor
  · rintro (⟨c, rfl, hcExp⟩ | ⟨_, hss⟩)
    · have hm : ([c] : List Nat) ∈ (PropSets.expand rs).map ([·]) ++ ss := List.mem_append.2 (.inl (List.mem_map.2 ⟨c, hcExp, rfl⟩))
      obtain ⟨idx, hidx, hidxEq⟩ := List.mem_iff_getElem.1 hm
      refine ⟨_, .int idx, #[.int c], rfl, ?_, by simp [seqList_eq, hl]⟩
      simp only [MathVal.idx, Int.natCast_nonneg, ↓reduceIte, Int.toNat_natCast, Option.bind_eq_bind,
        Option.bind_some, List.getElem?_toArray, List.getElem?_map, List.getElem?_eq_getElem hidx, hidxEq]
      rfl
    · have hm : pts ∈ (PropSets.expand rs).map ([·]) ++ ss := List.mem_append.2 (.inr hss)
      obtain ⟨idx, hidx, hidxEq⟩ := List.mem_iff_getElem.1 hm
      refine ⟨_, .int idx, (pts.map (fun n : Nat => MathVal.int n)).toArray, rfl, ?_, by simp [seqList_eq, hl]⟩
      simp only [MathVal.idx, Int.natCast_nonneg, ↓reduceIte, Int.toNat_natCast, Option.bind_eq_bind,
        Option.bind_some, List.getElem?_toArray, List.getElem?_map, List.getElem?_eq_getElem hidx, hidxEq]
      rfl
  · rintro ⟨es, i, e', hEq, hget, hseq⟩; cases hEq
    obtain ⟨idx, rfl, _, hig⟩ := seqGet_idx hget
    simp only [List.getElem?_toArray, List.getElem?_map, Option.map_eq_some_iff] at hig
    obtain ⟨u, hu, rfl⟩ := hig
    have huEq : u = pts := int_map_inj (by simpa [seqList_eq, hl] using hseq)
    subst huEq
    rcases List.mem_append.1 (List.mem_of_getElem? hu) with h1 | h2
    · obtain ⟨c, hc, hce⟩ := List.mem_map.1 h1; subst hce; exact .inl ⟨c, rfl, hc⟩
    · exact .inr ⟨by have := (hsAll u h2).1; omega, h2⟩

end Engine.Impl
