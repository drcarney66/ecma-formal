module

public import Engine.Parse.Core
public import Ecma.Spec.Program
public import Ecma.Grammar.Derives

@[expose] public section

/-!
# Soundness of `Engine.Parse`'s lookup tables and grammar invariants (`parseTablesOk`)

From `parseTablesOk = true`, every fast lookup (`altsOf`, `orderedBy`, `orderedNtsBy`, `prodIdOf`,
`isCapturing`, `isSloppy`, `virtualOk`, `ruleNt`) agrees with `Ecma.Spec.gl`, and the structural
grammar invariants (`synItemOk`, `codeItemOk`, `posBounded`) hold for every alternative in effect.
Also proves bitmask characterization of `paramBits` and `LawfulBEq` / `ctorIdx` injectivity on
`GrammarId`, `Param`, and `NT`.
-/

namespace Engine.Parse

open Ecma.Grammar

theorem grammarId_ctorIdx_inj {x y : GrammarId} (h : x.ctorIdx = y.ctorIdx) : x = y := by
  cases x <;> cases y <;> cases h <;> rfl

theorem param_ctorIdx_inj {x y : Param} (h : x.ctorIdx = y.ctorIdx) : x = y := by
  cases x <;> cases y <;> cases h <;> rfl

theorem nt_ctorIdx_inj {x y : NT} (h : x.ctorIdx = y.ctorIdx) : x = y := by
  cases hd : instDecidableEqNT x y with
  | isTrue heq => exact heq
  | isFalse _ =>
    dsimp only [instDecidableEqNT] at hd
    split at hd
    · cases hd
    · next hne => exact absurd h hne

instance : ReflBEq GrammarId where
  rfl {a} := by cases a <;> rfl

instance : LawfulBEq GrammarId where
  eq_of_beq {a b} h := by cases a <;> cases b <;> cases h <;> rfl

instance : ReflBEq Param where
  rfl {a} := by cases a <;> rfl

instance : LawfulBEq Param where
  eq_of_beq {a b} h := by cases a <;> cases b <;> cases h <;> rfl

instance : ReflBEq NT where
  rfl {a} := beq_self_eq_true a.ctorIdx

instance : LawfulBEq NT where
  eq_of_beq {_ _} h := nt_ctorIdx_inj (beq_iff_eq.mp h)

theorem glData_eq : glData = Ecma.Spec.gl := rfl

theorem prods_eq : prods = Ecma.Spec.gl.byId := rfl

theorem prodOf_eq (p : Nat) : prodOf p = Ecma.Spec.gl.byId[p]?.join := by
  unfold prodOf
  rw [prods_eq]

theorem prodIdSpecFrom_eq (s : Src) (m : List Bool) :
    prodIdSpecFrom prods s m = glData.prodId s m := rfl

theorem ctorSpecFrom_eq (s : Src) :
    ctorSpecFrom allProdsThunk.get s = glData.ctorOf s := rfl

theorem cxIdx_lt (cx : Ctx) : cxIdx cx < 32 := by
  rcases cx with ⟨m, ⟨a, b, c, d⟩⟩
  cases m <;> cases a <;> cases b <;> cases c <;> cases d <;> decide

theorem cxOfIdx_cxIdx (cx : Ctx) : cxOfIdx (cxIdx cx) = cx := by
  rcases cx with ⟨m, ⟨a, b, c, d⟩⟩
  cases m <;> cases a <;> cases b <;> cases c <;> cases d <;> rfl

theorem mem_allGrammarIds (g : GrammarId) : g ∈ allGrammarIds := by
  cases g <;> simp [allGrammarIds]

/-! ## `paramBits` characterization -/

private theorem testBit_one_shiftLeft (j k : Nat) :
    (1 <<< j).testBit k = (j == k) := by
  rw [show (1 <<< j) = 2 ^ j from by simp [Nat.shiftLeft_eq]]
  rw [Nat.testBit_two_pow]
  apply Bool.eq_iff_iff.mpr
  simp [beq_iff_eq]

theorem testBit_paramBits_foldl (ps : List Param) (acc k : Nat) :
    (ps.foldl (fun b p => b ||| (1 <<< p.ctorIdx)) acc).testBit k =
      (acc.testBit k || ps.any fun p => p.ctorIdx == k) := by
  induction ps generalizing acc with
  | nil => simp
  | cons p rest ih =>
    simp only [List.foldl_cons, ih, Nat.testBit_or, testBit_one_shiftLeft, List.any_cons, Bool.or_assoc]

theorem testBit_paramBits (ps : List Param) (p : Param) :
    (paramBits ps).testBit p.ctorIdx = ps.contains p := by
  unfold paramBits
  rw [testBit_paramBits_foldl]
  have hz : (0 : Nat).testBit p.ctorIdx = false := Nat.zero_testBit p.ctorIdx
  rw [hz, Bool.false_or]
  apply Bool.eq_iff_iff.mpr
  simp only [List.any_eq_true, beq_iff_eq, List.contains_iff_mem]
  constructor
  · rintro ⟨q, hq, hidx⟩
    exact param_ctorIdx_inj hidx ▸ hq
  · intro hp
    exact ⟨p, hp, rfl⟩

theorem contains_eq_of_paramBits {ps1 ps2 : List Param} (h : paramBits ps1 = paramBits ps2) (p : Param) :
    ps1.contains p = ps2.contains p := by
  rw [← testBit_paramBits ps1 p, ← testBit_paramBits ps2 p, h]

theorem guardHolds_eq_of_contains {ps1 ps2 : List Param}
    (h : ∀ p, ps1.contains p = ps2.contains p) (g : Guard) :
    Guard.holds ps1 g = Guard.holds ps2 g := by
  simp only [Guard.holds, h g.param]

theorem applyArgs_eq_of_contains {ps1 ps2 : List Param}
    (h : ∀ p, ps1.contains p = ps2.contains p) (args : List Arg) :
    applyArgs ps1 args = applyArgs ps2 args := by
  unfold applyArgs
  congr 1; funext a; cases a.sign <;> simp only [h a.param]

theorem mem_paramsOfArgs (args : List (Nat × Bool)) (p : Param) :
    p ∈ paramsOfArgs args ↔ (p.ctorIdx, true) ∈ args := by
  have hall : p ∈ allParams := by cases p <;> simp [allParams]
  simp [paramsOfArgs, List.mem_filter, hall]

/-! ## `definedNTs` and `allSrcs` coverage -/

private theorem foldl_dedup_mem {α : Type} [BEq α] [LawfulBEq α] (xs init : List α) (x : α) :
    x ∈ xs.foldl (fun acc y => if acc.contains y then acc else acc ++ [y]) init ↔
      x ∈ init ∨ x ∈ xs := by
  induction xs generalizing init with
  | nil => simp
  | cons y ys ih =>
    simp only [List.foldl_cons]
    by_cases hy : init.contains y = true
    · simp only [hy, ↓reduceIte, ih, List.mem_cons]
      have hmem : y ∈ init := List.contains_iff_mem.mp hy
      constructor
      · rintro (hi | hys)
        · exact Or.inl hi
        · exact Or.inr (Or.inr hys)
      · rintro (hi | rfl | hys)
        · exact Or.inl hi
        · exact Or.inl hmem
        · exact Or.inr hys
    · simp only [hy, Bool.false_eq_true, ↓reduceIte, ih, List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
      constructor
      · rintro ((hi | rfl) | hys)
        · exact Or.inl hi
        · exact Or.inr (Or.inl rfl)
        · exact Or.inr (Or.inr hys)
      · rintro (hi | rfl | hys)
        · exact Or.inl (Or.inl hi)
        · exact Or.inl (Or.inr rfl)
        · exact Or.inr hys

theorem mem_definedNTs_iff (n : NT) :
    n ∈ definedNTs ↔
      (∃ p ∈ glData.grammars, ∃ r ∈ p.2, r.lhs = n) ∨
      (∃ b ∈ glData.blocks, ∃ r ∈ b.rules, r.lhs = n) := by
  unfold definedNTs
  rw [foldl_dedup_mem]
  simp [List.mem_append, List.mem_flatMap, List.mem_map]

private theorem lookup_mem {α β : Type} [BEq α] [LawfulBEq α] {k : α} {xs : List (α × β)} {v : β}
    (h : xs.lookup k = some v) : ∃ p ∈ xs, p.1 = k ∧ p.2 = v := by
  induction xs with
  | nil => cases h
  | cons hd tl ih =>
    rcases hd with ⟨a, b⟩
    simp only [List.lookup] at h
    cases hab : k == a
    · simp only [hab] at h
      obtain ⟨p, hp, hk, hv⟩ := ih h
      exact ⟨p, List.mem_cons_of_mem _ hp, hk, hv⟩
    · simp only [hab, Option.some.injEq] at h
      exact ⟨(a, b), List.mem_cons_self .., (beq_iff_eq.mp hab).symm, h⟩

theorem mem_definedNTs_of_rulesOf {g : GrammarId} {r : Rule} (hr : r ∈ glData.rulesOf g) :
    r.lhs ∈ definedNTs := by
  unfold GL.rulesOf at hr
  cases hl : glData.grammars.lookup g with
  | none => rw [hl] at hr; cases hr
  | some rs =>
    rw [hl] at hr
    obtain ⟨p, hp, _, rfl⟩ := lookup_mem hl
    exact (mem_definedNTs_iff r.lhs).mpr (Or.inl ⟨p, hp, r, hr, rfl⟩)

theorem mem_allSrcs_of_rulesOf {g : GrammarId} {r : Rule} (hr : r ∈ glData.rulesOf g)
    {s : Src} (hs : s ∈ srcsOf g r) : s ∈ allSrcs := by
  unfold GL.rulesOf at hr
  cases hl : glData.grammars.lookup g with
  | none => rw [hl] at hr; cases hr
  | some rs =>
    rw [hl] at hr
    obtain ⟨⟨g', rs'⟩, hp, rfl, rfl⟩ := lookup_mem hl
    unfold allSrcs
    rw [List.mem_append]
    left
    rw [List.mem_flatMap]
    refine ⟨(g', rs'), hp, ?_⟩
    rw [List.mem_flatMap]
    exact ⟨r, hr, hs⟩

theorem mem_allSrcs_of_alts {cx : Ctx} {g : GrammarId} {n : NT} {s : Src}
    (hs : s ∈ glData.alts cx g n) : s ∈ allSrcs := by
  have hpin : ∀ x ∈ glData.pinned g n, x ∈ allSrcs := by
    intro x hx
    unfold GL.pinned at hx
    cases hf1 : (glData.rulesOf g).find? (·.lhs == n) with
    | some r =>
      rw [hf1] at hx
      exact mem_allSrcs_of_rulesOf (List.mem_of_find?_eq_some hf1) hx
    | none =>
      rw [hf1] at hx
      cases hb : baseGrammar g with
      | none => rw [hb] at hx; cases hx
      | some bg =>
        rw [hb] at hx
        cases hf2 : (glData.rulesOf bg).find? (·.lhs == n) with
        | none => simp [hf2] at hx
        | some r =>
          simp only [hf2, Option.map_some, Option.getD_some] at hx
          exact mem_allSrcs_of_rulesOf (List.mem_of_find?_eq_some hf2) hx
  have hov : ∀ (bs : List (Block × OverlayMode)) (acc : List Src),
      (∀ pm ∈ bs, pm.1 ∈ glData.blocks ∧ (∃ sc md cd, pm.1.kind = .overlay sc md cd)) →
      (∀ x ∈ acc, x ∈ allSrcs) →
      ∀ x ∈ bs.foldl (fun a (b, m) =>
        match b.rules.find? (·.lhs == n), m with
        | none, _ => a
        | some r, .extend => a ++ (srcsOf .annexB r).filter fun s' => !a.any (·.alt == s'.alt)
        | some r, .replace => srcsOf .annexB r) acc,
      x ∈ allSrcs := by
    intro bs
    induction bs with
    | nil => intro acc _ hacc x hx; exact hacc x hx
    | cons hd tl ih =>
      rcases hd with ⟨b, m⟩
      intro acc hbs hacc x hx
      obtain ⟨hb, sc, md, cd, hkind⟩ := hbs (b, m) (List.mem_cons_self ..)
      have hbs' := fun pm hpm => hbs pm (List.mem_cons_of_mem _ hpm)
      simp only [List.foldl_cons] at hx
      cases hfr : b.rules.find? (·.lhs == n) with
      | none =>
        rw [hfr] at hx
        exact ih acc hbs' hacc x hx
      | some r =>
        rw [hfr] at hx
        have hr : r ∈ b.rules := List.mem_of_find?_eq_some hfr
        have hsrc : ∀ y ∈ srcsOf .annexB r, y ∈ allSrcs := by
          intro y hy
          unfold allSrcs
          rw [List.mem_append]; right
          rw [List.mem_flatMap]; refine ⟨b, hb, ?_⟩
          rw [hkind]
          simp only [↓reduceIte, List.mem_flatMap]
          exact ⟨r, hr, hy⟩
        cases m with
        | extend =>
          refine ih _ hbs' (fun y hy => ?_) x hx
          rcases List.mem_append.mp hy with hya | hyf
          · exact hacc y hya
          · exact hsrc y (List.mem_filter.mp hyf).1
        | replace =>
          exact ih _ hbs' hsrc x hx
  unfold GL.alts at hs
  refine hov (glData.overlays cx g) (glData.pinned g n) (fun pm hpm => ?_) hpin s hs
  unfold GL.overlays at hpm
  split at hpm
  · cases hpm
  · rw [List.mem_filterMap] at hpm
    obtain ⟨b, hb, hfb⟩ := hpm
    cases hbk : b.kind with
    | main | supplemental _ => rw [hbk] at hfb; cases hfb
    | overlay sc md cd =>
      rw [hbk] at hfb; dsimp only at hfb
      split at hfb
      · cases hfb; exact ⟨hb, sc, md, cd, hbk⟩
      · cases hfb

theorem rulesOf_find_none_of_not_definedNTs {g : GrammarId} {n : NT} (hn : n ∉ definedNTs) :
    (glData.rulesOf g).find? (·.lhs == n) = none := by
  rw [List.find?_eq_none]
  intro r hr heq
  rw [beq_iff_eq] at heq
  exact hn (heq ▸ mem_definedNTs_of_rulesOf hr)

theorem rulesOf_any_false_of_not_definedNTs {g : GrammarId} {n : NT} (hn : n ∉ definedNTs) :
    (glData.rulesOf g).any (·.lhs == n) = false := by
  rw [Bool.eq_false_iff, ne_eq, List.any_eq_true]
  rintro ⟨r, hr, heq⟩
  rw [beq_iff_eq] at heq
  exact hn (heq ▸ mem_definedNTs_of_rulesOf hr)

theorem alts_nil_of_not_definedNTs {cx : Ctx} {g : GrammarId} {n : NT} (hn : n ∉ definedNTs) :
    glData.alts cx g n = [] := by
  have hpin : glData.pinned g n = [] := by
    unfold GL.pinned
    rw [rulesOf_find_none_of_not_definedNTs hn]
    cases baseGrammar g with
    | none => rfl
    | some b => dsimp only; rw [rulesOf_find_none_of_not_definedNTs hn]; rfl
  unfold GL.alts
  rw [hpin]
  have hov : ∀ (bs : List (Block × OverlayMode)),
      (∀ pm ∈ bs, pm.1 ∈ glData.blocks) →
      bs.foldl (fun acc (b, m) =>
        match b.rules.find? (·.lhs == n), m with
        | none, _ => acc
        | some r, .extend => acc ++ (srcsOf .annexB r).filter fun s => !acc.any (·.alt == s.alt)
        | some r, .replace => srcsOf .annexB r) [] = [] := by
    intro bs hbs
    induction bs with
    | nil => rfl
    | cons hd tl ih =>
      rcases hd with ⟨b, m⟩
      have hb : b ∈ glData.blocks := hbs (b, m) (List.mem_cons_self ..)
      have hf : b.rules.find? (·.lhs == n) = none := by
        rw [List.find?_eq_none]
        intro r hr heq
        rw [beq_iff_eq] at heq
        exact hn ((mem_definedNTs_iff n).mpr (Or.inr ⟨b, hb, r, hr, heq⟩))
      simp only [List.foldl_cons, hf]
      exact ih (fun pm hpm => hbs pm (List.mem_cons_of_mem _ hpm))
  apply hov
  intro pm hpm
  unfold GL.overlays at hpm
  split at hpm
  · cases hpm
  · rw [List.mem_filterMap] at hpm
    obtain ⟨b, hb, hfb⟩ := hpm
    cases hbk : b.kind with
    | main | supplemental _ => rw [hbk] at hfb; cases hfb
    | overlay s m c =>
      rw [hbk] at hfb
      dsimp only at hfb
      split at hfb
      · cases hfb; exact hb
      · cases hfb

private theorem foldl_altsTable_mem (cx : Ctx) (g : GrammarId) (ns : List NT)
    (hns : ∀ x ∈ ns, x ∈ definedNTs)
    (arr : Array (Option (NT × List Src)))
    (hinit : ∀ (idx : Nat) m as, arr[idx]? = some (some (m, as)) → m ∈ definedNTs) :
    ∀ (idx : Nat) m as,
      (ns.foldl (fun a n => a.setIfInBounds n.ctorIdx (some (n, glData.alts cx g n))) arr)[idx]? =
        some (some (m, as)) →
      m ∈ definedNTs := by
  induction ns generalizing arr with
  | nil => exact hinit
  | cons y ys ih =>
    apply ih (fun x hx => hns x (List.mem_cons_of_mem _ hx))
    intro idx m as h
    rw [Array.getElem?_setIfInBounds] at h
    split at h
    · split at h
      · cases h
        exact hns y (List.mem_cons_self ..)
      · cases h
    · exact hinit idx m as h

theorem altsOf_nil_of_not_definedNTs {cx : Ctx} {g : GrammarId} {n : NT} (hn : n ∉ definedNTs) :
    altsOf cx g n = [] := by
  unfold altsOf
  cases hgt : ((altsTable[cxIdx cx]?.map Thunk.get).bind fun gt => (gt[g.ctorIdx]?).bind (·[n.ctorIdx]?)).join with
  | none => rfl
  | some pair =>
    rcases pair with ⟨n', as⟩
    have hmem : n' ∈ definedNTs := by
      have hci : altsTable[cxIdx cx]? = some (Thunk.mk fun _ =>
          allGrammarIds.toArray.map fun g =>
            definedNTs.foldl (init := Array.replicate numNTs none) fun arr m =>
              arr.setIfInBounds m.ctorIdx (some (m, glData.alts (cxOfIdx (cxIdx cx)) g m))) := by
        simp [altsTable, cxIdx_lt cx]
      have hg : allGrammarIds.toArray[g.ctorIdx]? = some g := by cases g <;> rfl
      rw [hci] at hgt
      simp only [Option.map_some, Option.bind_some, Thunk.get] at hgt
      rw [Array.getElem?_map, hg] at hgt
      simp only [Option.map_some, Option.bind_some, Option.join_eq_some_iff] at hgt
      exact foldl_altsTable_mem (cxOfIdx (cxIdx cx)) g definedNTs (fun _ h => h) _
        (fun idx m as hm => by simp [Array.getElem?_replicate] at hm) n.ctorIdx n' as hgt
    have hneq : (n' == n) = false := by
      rw [Bool.eq_false_iff, ne_eq, beq_iff_eq]
      rintro rfl
      exact hn hmem
    simp [hneq]

private theorem foldl_ruleNtTable_mem (g : GrammarId) (rs : List Rule)
    (hrs : ∀ r ∈ rs, r ∈ glData.rulesOf g)
    (arr : Array (Option NT))
    (hinit : ∀ (idx : Nat) m, arr[idx]? = some (some m) → ∃ r ∈ glData.rulesOf g, r.lhs = m) :
    ∀ (idx : Nat) m,
      (rs.foldl (fun a r => a.setIfInBounds r.lhs.ctorIdx (some r.lhs)) arr)[idx]? = some (some m) →
      ∃ r ∈ glData.rulesOf g, r.lhs = m := by
  induction rs generalizing arr with
  | nil => exact hinit
  | cons y ys ih =>
    apply ih (fun r hr => hrs r (List.mem_cons_of_mem _ hr))
    intro idx m h
    rw [Array.getElem?_setIfInBounds] at h
    split at h
    · split at h
      · cases h
        exact ⟨y, hrs y (List.mem_cons_self ..), rfl⟩
      · cases h
    · exact hinit idx m h

theorem ruleNt_mem_rulesOf {g : GrammarId} {idx : Nat} {m : NT} (h : ruleNt g idx = some m) :
    ∃ r ∈ glData.rulesOf g, r.lhs = m := by
  unfold ruleNt at h
  simp only [ruleNtTable, Thunk.get] at h
  have hg : allGrammarIds.toArray[g.ctorIdx]? = some g := by
    cases g <;> rfl
  rw [Array.getElem?_map, hg] at h
  simp only [Option.map_some, Option.bind_some, Option.join_eq_some_iff] at h
  exact foldl_ruleNtTable_mem g (glData.rulesOf g) (fun _ hr => hr) _
    (fun i m' hm => by simp [Array.getElem?_replicate] at hm) idx m h

theorem mem_definedNTs_of_alts {cx : Ctx} {g : GrammarId} {n : NT} {s : Src}
    (hs : s ∈ glData.alts cx g n) : n ∈ definedNTs :=
  Classical.byContradiction fun hnot => by
    rw [alts_nil_of_not_definedNTs hnot] at hs
    cases hs

/-! ## Extracting equations and invariants from `parseTablesOk = true` -/

private theorem split_parseTablesOk (hok : parseTablesOk = true) :
    definedNTs.all (·.ctorIdx < numNTs) = true ∧
    srcsCheck = true ∧
    cxsCheck = true ∧
    ruleNoneCheck = true ∧
    synCheck = true ∧
    codeCheck = true ∧
    fastCheck = true := by
  unfold parseTablesOk checkParseTables at hok
  simp only [Bool.and_eq_true, and_assoc] at hok
  exact hok

theorem altsOf_eq (hok : parseTablesOk = true) (cx : Ctx) (g : GrammarId) (n : NT) :
    altsOf cx g n = Ecma.Spec.gl.alts cx g n := by
  rw [← glData_eq]
  by_cases hn : n ∈ definedNTs
  · have hcxs := (split_parseTablesOk hok).2.2.1
    unfold cxsCheck at hcxs
    have hci := List.all_eq_true.mp hcxs (cxIdx cx) (List.mem_range.mpr (cxIdx_lt cx))
    rw [cxOfIdx_cxIdx] at hci
    simp only [Bool.and_eq_true] at hci
    have hg := List.all_eq_true.mp hci.2 g (mem_allGrammarIds g)
    simp only [Bool.and_eq_true] at hg
    have hnt := List.all_eq_true.mp hg.2 n hn
    simp only [Bool.and_eq_true] at hnt
    exact of_decide_eq_true hnt.1.1
  · rw [altsOf_nil_of_not_definedNTs hn, alts_nil_of_not_definedNTs hn]

theorem orderedBy_eq (hok : parseTablesOk = true) (cx : Ctx) (g : GrammarId) :
    orderedBy cx g = Ecma.Spec.gl.ordered cx g := by
  rw [← glData_eq]
  have hcxs := (split_parseTablesOk hok).2.2.1
  unfold cxsCheck at hcxs
  have hci := List.all_eq_true.mp hcxs (cxIdx cx) (List.mem_range.mpr (cxIdx_lt cx))
  rw [cxOfIdx_cxIdx] at hci
  simp only [Bool.and_eq_true] at hci
  have hg := List.all_eq_true.mp hci.2 g (mem_allGrammarIds g)
  simp only [Bool.and_eq_true] at hg
  exact of_decide_eq_true hg.1.1

theorem orderedNtsBy_eq (hok : parseTablesOk = true) (cx : Ctx) (g : GrammarId) :
    orderedNtsBy cx g = Ecma.Spec.gl.orderedNts cx g := by
  rw [← glData_eq]
  have hcxs := (split_parseTablesOk hok).2.2.1
  unfold cxsCheck at hcxs
  have hci := List.all_eq_true.mp hcxs (cxIdx cx) (List.mem_range.mpr (cxIdx_lt cx))
  rw [cxOfIdx_cxIdx] at hci
  simp only [Bool.and_eq_true] at hci
  have hg := List.all_eq_true.mp hci.2 g (mem_allGrammarIds g)
  simp only [Bool.and_eq_true] at hg
  exact of_decide_eq_true hg.1.2

theorem src_invariants (hok : parseTablesOk = true) {s : Src} (hs : s ∈ allSrcs) :
    ctorOfSrc s = Ecma.Spec.gl.ctorOf s ∧
    s.alt.opts = (s.alt.rhs.filter fun | .sym _ true => true | _ => false).length ∧
    (∀ m ∈ masks s.alt.opts,
      prodIdOf s m = Ecma.Spec.gl.prodId s m ∧
      ∃ id P, Ecma.Spec.gl.prodId s m = some id ∧ prodOf id = some P ∧
        P.grammar = s.grammar ∧ P.rule = s.rule ∧ P.alt = s.idx ∧ P.mask = m) ∧
    (∀ it ∈ s.alt.rhs, srcItemTermOk it = true) := by
  rw [← glData_eq]
  have hsrcs := (split_parseTablesOk hok).2.1
  unfold srcsCheck at hsrcs
  have hs' := List.all_eq_true.mp hsrcs s hs
  simp only [Bool.and_eq_true] at hs'
  obtain ⟨⟨⟨hterm, hctor⟩, hopts⟩, hms⟩ := hs'
  rw [ctorSpecFrom_eq] at hctor
  refine ⟨of_decide_eq_true hctor, of_decide_eq_true hopts, fun m hm => ?_,
    fun it hit => List.all_eq_true.mp hterm it hit⟩
  have hm' := List.all_eq_true.mp hms m hm
  simp only [Bool.and_eq_true] at hm'
  obtain ⟨⟨hpeq, hsome⟩, hmatch⟩ := hm'
  rw [prodIdSpecFrom_eq] at hpeq hsome hmatch
  obtain ⟨id, hid⟩ := Option.isSome_iff_exists.mp hsome
  rw [hid] at hmatch
  dsimp only [Bind.bind, Option.bind] at hmatch
  cases hpo : prodOf id with
  | none => rw [hpo] at hmatch; cases hmatch
  | some P =>
    rw [hpo] at hmatch
    obtain ⟨h1, h2, h3, h4⟩ := of_decide_eq_true hmatch
    exact ⟨of_decide_eq_true hpeq, id, P, hid, hpo, h1, h2, h3, h4⟩

theorem srcItemTermOk_of_mem (hok : parseTablesOk = true) {cx : Ctx} {g : GrammarId} {n : NT} {s : Src}
    (hs : s ∈ Ecma.Spec.gl.alts cx g n) {it : Item} (hit : it ∈ s.alt.rhs) :
    srcItemTermOk it = true := by
  rw [← glData_eq] at hs
  exact (src_invariants hok (mem_allSrcs_of_alts hs)).2.2.2 it hit

theorem alt_lhs_and_opts (hok : parseTablesOk = true) {cx : Ctx} {g : GrammarId} {n : NT} {s : Src}
    (hs : s ∈ Ecma.Spec.gl.alts cx g n) :
    s.rule.lhs = n ∧
    s.alt.opts = (s.alt.rhs.filter fun | .sym _ true => true | _ => false).length := by
  rw [← glData_eq] at hs
  have hn := mem_definedNTs_of_alts hs
  have hcxs := (split_parseTablesOk hok).2.2.1
  unfold cxsCheck at hcxs
  have hci := List.all_eq_true.mp hcxs (cxIdx cx) (List.mem_range.mpr (cxIdx_lt cx))
  rw [cxOfIdx_cxIdx] at hci
  simp only [Bool.and_eq_true] at hci
  have hg := List.all_eq_true.mp hci.2 g (mem_allGrammarIds g)
  simp only [Bool.and_eq_true] at hg
  have hnt := List.all_eq_true.mp hg.2 n hn
  simp only [Bool.and_eq_true] at hnt
  have hs' := List.all_eq_true.mp hnt.2 s hs
  simp only [Bool.and_eq_true, beq_iff_eq] at hs'
  exact ⟨hs'.1, (src_invariants hok (mem_allSrcs_of_alts hs)).2.1⟩

theorem prodIdOf_spec (hok : parseTablesOk = true) {cx : Ctx} {g : GrammarId} {n : NT} {s : Src}
    (hs : s ∈ Ecma.Spec.gl.alts cx g n) {m : List Bool} (hm : m ∈ masks s.alt.opts) :
    prodIdOf s m = Ecma.Spec.gl.prodId s m ∧
    ∃ id P, Ecma.Spec.gl.prodId s m = some id ∧ prodOf id = some P ∧
      P.grammar = s.grammar ∧ P.rule = s.rule ∧ P.alt = s.idx ∧ P.mask = m ∧
      (Ecma.Spec.gl.alts cx g P.rule.lhs).find?
        (fun ef => ef.grammar == P.grammar && ef.idx == P.alt && ef.rule == P.rule) = some s := by
  rw [← glData_eq] at hs
  have ⟨hpeq, id, P, hid, hpo, h1, h2, h3, h4⟩ := (src_invariants hok (mem_allSrcs_of_alts hs)).2.2.1 m hm
  have hn := mem_definedNTs_of_alts hs
  have hcxs := (split_parseTablesOk hok).2.2.1
  unfold cxsCheck at hcxs
  have hci := List.all_eq_true.mp hcxs (cxIdx cx) (List.mem_range.mpr (cxIdx_lt cx))
  rw [cxOfIdx_cxIdx] at hci
  simp only [Bool.and_eq_true] at hci
  have hg := List.all_eq_true.mp hci.2 g (mem_allGrammarIds g)
  simp only [Bool.and_eq_true] at hg
  have hnt := List.all_eq_true.mp hg.2 n hn
  simp only [Bool.and_eq_true] at hnt
  have hs' := List.all_eq_true.mp hnt.2 s hs
  simp only [Bool.and_eq_true, beq_iff_eq] at hs'
  have hm' := List.all_eq_true.mp hs'.2 m hm
  have hpoid : prodIdOf s m = some id := hpeq.trans hid
  rw [hpoid] at hm'
  dsimp only [Bind.bind, Option.bind] at hm'
  rw [hpo] at hm'
  have hfind := of_decide_eq_true hm'
  have hlhs : P.rule.lhs = n := by rw [h2, hs'.1]
  rw [← hlhs, glData_eq] at hfind
  exact ⟨hpeq, id, P, hid, hpo, h1, h2, h3, h4, hfind⟩

theorem ruleNt_of_rulesOf (hok : parseTablesOk = true) {g : GrammarId} {goal : NT}
    (h : (Ecma.Spec.gl.rulesOf g).any (·.lhs == goal) = true) :
    ruleNt g goal.ctorIdx = some goal := by
  rw [← glData_eq] at h
  obtain ⟨r, hr, heq⟩ := List.any_eq_true.mp h
  rw [beq_iff_eq] at heq; subst heq
  have hn := mem_definedNTs_of_rulesOf hr
  have hcxs := (split_parseTablesOk hok).2.2.1
  unfold cxsCheck at hcxs
  have hci := List.all_eq_true.mp hcxs 0 (by decide)
  simp only [Bool.and_eq_true] at hci
  have hg := List.all_eq_true.mp hci.2 g (mem_allGrammarIds g)
  simp only [Bool.and_eq_true] at hg
  have hnt := List.all_eq_true.mp hg.2 r.lhs hn
  simp only [Bool.and_eq_true] at hnt
  have heqv := of_decide_eq_true hnt.1.2
  exact Eq.mpr heqv h

theorem ruleNt_some_imp (hok : parseTablesOk = true) {g : GrammarId} {idx : Nat} {lhs : NT}
    (h : ruleNt g idx = some lhs) :
    lhs.ctorIdx = idx ∧ (Ecma.Spec.gl.rulesOf g).any (·.lhs == lhs) = true := by
  rw [← glData_eq]
  have hidx : idx < numNTs := Classical.byContradiction fun hge => by
    unfold ruleNt at h
    simp only [ruleNtTable, Thunk.get] at h
    have hg : allGrammarIds.toArray[g.ctorIdx]? = some g := by cases g <;> rfl
    rw [Array.getElem?_map, hg] at h
    simp only [Option.map_some, Option.bind_some] at h
    have hsz : ((glData.rulesOf g).foldl (fun arr r => arr.setIfInBounds r.lhs.ctorIdx (some r.lhs))
        (Array.replicate numNTs none)).size = numNTs := by
      have : ∀ (rs : List Rule) (arr : Array (Option NT)),
          (rs.foldl (fun a r => a.setIfInBounds r.lhs.ctorIdx (some r.lhs)) arr).size = arr.size := by
        intro rs arr; induction rs generalizing arr with
        | nil => rfl
        | cons x xs ih => rw [List.foldl_cons, ih, Array.size_setIfInBounds]
      rw [this, Array.size_replicate]
    rw [Array.getElem?_eq_none (by omega)] at h
    cases h
  have hrn := (split_parseTablesOk hok).2.2.2.1
  unfold ruleNoneCheck at hrn
  have hrg := List.all_eq_true.mp hrn g (mem_allGrammarIds g)
  have hri := List.all_eq_true.mp hrg idx (List.mem_range.mpr hidx)
  rw [h] at hri
  simp only [Bool.and_eq_true, beq_iff_eq] at hri
  exact hri

theorem hasRule_iff (hok : parseTablesOk = true) (g : GrammarId) (idx : Nat) :
    hasRule g idx = true ↔ ∃ lhs, lhs.ctorIdx = idx ∧ (Ecma.Spec.gl.rulesOf g).any (·.lhs == lhs) = true := by
  unfold hasRule
  cases hr : ruleNt g idx with
  | none =>
    simp only [Option.isSome_none, Bool.false_eq_true, false_iff, not_exists, not_and]
    rintro lhs rfl hmem
    have := ruleNt_of_rulesOf hok hmem
    rw [hr] at this; cases this
  | some lhs =>
    simp only [Option.isSome_some, true_iff]
    exact ⟨lhs, ruleNt_some_imp hok hr⟩

private theorem zipIdx_id_lt {α : Type} {xs : List α} {p : α × Nat} (hp : p ∈ xs.zipIdx) :
    p.2 < xs.length := by
  have hgen : ∀ (l : List α) (k : Nat), p ∈ l.zipIdx k → p.2 < k + l.length := by
    intro l
    induction l with
    | nil => intro k h; cases h
    | cons _ tl ih =>
      intro k h
      rcases List.mem_cons.mp h with rfl | htl
      · simp
      · have := ih (k + 1) htl
        simp; omega
  simpa using hgen xs 0 hp

private theorem list_toArray_getElem? {α : Type} (xs : List α) (i : Nat) :
    xs.toArray[i]? = xs[i]? := by
  simp

theorem isCapturing_iff (_ : parseTablesOk = true) (id : Nat) :
    isCapturing id = true ↔ id ∈ Ecma.Spec.gl.capturingIds := by
  rw [← glData_eq]
  unfold isCapturing capturingArr Thunk.get
  by_cases hlt : id < prods.size
  · rw [Array.getElem?_map, list_toArray_getElem?, List.getElem?_range hlt]
    simp
  · rw [Array.getElem?_eq_none (by simp; omega)]
    simp only [Option.getD_none, Bool.false_eq_true, false_iff]
    intro hmem
    unfold GL.capturingIds at hmem
    rw [List.mem_filterMap] at hmem
    obtain ⟨⟨o, id'⟩, hz, hb⟩ := hmem
    have hlt' : id' < glData.byId.toList.length := zipIdx_id_lt hz
    rw [Array.length_toList] at hlt'
    cases o with
    | none => cases hb
    | some p =>
      dsimp only [Option.bind] at hb
      split at hb
      · cases hb; simp [prods_eq, ← glData_eq] at hlt; omega
      · cases hb

theorem isSloppy_iff (_ : parseTablesOk = true) (id : Nat) :
    isSloppy id = true ↔ id ∈ Ecma.Spec.gl.sloppyIds := by
  rw [← glData_eq]
  unfold isSloppy sloppyArr Thunk.get
  by_cases hlt : id < prods.size
  · rw [Array.getElem?_map, list_toArray_getElem?, List.getElem?_range hlt]
    simp
  · rw [Array.getElem?_eq_none (by simp; omega)]
    simp only [Option.getD_none, Bool.false_eq_true, false_iff]
    intro hmem
    unfold GL.sloppyIds at hmem
    rw [List.mem_filterMap] at hmem
    obtain ⟨⟨o, id'⟩, hz, hb⟩ := hmem
    have hlt' : id' < glData.byId.toList.length := zipIdx_id_lt hz
    rw [Array.length_toList] at hlt'
    cases o with
    | none => cases hb
    | some p =>
      dsimp only [Option.bind] at hb
      split at hb
      · cases hb; simp [prods_eq, ← glData_eq] at hlt; omega
      · cases hb

theorem semiAllowedSpec_iff (s : Src) (k : Nat) (paren : Bool) :
    semiAllowedSpec s k paren = true ↔ semiAllowed Ecma.Spec.gl s k paren := by
  unfold semiAllowedSpec semiAllowedAt semiAllowed
  rw [← glData_eq]
  cases hc : glData.ctorOf s with
  | none =>
    simp only [Bool.false_eq_true, false_iff, not_exists, not_and]
    intro c cls hc'; cases hc'
  | some c =>
    simp only [List.any_eq_true, Bool.and_eq_true, beq_iff_eq]
    constructor
    · rintro ⟨⟨c', k', cls⟩, hmem, ⟨rfl, rfl⟩, hcls⟩
      refine ⟨c', cls, rfl, hmem, ?_⟩
      cases cls <;> simp at hcls ⊢ <;> exact hcls
    · rintro ⟨c', cls, hc', hmem, hcls⟩
      cases hc'
      refine ⟨(c, k, cls), hmem, ⟨rfl, rfl⟩, ?_⟩
      cases cls <;> simp at hcls ⊢ <;> exact hcls

theorem orderedBy_syntactic_false (hok : parseTablesOk = true) (cx : Ctx) :
    orderedBy cx .syntactic = false := by
  have hsyn := (split_parseTablesOk hok).2.2.2.2.1
  unfold synCheck at hsyn
  have hci := List.all_eq_true.mp hsyn (cxIdx cx) (List.mem_range.mpr (cxIdx_lt cx))
  rw [cxOfIdx_cxIdx] at hci
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at hci
  exact hci.1

theorem virtualOk_iff (hok : parseTablesOk = true) {cx : Ctx} {n : NT} {s : Src}
    (hs : s ∈ Ecma.Spec.gl.alts cx .syntactic n) {k : Nat} (_ : k < s.alt.rhs.length) (paren : Bool) :
    virtualOk s k paren = true ↔ semiAllowed Ecma.Spec.gl s k paren := by
  rw [← glData_eq] at hs
  have hctor : ctorOfSrc s = glData.ctorOf s := (src_invariants hok (mem_allSrcs_of_alts hs)).1
  have hveq : virtualOk s k paren = semiAllowedSpec s k paren :=
    congrArg (fun o => semiAllowedAt o k paren) hctor
  rw [hveq]
  exact semiAllowedSpec_iff s k paren

theorem syn_nonempty_in_rulesOf (hok : parseTablesOk = true) {cx : Ctx} {n : NT}
    (h : Ecma.Spec.gl.alts cx .syntactic n ≠ []) :
    (Ecma.Spec.gl.rulesOf .syntactic).any (·.lhs == n) = true := by
  rw [← glData_eq] at h ⊢
  have hn : n ∈ definedNTs := Classical.byContradiction fun hnot => h (alts_nil_of_not_definedNTs hnot)
  have hsyn := (split_parseTablesOk hok).2.2.2.2.1
  unfold synCheck at hsyn
  have hci := List.all_eq_true.mp hsyn (cxIdx cx) (List.mem_range.mpr (cxIdx_lt cx))
  rw [cxOfIdx_cxIdx] at hci
  simp only [Bool.and_eq_true] at hci
  have hnt := List.all_eq_true.mp hci.2 n hn
  simp only [Bool.and_eq_true, Bool.or_eq_true, List.isEmpty_iff] at hnt
  rw [altsOf_eq hok, ← glData_eq] at hnt
  rcases hnt.1 with hempty | hmem
  · exact absurd hempty h
  · exact hmem

theorem synItemOk_of_mem (hok : parseTablesOk = true) {cx : Ctx} {n : NT} {s : Src}
    (hs : s ∈ Ecma.Spec.gl.alts cx .syntactic n) {it : Item} (hit : it ∈ s.alt.rhs) :
    synItemOk cx it = true := by
  rw [← glData_eq] at hs
  have hn := mem_definedNTs_of_alts hs
  have hsyn := (split_parseTablesOk hok).2.2.2.2.1
  unfold synCheck at hsyn
  have hci := List.all_eq_true.mp hsyn (cxIdx cx) (List.mem_range.mpr (cxIdx_lt cx))
  rw [cxOfIdx_cxIdx] at hci
  simp only [Bool.and_eq_true] at hci
  have hnt := List.all_eq_true.mp hci.2 n hn
  simp only [Bool.and_eq_true] at hnt
  rw [altsOf_eq hok, ← glData_eq] at hnt
  have hs' := List.all_eq_true.mp hnt.2 s hs
  exact List.all_eq_true.mp hs' it hit

theorem codeItemOk_of_mem (hok : parseTablesOk = true) {cx : Ctx} {g : GrammarId}
    (hg : g ∈ codeGrammars) {n : NT} {s : Src}
    (hs : s ∈ Ecma.Spec.gl.alts cx g n) {it : Item} (hit : it ∈ s.alt.rhs) :
    codeItemOk cx g it = true := by
  rw [← glData_eq] at hs
  have hn := mem_definedNTs_of_alts hs
  have hcode := (split_parseTablesOk hok).2.2.2.2.2.1
  unfold codeCheck at hcode
  have hci := List.all_eq_true.mp hcode (cxIdx cx) (List.mem_range.mpr (cxIdx_lt cx))
  rw [cxOfIdx_cxIdx] at hci
  have hcg := List.all_eq_true.mp hci g hg
  have hnt := List.all_eq_true.mp hcg n hn
  rw [altsOf_eq hok, ← glData_eq] at hnt
  have hs' := List.all_eq_true.mp hnt s hs
  exact List.all_eq_true.mp hs' it hit

theorem fast_invariants (hok : parseTablesOk = true) (cx : Ctx) :
    ruleNt .syntactic NT.StringLiteral.ctorIdx = none ∧
    (codeGrammars.filterMap fun g => (ruleNt g NT.StringLiteral.ctorIdx).map ((g, ·))) =
      [(.lexical, .StringLiteral)] ∧
    ruleNt .syntactic NT.JSONText.ctorIdx = none ∧
    (codeGrammars.filterMap fun g => (ruleNt g NT.JSONText.ctorIdx).map ((g, ·))) =
      [(.json, .JSONText)] ∧
    orderedBy cx .lexical = false ∧
    orderedBy cx .numericString = false ∧
    orderedBy cx .json = false ∧
    (∀ s ∈ Ecma.Spec.gl.alts cx .lexical .StringLiteral,
      match s.alt.rhs with
      | .sym (.t (.text "\"" _)) false :: _ | .sym (.t (.text "'" _)) false :: _ => True
      | _ => False) ∧
    (∀ n, Ecma.Spec.gl.alts cx .json n = Ecma.Spec.gl.pinned .json n) := by
  have hf := (split_parseTablesOk hok).2.2.2.2.2.2
  unfold fastCheck at hf
  simp only [Bool.and_eq_true, and_assoc] at hf
  obtain ⟨h1, h2, h3, h4, hcxs⟩ := hf
  have hci := List.all_eq_true.mp hcxs (cxIdx cx) (List.mem_range.mpr (cxIdx_lt cx))
  rw [cxOfIdx_cxIdx] at hci
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at hci
  obtain ⟨⟨⟨⟨hl, hns⟩, hj⟩, hsl⟩, hjson⟩ := hci
  refine ⟨of_decide_eq_true h1, of_decide_eq_true h2, of_decide_eq_true h3, of_decide_eq_true h4,
    hl, hns, hj, ?_, ?_⟩
  · intro s hs
    rw [altsOf_eq hok] at hsl
    have hb := List.all_eq_true.mp hsl s hs
    split at hb <;> simp_all
  · intro n
    rw [← glData_eq]
    by_cases hn : n ∈ definedNTs
    · have hjn := of_decide_eq_true (List.all_eq_true.mp hjson n hn)
      rw [altsOf_eq hok, ← glData_eq] at hjn
      exact hjn
    · rw [alts_nil_of_not_definedNTs hn]
      unfold GL.pinned
      rw [rulesOf_find_none_of_not_definedNTs hn]; rfl

end Engine.Parse
