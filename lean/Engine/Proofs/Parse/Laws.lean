module

public import Engine.Model.Parse
public import Engine.Proofs.Parse.Shape
public import Engine.Proofs.Parse.JsonText
public import Engine.Proofs.Parse.Code
public import Engine.Proofs.Parse.Strict
public import Engine.Proofs.Parse.Syntax

@[expose] public section

/-!
# Soundness and completeness of `Engine.parse`: `Ecma.Model.ParseLaws`

Proves `Engine.Impl.parseLaws`: for every invocation context `pc`, stamp `st`, code-point list
`src`, goal nonterminal `goal`, argument list `args`, and parameter list `ps` with `ParamsOf args ps`:
1. `sound`: `Engine.parse pc st (Impl.seqOfNats src) goal.ctorIdx args = some (some n)` implies
   `∃ t, (G.at pc).ParseIs Impl st goal ps src n t`.
2. `complete`: `Engine.parse pc st (Impl.seqOfNats src) goal.ctorIdx args = some none` implies
   `∀ t, ¬ (G.at pc).Parses goal ps src t`.
-/

namespace Engine.Impl

open Ecma.Grammar Engine.Model Engine.Parse
open Ecma (ParamId NtId ProdId ParseCx GrammarCtx ParamsOf)

private theorem opt_none_or_some {α : Type} (o : Option α) :
    o = none ∨ ∃ x, o = some x :=
  match o with
  | none => Or.inl rfl
  | some x => Or.inr ⟨x, rfl⟩

private theorem except_eq_err_or_ok {ε α : Type} (r : Except ε α) :
    (∃ e, r = .error e) ∨ (∃ v, r = .ok v) :=
  match r with
  | .error e => Or.inl ⟨e, rfl⟩
  | .ok v => Or.inr ⟨v, rfl⟩

private theorem list_all_congr {α : Type} {p q : α → Bool} {l : List α}
    (h : ∀ x ∈ l, p x = q x) : l.all p = l.all q := by
  induction l with
  | nil => rfl
  | cons hd tl ih =>
    simp only [List.all_cons, h hd (List.mem_cons_self ..),
      ih (fun x hx => h x (List.mem_cons_of_mem _ hx))]

theorem parseTablesOk_of_thunk (h : (!parseTablesOkThunk.get) = false) :
    parseTablesOk = true := by
  have key : ∀ (f : Unit → Bool), (Thunk.mk f).get = f () := fun _ => by simp only [Thunk.get]
  cases hb : parseTablesOkThunk.get with
  | false => rw [hb] at h; cases h
  | true => exact (key checkParseTables).symm.trans hb

/-! ## `allParams`, `paramsOfArgs`, `seqOfNats`, and `codePointsOf` -/

theorem mem_allParams (p : Param) : p ∈ allParams := by
  cases p <;> simp [allParams]

theorem mem_paramsOfArgs_iff {args : List (ParamId × Bool)} {p : Param} :
    p ∈ paramsOfArgs args ↔ (p.ctorIdx, true) ∈ args := by
  unfold paramsOfArgs
  rw [List.mem_filter, List.contains_iff_mem]
  exact ⟨fun h => h.2, fun h => ⟨mem_allParams p, h⟩⟩

theorem paramsOfArgs_iff_of_paramsOf {args : List (ParamId × Bool)} {ps : List Param}
    (hps : ParamsOf args ps) :
    ∀ p, p ∈ paramsOfArgs args ↔ p ∈ ps :=
  fun p => mem_paramsOfArgs_iff.trans (hps p).symm

theorem seqOfNats_eq (src : List Nat) :
    Impl.seqOfNats src = (src.map fun (c : Nat) => MathVal.int c).toArray := by
  apply Array.ext'
  unfold Ecma.Model.seqOfNats
  have hgen : ∀ (xs : List Nat) (acc : Array MathVal),
      (xs.foldl (fun s c => Impl.seqPush s (Impl.ofNat c)) acc).toList =
        acc.toList ++ xs.map fun (c : Nat) => MathVal.int c := by
    intro xs
    induction xs with
    | nil => intro acc; simp
    | cons c tl ih =>
      intro acc
      rw [List.foldl_cons, ih]
      change (acc.push (MathVal.int (c : Nat))).toList ++ _ = _
      rw [Array.toList_push, List.append_assoc, List.singleton_append, List.map_cons]
  rw [hgen src #[]]; simp

private def cpStep : MathVal → Option Nat
  | .int i => if 0 ≤ i ∧ i ≤ 0x10FFFF then some i.toNat else none
  | _ => none

theorem codePointsOf_some_bound {arr : Array MathVal} {cs : Array Nat}
    (h : Engine.codePointsOf arr = some cs) :
    ∀ c ∈ cs.toList, c ≤ 0x10FFFF := by
  unfold Engine.codePointsOf at h
  have harr : arr = arr.toList.toArray := by simp
  rw [harr] at h
  have hmap : arr.toList.toArray.mapM cpStep = some cs := h
  rw [List.mapM_toArray] at hmap
  simp only [Functor.map, Option.map_eq_some_iff] at hmap
  obtain ⟨ys, hys, rfl⟩ := hmap
  have hlist : ∀ (vs : List MathVal) (ns : List Nat),
      vs.mapM cpStep = some ns → ∀ c ∈ ns, c ≤ 0x10FFFF := by
    intro vs
    induction vs with
    | nil =>
      intro ns hm c hc
      simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at hm
      subst hm; nomatch hc
    | cons v tl ih =>
      intro ns hm c hc
      simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff,
        Option.pure_def, Option.some.injEq] at hm
      obtain ⟨b, hb, rest, hrest, rfl⟩ := hm
      rcases List.mem_cons.mp hc with rfl | hmem
      · cases v with
        | int i =>
          dsimp only [cpStep] at hb
          by_cases hi : 0 ≤ i ∧ i ≤ 0x10FFFF
          · simp only [hi, and_self, ↓reduceIte, Option.some.injEq] at hb
            subst hb; omega
          · simp [hi] at hb
        | _ => cases hb
      · exact ih rest hrest c hmem
  exact hlist arr.toList ys hys

theorem codePointsOf_seqOfNats_some {src : List Nat} {cs : Array Nat}
    (h : Engine.codePointsOf (Impl.seqOfNats src) = some cs) :
    cs.toList = src ∧ ∀ c ∈ cs.toList, c ≤ 0x10FFFF := by
  have hcp := codePointsOf_some_bound h
  refine ⟨?_, hcp⟩
  rw [seqOfNats_eq] at h
  unfold Engine.codePointsOf at h
  have hmap : (src.map fun (c : Nat) => MathVal.int c).toArray.mapM cpStep = some cs := h
  rw [List.mapM_toArray] at hmap
  simp only [Functor.map, Option.map_eq_some_iff] at hmap
  obtain ⟨ys, hys, rfl⟩ := hmap
  have hlist : ∀ (xs ys : List Nat),
      (xs.map fun (c : Nat) => MathVal.int c).mapM cpStep = some ys → ys = xs := by
    intro xs
    induction xs with
    | nil =>
      intro ys hm
      simp only [List.map_nil, List.mapM_nil, Option.pure_def, Option.some.injEq] at hm
      exact hm.symm
    | cons x tl ih =>
      intro ys hm
      simp only [List.map_cons, List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff,
        Option.pure_def, Option.some.injEq] at hm
      obtain ⟨b, hb, rest, hrest, rfl⟩ := hm
      dsimp only [cpStep] at hb
      by_cases hx : (0 : Int) ≤ (x : Int) ∧ (x : Int) ≤ 0x10FFFF
      · simp only [hx, and_self, ↓reduceIte, Int.toNat_natCast, Option.some.injEq] at hb
        subst hb
        rw [ih rest hrest]
      · simp only [hx, ↓reduceIte] at hb
        cases hb
  exact hlist src ys hys

/-! ## Parameter set congruence on `Sentence`, `ASIOk`, `NonStrictOk`, and `ParsesCode` -/

theorem sentence_congr_params {cx : Ctx} {P : CodePrims} {goal : NT}
    {ps1 ps2 : List Param} {toks : List Token} {t : Tree}
    (hp : ∀ p, p ∈ ps1 ↔ p ∈ ps2)
    (hhasSyn : (Ecma.Spec.gl.rulesOf .syntactic).any (·.lhs == goal) = true)
    (hok : parseTablesOk = true)
    (hsent : Sentence Ecma.Spec.gl cx P goal ps1 toks t) :
    ∃ id kids,
      t = .node goal id ps1 0 toks.length kids ∧
      Sentence Ecma.Spec.gl cx P goal ps2 toks (.node goal id ps2 0 toks.length kids) := by
  have hne : Ecma.Spec.gl.alts cx .syntactic goal ≠ [] := by
    have hhr : hasRule .syntactic goal.ctorIdx = true :=
      (hasRule_iff hok .syntactic goal.ctorIdx).mpr ⟨goal, rfl, hhasSyn⟩
    rw [Strict.hasRule_syntactic_eq hok cx goal] at hhr
    intro hnil; rw [hnil] at hhr; cases hhr
  obtain ⟨K, hK⟩ := hsent
  have hs0 := hK (max K 1) (Nat.le_max_left K 1)
  obtain ⟨k0, hk0⟩ : ∃ k0, max K 1 = k0 + 1 := ⟨max K 1 - 1, by omega⟩
  rw [hk0] at hs0
  dsimp only [DerivesAt] at hs0
  generalize ha0 : (0 : Nat) = a0 at hs0
  generalize hb0 : toks.length = b0 at hs0
  cases hs0 with
  | lex hnil _ _ => exact absurd hnil hne
  | @node _ _ _ _ _ kids id _ _ _ _ _ =>
    subst ha0; subst hb0
    refine ⟨id, kids, rfl, ⟨max K 1, fun k hk => ?_⟩⟩
    have hsk := hK k (Nat.le_trans (Nat.le_max_left K 1) hk)
    obtain ⟨k1, rfl⟩ : ∃ k1, k = k1 + 1 := ⟨k - 1, by omega⟩
    exact step_congr_root_params hp hsk

theorem nonStrictOk_congr_root_params (G : GrammarCtx) {src : List Nat}
    {els : List Element} {toks : List Token} {n : NT} {id : Nat}
    {ps1 ps2 : List Param} {i j : Nat} {kids : List Tree} :
    NonStrictOk G.gl (G.StrictIn src els toks) [] (.node n id ps1 i j kids) ↔
      NonStrictOk G.gl (G.StrictIn src els toks) [] (.node n id ps2 i j kids) := by
  let V := Tree.view (Ecma.Grammar.tokenText src els toks)
  let r1 := Tree.node n id ps1 i j kids
  let r2 := Tree.node n id ps2 i j kids
  have hh : V.height r1 = V.height r2 := by
    dsimp only [V, r1, r2, Tree.view]
    rw [Tree.height, Tree.height]
  have hpscan : ∀ d, prologueScan V d r1 = prologueScan V d r2 := fun d => by cases d <;> rfl
  have hpstr : prologueStrict V r1 = prologueStrict V r2 := by
    unfold prologueStrict
    rw [hh, hpscan]
  have hbstr : bodyStrict V r1 = bodyStrict V r2 := by
    unfold bodyStrict
    rw [← hh]
    cases V.height r1 with
    | zero => rfl
    | succ d =>
      unfold bodyOf
      have hisF : V.isA r1 .FunctionBody = V.isA r2 .FunctionBody := rfl
      have hkidsEq : V.kids r1 = V.kids r2 := rfl
      rw [← hisF, ← hkidsEq]
      cases V.isA r1 .FunctionBody with
      | false => rfl
      | true => simp [hpstr]
  have hsdown : ∀ s path, strictDown V s (r1 :: path) = strictDown V s (r2 :: path) := by
    intro s path
    cases path with
    | nil => rfl
    | cons p0 rest =>
      unfold strictDown
      have hcF : V.isIn classForms r1 = V.isIn classForms r2 := rfl
      have hfF : V.isIn functionForms r1 = V.isIn functionForms r2 := rfl
      have hmD : V.isA r1 .MethodDefinition = V.isA r2 .MethodDefinition := rfl
      rw [← hcF, ← hfF, ← hmD, hbstr]
  have htopEq : (if V.isA r1 .Module then true else if V.isA r1 .Script then prologueStrict V r1 else V.isIn bodyGoals r1 && bodyStrict V r1) =
      (if V.isA r2 .Module then true else if V.isA r2 .Script then prologueStrict V r2 else V.isIn bodyGoals r2 && bodyStrict V r2) := by
    have hm : V.isA r1 .Module = V.isA r2 .Module := rfl
    have hs : V.isA r1 .Script = V.isA r2 .Script := rfl
    have hb : V.isIn bodyGoals r1 = V.isIn bodyGoals r2 := rfl
    rw [← hm, ← hs, ← hb, hpstr, hbstr]
  have hscRoot : G.StrictIn src els toks [] r1 ↔ G.StrictIn src els toks [] r2 := by
    unfold GrammarCtx.StrictIn Ecma.Grammar.StrictCode
    refine or_congr Iff.rfl ?_
    change strictCode V [] r1 = true ↔ strictCode V [] r2 = true
    unfold strictCode
    dsimp only [List.reverse_nil, List.nil_append]
    rw [htopEq, hsdown]
  have hscSub : ∀ up u, G.StrictIn src els toks (up ++ [r1]) u ↔ G.StrictIn src els toks (up ++ [r2]) u := by
    intro up u
    unfold GrammarCtx.StrictIn Ecma.Grammar.StrictCode
    refine or_congr Iff.rfl ?_
    change strictCode V (up ++ [r1]) u = true ↔ strictCode V (up ++ [r2]) u = true
    unfold strictCode
    have hrev1 : (up ++ [r1]).reverse ++ [u] = r1 :: (up.reverse ++ [u]) := by simp
    have hrev2 : (up ++ [r2]).reverse ++ [u] = r2 :: (up.reverse ++ [u]) := by simp
    rw [hrev1, hrev2]
    dsimp only
    rw [htopEq, hsdown]
  have hsub : ∀ (sz : Nat) (up : List Tree) (u : Tree), sizeOf u ≤ sz →
      (NonStrictOk G.gl (G.StrictIn src els toks) (up ++ [r1]) u ↔
        NonStrictOk G.gl (G.StrictIn src els toks) (up ++ [r2]) u) := by
    intro sz
    induction sz using Nat.strongRecOn with
    | ind sz ih =>
      intro up u hsz
      cases u with
      | leaf _ _ | lex _ _ => exact Iff.rfl
      | node m id0 ps0 a0 b0 ks0 =>
        dsimp only [NonStrictOk]
        refine and_congr (imp_congr_right fun _ => not_congr (hscSub up _)) ?_
        have hks : ∀ (l : List Tree), sizeOf l ≤ sizeOf ks0 →
            (NonStrictOk.all G.gl (G.StrictIn src els toks) (.node m id0 ps0 a0 b0 ks0 :: up ++ [r1]) l ↔
              NonStrictOk.all G.gl (G.StrictIn src els toks) (.node m id0 ps0 a0 b0 ks0 :: up ++ [r2]) l) := by
          intro l
          induction l with
          | nil => intro _; exact Iff.rfl
          | cons d ds ihL =>
            intro hszL
            have hdLt : sizeOf d < sz := by
              simp +arith only [Tree.node.sizeOf_spec, List.cons.sizeOf_spec] at hsz hszL; omega
            have hdsLe : sizeOf ds ≤ sizeOf ks0 := by
              simp +arith only [List.cons.sizeOf_spec] at hszL; omega
            dsimp only [NonStrictOk.all]
            exact and_congr
              (ih (sizeOf d) hdLt (.node m id0 ps0 a0 b0 ks0 :: up) d (Nat.le_refl _))
              (ihL hdsLe)
        simpa only [List.cons_append] using hks ks0 (Nat.le_refl _)
  have hkidsAll : ∀ (l : List Tree),
      NonStrictOk.all G.gl (G.StrictIn src els toks) [r1] l ↔
        NonStrictOk.all G.gl (G.StrictIn src els toks) [r2] l := by
    intro l
    induction l with
    | nil => exact Iff.rfl
    | cons d ds ihL =>
      dsimp only [NonStrictOk.all]
      exact and_congr (hsub (sizeOf d) [] d (Nat.le_refl _)) ihL
  dsimp only [NonStrictOk]
  exact and_congr (imp_congr_right fun _ => not_congr hscRoot) (hkidsAll kids)

mutual
private theorem synOpen_congr_params {cx : Ctx} {P : CodePrims} {src : List Nat}
    {first : Bool} {vs : List (Nat × Bool)} {goal : NT} {q1 q2 : List Param}
    (hcq : ∀ p, q1.contains p = q2.contains p)
    {n : NT} {r : List Param} {i : Nat}
    (ho : SynOpen Ecma.Spec.gl cx P src first vs goal q1 n r i) :
    ∃ r', (∀ p, r.contains p = r'.contains p) ∧
      SynOpen Ecma.Spec.gl cx P src first vs goal q2 n r' i :=
  match ho with
  | .root => ⟨q2, hcq, .root⟩
  | .nt hp0 hne =>
    let ⟨_, hr0', hp0'⟩ := synPrefix_congr_params hcq hp0
    ⟨_, fun p => by rw [applyArgs_eq_of_contains hr0'], .nt hp0' hne⟩
  | .butNotN hp0 hne =>
    let ⟨_, hr0', hp0'⟩ := synPrefix_congr_params hcq hp0
    ⟨_, fun p => by rw [applyArgs_eq_of_contains hr0'], .butNotN hp0' hne⟩

private theorem synPrefix_congr_params {cx : Ctx} {P : CodePrims} {src : List Nat}
    {first : Bool} {vs : List (Nat × Bool)} {goal : NT} {q1 q2 : List Param}
    (hcq : ∀ p, q1.contains p = q2.contains p)
    {s : Src} {r : List Param} {k : Nat} {is : List Item} {i : Nat}
    (hpr : SynPrefix Ecma.Spec.gl cx P src first vs goal q1 s r k is i) :
    ∃ r', (∀ p, r.contains p = r'.contains p) ∧
      SynPrefix Ecma.Spec.gl cx P src first vs goal q2 s r' k is i :=
  match hpr with
  | .enter s0 ho0 hs0 hg0 =>
    let ⟨r', hr', ho'⟩ := synOpen_congr_params hcq ho0
    have hg' : s0.alt.guard.all (Guard.holds r') = true := by
      rw [← hg0]; apply list_all_congr; intro x _
      cases x with | mk sg p => unfold Guard.holds; cases sg <;> rw [hr' p]
    ⟨r', hr', .enter s0 ho' hs0 hg'⟩
  | .absent hp0 => let ⟨r', hr', hp'⟩ := synPrefix_congr_params hcq hp0; ⟨r', hr', .absent hp'⟩
  | .term hp0 ht => let ⟨r', hr', hp'⟩ := synPrefix_congr_params hcq hp0; ⟨r', hr', .term hp' ht⟩
  | .nt hp0 hne hd hfk hnc =>
    let ⟨r', hr', hp'⟩ := synPrefix_congr_params hcq hp0
    ⟨r', hr', .nt hp' hne (applyArgs_eq_of_contains hr' _ ▸ hd) hfk hnc⟩
  | .leaf hp0 hn hl hfk hnc => let ⟨r', hr', hp'⟩ := synPrefix_congr_params hcq hp0; ⟨r', hr', .leaf hp' hn hl hfk hnc⟩
  | .butNotT hp0 ht hex => let ⟨r', hr', hp'⟩ := synPrefix_congr_params hcq hp0; ⟨r', hr', .butNotT hp' ht hex⟩
  | .butNotN hp0 hne hd hex =>
    let ⟨r', hr', hp'⟩ := synPrefix_congr_params hcq hp0
    ⟨r', hr', .butNotN hp' hne (applyArgs_eq_of_contains hr' _ ▸ hd) hex⟩
  | .butNotLeaf hp0 hn hl hex => let ⟨r', hr', hp'⟩ := synPrefix_congr_params hcq hp0; ⟨r', hr', .butNotLeaf hp' hn hl hex⟩
  | .look hp0 hlk => let ⟨r', hr', hp'⟩ := synPrefix_congr_params hcq hp0; ⟨r', hr', .look hp' hlk⟩
  | .noLT hp0 hnl => let ⟨r', hr', hp'⟩ := synPrefix_congr_params hcq hp0; ⟨r', hr', .noLT hp' hnl⟩
  | .empty hp0 => let ⟨r', hr', hp'⟩ := synPrefix_congr_params hcq hp0; ⟨r', hr', .empty hp'⟩
  | .onlyIf hp0 => let ⟨r', hr', hp'⟩ := synPrefix_congr_params hcq hp0; ⟨r', hr', .onlyIf hp'⟩
end

private theorem asiOk_congr_params {cx : Ctx} {P : CodePrims} {goal : NT}
    {ps1 ps2 : List Param} {src : List Nat} {els : List Element} {toks : List Token}
    (hp : ∀ p, p ∈ ps1 ↔ p ∈ ps2) :
    ASIOk Ecma.Spec.gl cx P goal ps1 src els toks ↔
      ASIOk Ecma.Spec.gl cx P goal ps2 src els toks := by
  have hc : ∀ p, ps1.contains p = ps2.contains p := fun p => by
    apply Bool.eq_iff_iff.mpr; simp only [List.contains_iff_mem]; exact hp p
  have hgrd : ∀ g : List Guard, g.all (Guard.holds ps1) = g.all (Guard.holds ps2) := by
    intro g; apply list_all_congr; intro x _
    cases x with | mk s p => unfold Guard.holds; cases s <;> rw [hc p]
  have hsynD : ∀ {first vs i j},
      SynDerives Ecma.Spec.gl cx P src first vs goal ps1 i j ↔
        SynDerives Ecma.Spec.gl cx P src first vs goal ps2 i j := by
    intro first vs i j
    have hseqC : ∀ {q1 q2 : List Param}, (∀ p, q1.contains p = q2.contains p) →
        ∀ {s k is a b},
        SynSeq Ecma.Spec.gl cx P src first vs s q1 k is a b →
        SynSeq Ecma.Spec.gl cx P src first vs s q2 k is a b := by
      intro q1 q2 hcq s k is
      induction is generalizing k with
      | nil => intro a b h; cases h; exact .nil
      | cons _ _ ih =>
        intro a b h
        cases h with
        | absent hr => exact .absent (ih hr)
        | term ht hr => exact .term ht (ih hr)
        | nt hne hd hfk hnc hr => rw [applyArgs_eq_of_contains hcq] at hd; exact .nt hne hd hfk hnc (ih hr)
        | leaf hn hl hfk hnc hr => exact .leaf hn hl hfk hnc (ih hr)
        | butNotT ht hex hr => exact .butNotT ht hex (ih hr)
        | butNotN hne hd hex hr => rw [applyArgs_eq_of_contains hcq] at hd; exact .butNotN hne hd hex (ih hr)
        | butNotLeaf hn hl hex hr => exact .butNotLeaf hn hl hex (ih hr)
        | look hlk hr => exact .look hlk (ih hr)
        | noLT hnl hr => exact .noLT hnl (ih hr)
        | empty hr => exact .empty (ih hr)
        | onlyIf hr => exact .onlyIf (ih hr)
    constructor
    · rintro ⟨s, hs, hg, hsq⟩; exact ⟨s, hs, hgrd _ ▸ hg, hseqC hc hsq⟩
    · rintro ⟨s, hs, hg, hsq⟩; exact ⟨s, hs, (hgrd _).symm ▸ hg, hseqC (fun p => (hc p).symm) hsq⟩
  have hhitIff : ∀ {first vs} {q1 q2 : List Param},
      (∀ p, q1.contains p = q2.contains p) →
      ∀ h, SynHit Ecma.Spec.gl cx P src first vs goal q1 h →
        SynHit Ecma.Spec.gl cx P src first vs goal q2 h := by
    intro first vs q1 q2 hcq h hh
    cases hh with
    | zero => exact .zero
    | term hp0 ht => obtain ⟨_, _, hp'⟩ := synPrefix_congr_params hcq hp0; exact .term hp' ht
    | nt hp0 hne hd hfk hnc =>
      obtain ⟨_, hr', hp'⟩ := synPrefix_congr_params hcq hp0
      exact .nt hp' hne (applyArgs_eq_of_contains hr' _ ▸ hd) hfk hnc
    | leaf hp0 hn hl hfk hnc => obtain ⟨_, _, hp'⟩ := synPrefix_congr_params hcq hp0; exact .leaf hp' hn hl hfk hnc
    | butNotT hp0 ht hex => obtain ⟨_, _, hp'⟩ := synPrefix_congr_params hcq hp0; exact .butNotT hp' ht hex
    | butNotN hp0 hne hd hex =>
      obtain ⟨_, hr', hp'⟩ := synPrefix_congr_params hcq hp0
      exact .butNotN hp' hne (applyArgs_eq_of_contains hr' _ ▸ hd) hex
    | butNotLeaf hp0 hn hl hex => obtain ⟨_, _, hp'⟩ := synPrefix_congr_params hcq hp0; exact .butNotLeaf hp' hn hl hex
  have hdoneIff : ∀ {first vs},
      SynDone Ecma.Spec.gl cx P src first vs goal ps1 ↔
        SynDone Ecma.Spec.gl cx P src first vs goal ps2 :=
    fun {_ _} => exists_congr fun _ => exists_congr fun _ => exists_congr fun _ =>
      and_congr hsynD Iff.rfl
  have hnextIff : ∀ {first vs p paren},
      NextASI Ecma.Spec.gl cx P src first vs goal ps1 p paren ↔
        NextASI Ecma.Spec.gl cx P src first vs goal ps2 p paren := by
    intro first vs p paren
    unfold NextASI
    refine and_congr (not_congr hdoneIff) (exists_congr fun f => ?_)
    have hhIff : ∀ h, SynHit Ecma.Spec.gl cx P src first vs goal ps1 h ↔
        SynHit Ecma.Spec.gl cx P src first vs goal ps2 h :=
      fun h => ⟨hhitIff hc h, hhitIff (fun p => (hc p).symm) h⟩
    exact and_congr (hhIff f) (and_congr (forall_congr' fun h => imp_congr_left (hhIff h)) Iff.rfl)
  have hvalIff : ∀ {first vs},
      ValidASI Ecma.Spec.gl cx P src first goal ps1 vs ↔
        ValidASI Ecma.Spec.gl cx P src first goal ps2 vs := by
    intro first vs
    constructor
    · intro hv; induction hv with
      | nil => exact .nil
      | step _ hn ih => exact .step ih (hnextIff.mp hn)
    · intro hv; induction hv with
      | nil => exact .nil
      | step _ hn ih => exact .step ih (hnextIff.mpr hn)
  exact exists_congr fun _ => and_congr hvalIff Iff.rfl

private theorem parsesCode_nodeRel_congr_params {M : Ecma.Model} {st : Nat}
    {cx : Ctx} {P : CodePrims} {g : GrammarId} {goal : NT}
    {ps1 ps2 : List Param} {src : List Nat} {nd : M.Node} {t : Tree}
    (hp : ∀ p, p ∈ ps1 ↔ p ∈ ps2)
    (hpc : ParsesCode Ecma.Spec.gl cx P g goal ps1 src t)
    (hrel : Ecma.Model.NodeRel M st src (fun i j => (i, j)) nd t) :
    ∃ t', ParsesCode Ecma.Spec.gl cx P g goal ps2 src t' ∧
      Ecma.Model.NodeRel M st src (fun i j => (i, j)) nd t' := by
  unfold ParsesCode at hpc ⊢
  cases hord : Ecma.Spec.gl.ordered cx g with
  | false =>
    simp only [hord, Bool.false_eq_true, ↓reduceIte] at hpc ⊢
    obtain ⟨t', _, _, hrelMap, _, hder'⟩ := derives_congr_params hp hpc
    exact ⟨t', hder', hrelMap _ _ _ _ _ hrel⟩
  | true =>
    simp only [hord, ↓reduceIte] at hpc ⊢
    obtain ⟨hder, hcom⟩ := hpc
    obtain ⟨t', _, _, hrelMap, hcomMap, hder'⟩ := derives_congr_params hp hder
    refine ⟨t', ⟨hder', hcomMap _ hcom ?_⟩, hrelMap _ _ _ _ _ hrel⟩
    intro a id' ks' _ _ ⟨K, hK⟩
    refine ⟨ks', max K 1, fun k hk => ?_⟩
    obtain ⟨km, rfl⟩ : ∃ km, k = km + 1 := ⟨k - 1, by omega⟩
    have hsk := hK (km + 1) (Nat.le_trans (Nat.le_max_left K 1) hk)
    exact step_congr_root_params (fun p => (hp p).symm) hsk

private theorem parsesCode_congr_params {cx : Ctx} {P : CodePrims} {g : GrammarId}
    {goal : NT} {ps1 ps2 : List Param} {src : List Nat} {t : Tree}
    (hp : ∀ p, p ∈ ps1 ↔ p ∈ ps2)
    (hpc : ParsesCode Ecma.Spec.gl cx P g goal ps1 src t) :
    ∃ t', ParsesCode Ecma.Spec.gl cx P g goal ps2 src t' := by
  unfold ParsesCode at hpc ⊢
  cases hord : Ecma.Spec.gl.ordered cx g with
  | false =>
    simp only [hord, Bool.false_eq_true, ↓reduceIte] at hpc ⊢
    obtain ⟨t', _, _, _, _, hder'⟩ := derives_congr_params hp hpc
    exact ⟨t', hder'⟩
  | true =>
    simp only [hord, ↓reduceIte] at hpc ⊢
    obtain ⟨hder, hcom⟩ := hpc
    obtain ⟨t', _, _, _, hcomMap, hder'⟩ := derives_congr_params hp hder
    refine ⟨t', hder', hcomMap _ hcom ?_⟩
    intro a id' ks' _ _ ⟨K, hK⟩
    refine ⟨ks', max K 1, fun k hk => ?_⟩
    obtain ⟨km, rfl⟩ : ∃ km, k = km + 1 := ⟨k - 1, by omega⟩
    have hsk := hK (km + 1) (Nat.le_trans (Nat.le_max_left K 1) hk)
    exact step_congr_root_params (fun p => (hp p).symm) hsk

/-! ## `Engine.Parse.parse` soundness and completeness -/

theorem fold_outcome_ok {α β : Type} (step : α → Outcome β) :
    ∀ (l : List α) {nd : β},
      (l.foldl (init := Outcome.noParse) fun acc x => match acc with
        | .noParse => step x
        | done => done) = .ok nd →
      ∃ x ∈ l, step x = .ok nd := by
  have hpresOk : ∀ (l : List α) (n0 : β),
      (l.foldl (init := Outcome.ok n0) fun acc x => match acc with
        | .noParse => step x
        | done => done) = .ok n0 := by
    intro l n0; induction l with
    | nil => rfl
    | cons _ tl ih => exact ih
  have hpresStop : ∀ (l : List α) (s : Engine.Parse.Stop),
      (l.foldl (init := Outcome.stop s) fun acc x => match acc with
        | .noParse => step x
        | done => done) = .stop s := by
    intro l s; induction l with
    | nil => rfl
    | cons _ tl ih => exact ih
  intro l
  induction l with
  | nil => intro _ h; cases h
  | cons hd tl ih =>
    intro nd h
    rw [List.foldl_cons] at h
    dsimp only at h
    cases hs : step hd with
    | stop s => rw [hs] at h; exact nomatch (hpresStop tl s).symm.trans h
    | ok n0 =>
      rw [hs] at h
      have heqOut := (hpresOk tl n0).symm.trans h
      injection heqOut with heq; subst heq
      exact ⟨hd, List.mem_cons_self .., hs⟩
    | noParse =>
      rw [hs] at h
      obtain ⟨x, hxMem, hxOk⟩ := ih h
      exact ⟨x, List.mem_cons_of_mem _ hxMem, hxOk⟩

private theorem fold_outcome_noParse {α β : Type} (step : α → Outcome β) :
    ∀ (l : List α),
      (l.foldl (init := Outcome.noParse) fun acc x => match acc with
        | .noParse => step x
        | done => done) = .noParse →
      ∀ x ∈ l, step x = .noParse := by
  have hpresOk : ∀ (l : List α) (n0 : β),
      (l.foldl (init := Outcome.ok n0) fun acc x => match acc with
        | .noParse => step x
        | done => done) = .ok n0 := by
    intro l n0; induction l with
    | nil => rfl
    | cons _ tl ih => exact ih
  have hpresStop : ∀ (l : List α) (s : Engine.Parse.Stop),
      (l.foldl (init := Outcome.stop s) fun acc x => match acc with
        | .noParse => step x
        | done => done) = .stop s := by
    intro l s; induction l with
    | nil => rfl
    | cons _ tl ih => exact ih
  intro l
  induction l with
  | nil => intro _ _ hx; nomatch hx
  | cons hd tl ih =>
    intro h x hxMem
    rw [List.foldl_cons] at h
    dsimp only at h
    cases hs : step hd with
    | stop s => rw [hs] at h; exact nomatch (hpresStop tl s).symm.trans h
    | ok n0 => rw [hs] at h; exact nomatch (hpresOk tl n0).symm.trans h
    | noParse =>
      rw [hs] at h
      rcases List.mem_cons.mp hxMem with rfl | htl
      · exact hs
      · exact ih h x htl

theorem parse_inner_sound (hok : parseTablesOk = true)
    {cx : Ctx} {strict : Bool} {stamp : Nat} {cs : Array Nat}
    (hcp : ∀ c ∈ cs.toList, c ≤ 0x10FFFF)
    {goal : NT} {args : List (ParamId × Bool)} {ps : List Param}
    (hps : ParamsOf args ps) {nd : Node}
    (hrun : Engine.Parse.parse Engine.builder cx strict stamp cs goal.ctorIdx args = .ok nd) :
    ∃ t, ({ gl := Ecma.Spec.gl, cx := cx, P := Engine.Model.codePrims, strict := strict } : GrammarCtx).ParseIs
      Impl stamp goal ps cs.toList nd t := by
  have hp0 := paramsOfArgs_iff_of_paramsOf hps
  unfold Engine.Parse.parse at hrun
  rcases opt_none_or_some (ruleNt .syntactic goal.ctorIdx) with hsynNone | ⟨lhs, hsynSome⟩
  · rw [hsynNone] at hrun
    dsimp only at hrun
    have hnoSyn : (Ecma.Spec.gl.rulesOf .syntactic).any (·.lhs == goal) = false := by
      rw [Bool.eq_false_iff, ne_eq]; intro h
      have := ruleNt_of_rulesOf hok h
      rw [hsynNone] at this; cases this
    obtain ⟨⟨g, lhs⟩, hmemGs, houtOk⟩ := fold_outcome_ok _ _ hrun
    dsimp only at houtOk
    have hcRun : Code.run Engine.builder cs g cx stamp lhs (paramsOfArgs args) = .ok (some nd) := by
      rcases except_eq_err_or_ok (Code.run Engine.builder cs g cx stamp lhs (paramsOfArgs args)) with ⟨err, herr⟩ | ⟨optN, hokR⟩
      · rw [herr] at houtOk; cases houtOk
      · cases optN with
        | none => rw [hokR] at houtOk; cases houtOk
        | some n0 => rw [hokR] at houtOk; injection houtOk with heq; subst n0; exact hokR
    rw [List.mem_filterMap] at hmemGs
    obtain ⟨g0, hgMem, hmapEq⟩ := hmemGs
    rcases opt_none_or_some (ruleNt g0 goal.ctorIdx) with hn0 | ⟨m0, hm0⟩
    · rw [hn0] at hmapEq; cases hmapEq
    · rw [hm0] at hmapEq
      injection hmapEq with hpEq
      injection hpEq with hgEq hmEq; subst g0; subst m0
      obtain ⟨hidxEq, hhasRule⟩ := ruleNt_some_imp hok hm0
      have hlhsGoal : lhs = goal := nt_ctorIdx_inj hidxEq
      subst lhs
      obtain ⟨t0, hpc0, hrel0⟩ := code_run_some_spec hok hgMem hcRun
      obtain ⟨t', hpc', hrel'⟩ := parsesCode_nodeRel_congr_params hp0 hpc0 hrel0
      refine ⟨t', ?_⟩
      unfold GrammarCtx.ParseIs
      simp only [hnoSyn, Bool.false_eq_true, ↓reduceIte]
      exact ⟨g, hgMem, hhasRule, hpc', hrel'⟩
  · rw [hsynSome] at hrun
    dsimp only at hrun
    obtain ⟨hidxEq, hhasSyn⟩ := ruleNt_some_imp hok hsynSome
    have hlhsGoal : lhs = goal := nt_ctorIdx_inj hidxEq
    subst lhs
    rcases except_eq_err_or_ok (Syntax.run Engine.builder cs cx stamp goal (paramsOfArgs args)) with ⟨err, herr⟩ | ⟨optN, hsRun⟩
    · rw [herr] at hrun; cases hrun
    · cases optN with
      | none => rw [hsRun] at hrun; cases hrun
      | some n0 =>
        rw [hsRun] at hrun
        dsimp only at hrun
        let G : GrammarCtx := { gl := Ecma.Spec.gl, cx := cx, P := Engine.Model.codePrims, strict := strict }
        have ⟨n0Eq, hnsOk⟩ : n0 = nd ∧ ∃ els toks t,
            Scans Ecma.Spec.gl cx Engine.Model.codePrims cs.toList els ∧
            GoalsAt goal els toks t ∧
            toks.filter (·.virt.isNone) = tokensOf cs.toList els ∧
            toks.all (fun k => k.virt.isNone || !k.lt) = true ∧
            ASIOk Ecma.Spec.gl cx Engine.Model.codePrims goal (paramsOfArgs args) cs.toList els toks ∧
            Sentence Ecma.Spec.gl cx Engine.Model.codePrims goal (paramsOfArgs args) toks t ∧
            ForHeadersExplicit toks t ∧
            Ecma.Model.NodeRel Impl stamp cs.toList (Ecma.Grammar.tokenSpan els toks) n0 t ∧
            NonStrictOk Ecma.Spec.gl (G.StrictIn cs.toList els toks) [] t := by
          obtain ⟨els, toks, t, hsc, hgl, hfi, hal, hasi, hsn, hfh, hnrel, hpst, _, _⟩ :=
            syntax_run_some_spec hok hcp hhasSyn hsRun
          by_cases hnoB : (!cx.annexB.any) = true
          · simp only [hnoB, ↓reduceIte] at hrun
            injection hrun with heq
            exact ⟨heq, els, toks, t, hsc, hgl, hfi, hal, hasi, hsn, hfh, hnrel,
              Strict.nonStrictOk_of_not_annexB hok hnoB _ t [] (Nat.le_refl _) hpst⟩
          · simp only [hnoB, Bool.false_eq_true, ↓reduceIte] at hrun
            cases hsl : Strict.sloppyOk Engine.builder (Syntax.depth cs.size + 1) strict (Syntax.depth cs.size + 1) [] n0 with
            | none => rw [hsl] at hrun; cases hrun
            | some b =>
              cases b with
              | false => rw [hsl] at hrun; cases hrun
              | true =>
                rw [hsl] at hrun; injection hrun with heq
                exact ⟨heq, els, toks, t, hsc, hgl, hfi, hal, hasi, hsn, hfh, hnrel,
                  Strict.sloppyOk_true_sound hok hsc hfi (Nat.le_refl _) hpst hnrel hsl⟩
        subst n0
        obtain ⟨els, toks, t0, hsc, hgl, hfi, hal, hasi0, hsn0, hfh, hnrel0, hns0⟩ := hnsOk
        obtain ⟨id0, kids0, ht0Eq, hsn⟩ := sentence_congr_params hp0 hhasSyn hok hsn0
        subst ht0Eq
        refine ⟨.node goal id0 ps 0 toks.length kids0, ?_⟩
        unfold GrammarCtx.ParseIs
        simp only [hhasSyn, ↓reduceIte]
        exact ⟨els, toks, hsc, hgl, hfi, hal, (asiOk_congr_params hp0).mp hasi0, hsn, hfh,
          (nonStrictOk_congr_root_params G).mp hns0, nodeRel_congr_root_params hp0 hnrel0⟩

theorem parse_inner_complete (hok : parseTablesOk = true)
    {cx : Ctx} {strict : Bool} {stamp : Nat} {cs : Array Nat}
    (hcp : ∀ c ∈ cs.toList, c ≤ 0x10FFFF)
    {goal : NT} {args : List (ParamId × Bool)} {ps : List Param}
    (hps : ParamsOf args ps)
    (hrun : Engine.Parse.parse Engine.builder cx strict stamp cs goal.ctorIdx args = .noParse) :
    ∀ t, ¬ ({ gl := Ecma.Spec.gl, cx := cx, P := Engine.Model.codePrims, strict := strict } : GrammarCtx).Parses
      goal ps cs.toList t := by
  have hp0 := paramsOfArgs_iff_of_paramsOf hps
  have hpSym : ∀ p, p ∈ ps ↔ p ∈ paramsOfArgs args := fun p => (hp0 p).symm
  unfold Engine.Parse.parse at hrun
  rcases opt_none_or_some (ruleNt .syntactic goal.ctorIdx) with hsynNone | ⟨lhs, hsynSome⟩
  · rw [hsynNone] at hrun
    dsimp only at hrun
    have hnoSyn : (Ecma.Spec.gl.rulesOf .syntactic).any (·.lhs == goal) = false := by
      rw [Bool.eq_false_iff, ne_eq]; intro h
      have := ruleNt_of_rulesOf hok h
      rw [hsynNone] at this; cases this
    have hallNone := fold_outcome_noParse _ _ hrun
    intro t hp
    unfold GrammarCtx.Parses at hp
    simp only [hnoSyn, Bool.false_eq_true, ↓reduceIte] at hp
    obtain ⟨g, hgMem, hgRule, hpc⟩ := hp
    have hrNt := ruleNt_of_rulesOf hok hgRule
    have hmemGs : (g, goal) ∈ codeGrammars.filterMap (fun g' => (ruleNt g' goal.ctorIdx).map ((g', ·))) := by
      rw [List.mem_filterMap]
      exact ⟨g, hgMem, by rw [hrNt]; rfl⟩
    have houtNone := hallNone (g, goal) hmemGs
    dsimp only at houtNone
    have hcNone : Code.run Engine.builder cs g cx stamp goal (paramsOfArgs args) = .ok none := by
      rcases except_eq_err_or_ok (Code.run Engine.builder cs g cx stamp goal (paramsOfArgs args)) with ⟨err, herr⟩ | ⟨optN, hokR⟩
      · rw [herr] at houtNone; cases houtNone
      · cases optN with
        | some _ => rw [hokR] at houtNone; cases houtNone
        | none => exact hokR
    obtain ⟨t', hpc'⟩ := parsesCode_congr_params hpSym hpc
    exact code_run_none_spec hok hgMem hcNone t' hpc'
  · rw [hsynSome] at hrun
    dsimp only at hrun
    obtain ⟨hidxEq, hhasSyn⟩ := ruleNt_some_imp hok hsynSome
    have hlhsGoal : lhs = goal := nt_ctorIdx_inj hidxEq
    subst lhs
    let G : GrammarCtx := { gl := Ecma.Spec.gl, cx := cx, P := Engine.Model.codePrims, strict := strict }
    rcases except_eq_err_or_ok (Syntax.run Engine.builder cs cx stamp goal (paramsOfArgs args)) with ⟨err, herr⟩ | ⟨optN, hsRun⟩
    · rw [herr] at hrun; cases hrun
    · cases optN with
      | none =>
        intro t hp
        unfold GrammarCtx.Parses at hp
        simp only [hhasSyn, ↓reduceIte] at hp
        obtain ⟨els, toks, hsc, hgl, hfi, hal, hasi, hsn, hfh, _⟩ := hp
        obtain ⟨id0, kids0, htEq, hsn0⟩ := sentence_congr_params hpSym hhasSyn hok hsn
        subst htEq
        exact syntax_run_none_spec hok hcp hhasSyn hsRun els toks
          (.node goal id0 (paramsOfArgs args) 0 toks.length kids0)
          hsc hgl hfi hal ((asiOk_congr_params hpSym).mp hasi) hsn0 hfh
      | some n0 =>
        rw [hsRun] at hrun
        dsimp only at hrun
        by_cases hnoB : (!cx.annexB.any) = true
        · simp [hnoB] at hrun
        · simp only [hnoB, Bool.false_eq_true, ↓reduceIte] at hrun
          cases hsl : Strict.sloppyOk Engine.builder (Syntax.depth cs.size + 1) strict (Syntax.depth cs.size + 1) [] n0 with
          | none => rw [hsl] at hrun; cases hrun
          | some b =>
            cases b with
            | true => rw [hsl] at hrun; cases hrun
            | false =>
              obtain ⟨els1, toks1, t1, hsc1, _, hfi1, _, _, _, _, hnrel1, hpst1, hsh1, htrans⟩ :=
                syntax_run_some_spec hok hcp hhasSyn hsRun
              have hnotNs1 := Strict.sloppyOk_false_sound hok hsc1 hfi1 (Nat.le_refl _) hsh1 hpst1 hnrel1 hsl
              intro t2 hp
              unfold GrammarCtx.Parses at hp
              simp only [hhasSyn, ↓reduceIte] at hp
              obtain ⟨els2, toks2, hsc2, hgl2, hfi2, hal2, hasi2, hsn2, hfh2, hns2⟩ := hp
              obtain ⟨id2, kids2, ht2Eq, hsn2'⟩ := sentence_congr_params hpSym hhasSyn hok hsn2
              subst ht2Eq
              have hns2' := (nonStrictOk_congr_root_params (ps2 := paramsOfArgs args) G).mp hns2
              have hns1 := htrans strict els2 toks2
                (.node goal id2 (paramsOfArgs args) 0 toks2.length kids2)
                hsc2 hgl2 hfi2 hal2 ((asiOk_congr_params hpSym).mp hasi2) hsn2' hfh2 hns2'
              exact hnotNs1 hns1

/-! ## `Engine.outcome` and `Engine.parse`: `Ecma.Model.ParseLaws` -/

theorem outcome_sound (hok : parseTablesOk = true)
    {stamp : Nat} {src : List Nat} {goal : NT} {args : List (ParamId × Bool)}
    {ps : List Param} (hps : ParamsOf args ps) {cx : Ctx} {strict : Bool} {nd : Node}
    (ho : Engine.outcome stamp (Impl.seqOfNats src) goal.ctorIdx args cx strict = .ok nd) :
    ∃ t, ({ gl := Ecma.Spec.gl, cx := cx, P := Engine.Model.codePrims, strict := strict } : GrammarCtx).ParseIs
      Impl stamp goal ps src nd t := by
  unfold Engine.outcome at ho
  rcases opt_none_or_some (Engine.codePointsOf (Impl.seqOfNats src)) with hcNone | ⟨cs, hcSome⟩
  · rw [hcNone] at ho; cases ho
  · rw [hcSome] at ho
    obtain ⟨hcsEq, hcp⟩ := codePointsOf_seqOfNats_some hcSome
    by_cases hfast : (Engine.noFirst goal.ctorIdx cs || Engine.noJSON goal.ctorIdx cs) = true
    · simp [hfast] at ho
    · simp only [hfast, Bool.false_eq_true, ↓reduceIte] at ho
      cases hpOut : Engine.Parse.parse Engine.builder cx strict stamp cs goal.ctorIdx args with
      | noParse | stop _ => rw [hpOut] at ho; cases ho
      | ok n0 =>
        rw [hpOut] at ho
        dsimp only [Engine.checked] at ho
        by_cases hsh : Engine.shaped n0 = true
        · simp only [hsh, ↓reduceIte] at ho
          injection ho with hnEq; subst n0
          obtain ⟨t, hpi⟩ := parse_inner_sound hok hcp hps hpOut
          exact ⟨t, hcsEq ▸ hpi⟩
        · simp [hsh] at ho

theorem outcome_complete (hok : parseTablesOk = true)
    {stamp : Nat} {src : List Nat} {goal : NT} {args : List (ParamId × Bool)}
    {ps : List Param} (hps : ParamsOf args ps) {cx : Ctx} {strict : Bool}
    (ho : Engine.outcome stamp (Impl.seqOfNats src) goal.ctorIdx args cx strict = .noParse) :
    ∀ t, ¬ ({ gl := Ecma.Spec.gl, cx := cx, P := Engine.Model.codePrims, strict := strict } : GrammarCtx).Parses
      goal ps src t := by
  unfold Engine.outcome at ho
  rcases opt_none_or_some (Engine.codePointsOf (Impl.seqOfNats src)) with hcNone | ⟨cs, hcSome⟩
  · rw [hcNone] at ho; cases ho
  · rw [hcSome] at ho
    obtain ⟨hcsEq, hcp⟩ := codePointsOf_seqOfNats_some hcSome
    rw [← hcsEq]
    by_cases hfast : (Engine.noFirst goal.ctorIdx cs || Engine.noJSON goal.ctorIdx cs) = true
    · rcases Bool.or_eq_true_iff.mp hfast with hnf | hnj
      · exact noFirst_complete hok hnf
      · exact noJSON_complete hok hnj
    · simp only [hfast, Bool.false_eq_true, ↓reduceIte] at ho
      cases hpOut : Engine.Parse.parse Engine.builder cx strict stamp cs goal.ctorIdx args with
      | stop _ => rw [hpOut] at ho; cases ho
      | ok n0 =>
        rw [hpOut] at ho
        dsimp only [Engine.checked] at ho
        cases hsh : Engine.shaped n0 <;> simp [hsh] at ho
      | noParse =>
        exact parse_inner_complete hok hcp hps hpOut

private theorem parseIs_restamp (st : Nat) {st0 : Nat} {G : GrammarCtx} {goal : NT}
    {ps : List Param} {src : List Nat} {nd : Node} {t : Tree}
    (h : G.ParseIs Impl st0 goal ps src nd t) :
    G.ParseIs Impl st goal ps src (Engine.restamp st nd) t := by
  unfold GrammarCtx.ParseIs at h ⊢
  split at h
  · rename_i hsyn
    simp only [hsyn, ↓reduceIte]
    obtain ⟨els, toks, hsc, hgl, hfi, hal, hasi, hsn, hfh, hns, hrel⟩ := h
    exact ⟨els, toks, hsc, hgl, hfi, hal, hasi, hsn, hfh, hns, nodeRel_restamp st hrel⟩
  · rename_i hsyn
    simp only [hsyn, Bool.false_eq_true, ↓reduceIte]
    obtain ⟨g, hg, hr, hpc, hrel⟩ := h
    exact ⟨g, hg, hr, hpc, nodeRel_restamp st hrel⟩

theorem engine_parse_sound {pc : ParseCx} {st : Nat} {src : List Nat} {goal : NT}
    {args : List (ParamId × Bool)} {ps : List Param} {n : Node}
    (hps : ParamsOf args ps)
    (h : Engine.parse pc st (Impl.seqOfNats src) goal.ctorIdx args = some (some n)) :
    ∃ t, ({ gl := Ecma.Spec.gl, cx := Engine.grammarCx pc, P := Engine.Model.codePrims, strict := pc.strict } : GrammarCtx).ParseIs
      Impl st goal ps src n t := by
  unfold Engine.parse at h
  by_cases hth : (!parseTablesOkThunk.get) = true
  · simp [hth] at h
  · have hthF : (!parseTablesOkThunk.get) = false := Bool.eq_false_iff.mpr hth
    have hok := parseTablesOk_of_thunk hthF
    simp only [hthF, Bool.false_eq_true, ↓reduceIte] at h
    have hfallback : (match Engine.outcome 0 (Impl.seqOfNats src) goal.ctorIdx args (Engine.grammarCx pc) pc.strict with
        | .ok m => some (some (Engine.restamp st m))
        | .noParse => some none
        | .stop _ => none) = some (some n) →
        ∃ t, ({ gl := Ecma.Spec.gl, cx := Engine.grammarCx pc, P := Engine.Model.codePrims, strict := pc.strict } : GrammarCtx).ParseIs
          Impl st goal ps src n t := by
      intro hf
      cases ho : Engine.outcome 0 (Impl.seqOfNats src) goal.ctorIdx args (Engine.grammarCx pc) pc.strict with
      | noParse | stop _ => rw [ho] at hf; cases hf
      | ok m =>
        rw [ho] at hf
        injection hf with hopt; injection hopt with hmEq; subst hmEq
        obtain ⟨t, hpi⟩ := outcome_sound hok hps ho
        exact ⟨t, parseIs_restamp st hpi⟩
    by_cases hnum : (goal.ctorIdx == NT.StringNumericLiteral.ctorIdx || goal.ctorIdx == NT.StringIntegerLiteral.ctorIdx) = true
    · simp only [hnum, ↓reduceIte] at h
      rcases opt_none_or_some (Engine.codePointsOf (Impl.seqOfNats src)) with hcNone | ⟨cs, hcSome⟩
      · rw [hcNone] at h; exact hfallback h
      · rw [hcSome] at h
        rcases opt_none_or_some (Engine.parseNumeric st (Impl.seqOfNats src) goal.ctorIdx args) with hpNone | ⟨optM, hpSome⟩
        · rw [hpNone] at h; exact hfallback h
        · rw [hpSome] at h
          cases optM with
          | none => exact hfallback h
          | some m =>
            dsimp only at h
            by_cases hchk : (Engine.shaped m && (Engine.builder.nt m == goal.ctorIdx &&
                Engine.builder.args m == paramsOfArgs args && Engine.builder.span m == (0, cs.size) &&
                (Engine.verifyCodeNode cs (Engine.grammarCx pc) .numericString st (m.height + 1) m).isSome)) = true
            · simp only [hchk, ↓reduceIte] at h
              injection h with hopt; injection hopt with hmEq; subst m
              simp only [Bool.and_eq_true, beq_iff_eq, Option.isSome_iff_exists] at hchk
              obtain ⟨_, ⟨⟨⟨hntM, hargsM⟩, hspM⟩, ⟨t0, hv⟩⟩⟩ := hchk
              obtain ⟨hcsEq, _⟩ := codePointsOf_seqOfNats_some hcSome
              have hp0 := paramsOfArgs_iff_of_paramsOf hps
              obtain ⟨t', hder, hrel⟩ := verifyCodeNode_sound (ps := ps) hok hntM
                (fun p => by rw [hargsM]; exact hp0 p) hspM hv
              have hgoalOr : goal = .StringNumericLiteral ∨ goal = .StringIntegerLiteral := by
                rcases Bool.or_eq_true_iff.mp hnum with h1 | h2
                · exact Or.inl (nt_ctorIdx_inj (beq_iff_eq.mp h1))
                · exact Or.inr (nt_ctorIdx_inj (beq_iff_eq.mp h2))
              have hnoSyn : (Ecma.Spec.gl.rulesOf .syntactic).any (·.lhs == goal) = false := by
                rw [← glData_eq]; rcases hgoalOr with rfl | rfl <;> decide
              have hhasNum : (Ecma.Spec.gl.rulesOf .numericString).any (·.lhs == goal) = true := by
                rw [← glData_eq]; rcases hgoalOr with rfl | rfl <;> decide
              have hordNum : Ecma.Spec.gl.ordered (Engine.grammarCx pc) .numericString = false := by
                rw [← orderedBy_eq hok]; exact (fast_invariants hok (Engine.grammarCx pc)).2.2.2.2.2.1
              have hszEq : cs.size = src.length := by rw [← Array.length_toList, hcsEq]
              refine ⟨t', ?_⟩
              unfold GrammarCtx.ParseIs
              simp only [hnoSyn, Bool.false_eq_true, ↓reduceIte]
              refine ⟨.numericString, by decide, hhasNum, ?_, hcsEq ▸ hrel⟩
              unfold ParsesCode
              simp only [hordNum, Bool.false_eq_true, ↓reduceIte]
              simpa [hcsEq, hszEq] using hder
            · simp [hchk] at h
    · simp only [hnum, Bool.false_eq_true, ↓reduceIte] at h
      exact hfallback h

theorem engine_parse_complete {pc : ParseCx} {st : Nat} {src : List Nat} {goal : NT}
    {args : List (ParamId × Bool)} {ps : List Param}
    (hps : ParamsOf args ps)
    (h : Engine.parse pc st (Impl.seqOfNats src) goal.ctorIdx args = some none) :
    ∀ t, ¬ ({ gl := Ecma.Spec.gl, cx := Engine.grammarCx pc, P := Engine.Model.codePrims, strict := pc.strict } : GrammarCtx).Parses
      goal ps src t := by
  unfold Engine.parse at h
  by_cases hth : (!parseTablesOkThunk.get) = true
  · simp [hth] at h
  · have hthF : (!parseTablesOkThunk.get) = false := Bool.eq_false_iff.mpr hth
    have hok := parseTablesOk_of_thunk hthF
    simp only [hthF, Bool.false_eq_true, ↓reduceIte] at h
    have hfallback : (match Engine.outcome 0 (Impl.seqOfNats src) goal.ctorIdx args (Engine.grammarCx pc) pc.strict with
        | .ok m => some (some (Engine.restamp st m))
        | .noParse => some none
        | .stop _ => none) = some none →
        ∀ t, ¬ ({ gl := Ecma.Spec.gl, cx := Engine.grammarCx pc, P := Engine.Model.codePrims, strict := pc.strict } : GrammarCtx).Parses
          goal ps src t := by
      intro hf
      cases ho : Engine.outcome 0 (Impl.seqOfNats src) goal.ctorIdx args (Engine.grammarCx pc) pc.strict with
      | ok _ | stop _ => rw [ho] at hf; cases hf
      | noParse => exact outcome_complete hok hps ho
    by_cases hnum : (goal.ctorIdx == NT.StringNumericLiteral.ctorIdx || goal.ctorIdx == NT.StringIntegerLiteral.ctorIdx) = true
    · simp only [hnum, ↓reduceIte] at h
      rcases opt_none_or_some (Engine.codePointsOf (Impl.seqOfNats src)) with hcNone | ⟨cs, hcSome⟩
      · rw [hcNone] at h; exact hfallback h
      · rw [hcSome] at h
        rcases opt_none_or_some (Engine.parseNumeric st (Impl.seqOfNats src) goal.ctorIdx args) with hpNone | ⟨optM, hpSome⟩
        · rw [hpNone] at h; exact hfallback h
        · rw [hpSome] at h
          cases optM with
          | none => exact hfallback h
          | some m =>
            dsimp only at h
            split at h <;> cases h
    · simp only [hnum, Bool.false_eq_true, ↓reduceIte] at h
      exact hfallback h

/-- The engine's parser meets `Ecma.Model.ParseLaws` under `Engine.Model.codePrims`. -/
theorem parseLaws (cx : Ctx) (strict : Bool) :
    Ecma.Model.ParseLaws Impl (grammarCtx cx Engine.Model.codePrims strict) where
  sound _ _ _ _ _ _ _ hps h := engine_parse_sound hps h
  complete _ _ _ _ _ _ hps h := engine_parse_complete hps h

end Engine.Impl
