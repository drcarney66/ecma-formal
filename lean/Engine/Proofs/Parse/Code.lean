module

public import Engine.Parse.Code
public import Engine.Proofs.Parse.Search
public import Engine.Proofs.Parse.JsonText
public import Engine.Proofs.Parse.Shape

@[expose] public section

/-!
# Soundness and completeness of the code-point grammar parser (`Engine.Parse.Code`)

Instantiates `AlphaSpec` for `Code.alpha`, proves negative-item exactness (`Code.dec`,
`Code.decAny`) and stratum stabilization for all `g ∈ codeGrammars`, equates `ModeDerives true`
with B.1.2 commitment (`Grammar.Committed`), proves `Code.parse`, `Code.groupLimit`, and `Code.run`
sound and complete against `Grammar.ParsesCode` and `Model.NodeRel`, and proves `verifyCodeNode`
soundness and `noFirst` completeness.
-/

namespace Engine.Parse

open Ecma.Grammar Search

private theorem opt_none_or_some {α : Type} (o : Option α) :
    o = none ∨ ∃ x, o = some x := by
  cases o with
  | none => exact Or.inl rfl
  | some x => exact Or.inr ⟨x, rfl⟩

private theorem except_eq_err_or_ok {ε α : Type} (r : Except ε α) :
    (∃ e, r = .error e) ∨ (∃ v, r = .ok v) := by
  cases r with
  | error e => exact Or.inl ⟨e, rfl⟩
  | ok v => exact Or.inr ⟨v, rfl⟩

/-! ## Builder, array/slice helpers, and restamping on `Model.NodeRel` -/

theorem builderSpec_engine : BuilderSpec Engine.builder where
  prod_node _ _ _ _ _ _ _ _ := rfl
  nt_node _ _ _ _ _ _ _ _ := rfl
  args_node _ _ _ _ _ _ _ _ := rfl
  span_node _ _ _ _ _ _ _ _ := rfl
  kids_node _ _ _ _ _ _ _ _ := rfl
  stamp_node _ _ _ _ _ _ _ _ := rfl
  text_node _ _ _ _ _ _ _ _ := rfl

theorem extract_toList_eq_slice (cs : Array Nat) (i j : Nat) :
    (cs.extract i j).toList = slice cs.toList i j := by
  simp [slice, Array.toList_extract]

theorem view_toArray_eq_extract (cs : Array Nat) (lo hi : Nat) :
    (view cs lo hi).toArray = cs.extract lo hi := by
  simp [view]

theorem slice_clamp_eq {α : Type} (inp : List α) (a b : Nat) :
    slice inp (min a inp.length) (min b inp.length) = slice inp a b := by
  unfold slice
  by_cases ha : a ≤ inp.length
  · rw [Nat.min_eq_left ha]
    by_cases hb : b ≤ inp.length
    · rw [Nat.min_eq_left hb]
    · rw [Nat.min_eq_right (by omega)]
      have hlen : (inp.drop a).length = inp.length - a := List.length_drop
      rw [List.take_of_length_le (by omega), List.take_of_length_le (by omega)]
  · have hgt : inp.length ≤ a := by omega
    rw [Nat.min_eq_right hgt, List.drop_of_length_le (Nat.le_refl _), List.drop_of_length_le hgt]
    simp

theorem impl_seqGet_nat {α : Type} (xs : Array α) (k : Nat) :
    Engine.Impl.seqGet xs (Engine.Impl.ofNat k) = xs[k]? := by
  show (Engine.Model.MathVal.idx (.int k)).bind (fun i => xs[i]?) = xs[k]?
  have h0 : (0 : Int) ≤ (k : Int) := Int.natCast_nonneg k
  simp [Engine.Model.MathVal.idx, h0]

private theorem nodeRel_restamp_gen {M : Ecma.Model} {st0 : Nat} {text : List Nat}
    {span : Nat → Nat → Nat × Nat} {nd : M.Node} {t : Tree}
    (hrel : Ecma.Model.NodeRel M st0 text span nd t) :
    ∀ {nd0 : Engine.Model.Node},
      M = Engine.Impl → HEq nd0 nd →
      Ecma.Model.NodeRel Engine.Impl st text span (Engine.restamp st nd0) t := by
  induction hrel with
  | @node span0 nd_m nt id ps i j kids hnt hprod hargs _ hsp hslen hsget hklen hkget _ ih =>
    intro nd0 hM hnd
    subst hM
    cases eq_of_heq hnd
    rcases nd0 with ⟨st0', lo, hi, p, nt0, ps0, ks, txt⟩
    rw [Engine.Impl.restamp_mk]
    have hkr := Engine.Impl.nodeKids_restamp st (.mk st0' lo hi p nt0 ps0 ks txt)
    rw [Engine.Impl.restamp_mk] at hkr
    refine .node hnt hprod hargs rfl hsp hslen hsget ?_ ?_ ?_
    · change Engine.Impl.seqLen (Engine.Impl.nodeKids _) = _
      rw [hkr]
      change Engine.Model.MathVal.int (Array.map (Engine.restamp st) _).size = _
      rw [Array.size_map]
      exact hklen
    · intro k
      change ((Engine.Impl.seqGet (Engine.Impl.nodeKids _) (Engine.Impl.ofNat k)).isSome = true) = _
      rw [hkr, impl_seqGet_nat, Array.getElem?_map, Option.isSome_map]
      have hk0 := hkget k; rw [impl_seqGet_nat] at hk0; exact hk0
    · intro k tk ck htk hck
      change Engine.Impl.seqGet (Engine.Impl.nodeKids _) (Engine.Impl.ofNat k) = some ck at hck
      rw [hkr, impl_seqGet_nat, Array.getElem?_map] at hck
      rcases opt_none_or_some ((Engine.Impl.nodeKids (.mk st0' lo hi p nt0 ps0 ks txt))[k]?) with hnone | ⟨c0, hc0⟩
      · rw [hnone] at hck; cases hck
      · rw [hc0, Option.map_some, Option.some.injEq] at hck
        subst hck
        exact ih k tk c0 htk (by rw [impl_seqGet_nat]; exact hc0) rfl HEq.rfl
  | leaf _ hsp hslen hsget hklen =>
    intro nd0 hM hnd
    subst hM
    cases eq_of_heq hnd
    rcases nd0 with ⟨st0', lo, hi, p, nt0, ps0, ks, txt⟩
    rw [Engine.Impl.restamp_mk]
    have hkr := Engine.Impl.nodeKids_restamp st (.mk st0' lo hi p nt0 ps0 ks txt)
    rw [Engine.Impl.restamp_mk] at hkr
    refine .leaf rfl hsp hslen hsget ?_
    change Engine.Impl.seqLen (Engine.Impl.nodeKids _) = _
    rw [hkr]
    change Engine.Model.MathVal.int (Array.map (Engine.restamp st) _).size = _
    rw [Array.size_map]
    exact hklen
  | lex _ ih =>
    intro nd0 hM hnd
    exact .lex (ih hM hnd)

theorem nodeRel_restamp (st : Nat) {st0 : Nat} {text : List Nat}
    {span : Nat → Nat → Nat × Nat} {nd : Engine.Model.Node} {t : Tree}
    (hrel : Ecma.Model.NodeRel Engine.Impl st0 text span nd t) :
    Ecma.Model.NodeRel Engine.Impl st text span (Engine.restamp st nd) t :=
  nodeRel_restamp_gen (st := st) hrel rfl HEq.rfl

theorem nodeRel_congr_root_params {M : Ecma.Model} {st : Nat} {text : List Nat}
    {span : Nat → Nat → Nat × Nat} {nd : M.Node} {nt : NT} {id : Nat}
    {ps1 ps2 : List Param} {i j : Nat} {kids : List Tree}
    (hp : ∀ p, p ∈ ps1 ↔ p ∈ ps2)
    (hrel : Ecma.Model.NodeRel M st text span nd (.node nt id ps1 i j kids)) :
    Ecma.Model.NodeRel M st text span nd (.node nt id ps2 i j kids) := by
  cases hrel with
  | node hnt hprod hargs hst hsp hslen hsget hklen hkget hkids =>
    exact .node hnt hprod (fun p => (hargs p).trans (hp p)) hst hsp hslen hsget hklen hkget hkids

theorem step_congr_root_params {α : Type} {A : Alphabet α} {neg : NT → List Param → Nat → Nat → Prop}
    {inp : List α} {gl : GL} {cx : Ctx} {g : GrammarId}
    {n : NT} {id : Nat} {ps1 ps2 : List Param} {i j : Nat} {kids : List Tree}
    (hp : ∀ p, p ∈ ps1 ↔ p ∈ ps2)
    (hs : Step A neg inp gl cx g n ps1 i j (.node n id ps1 i j kids)) :
    Step A neg inp gl cx g n ps2 i j (.node n id ps2 i j kids) := by
  have hc : ∀ p, ps1.contains p = ps2.contains p := fun p => by
    apply Bool.eq_iff_iff.mpr; simp only [List.contains_iff_mem]; exact hp p
  have hseqCongr : ∀ {s k is a b m ts},
      Seq A neg inp gl cx g s ps1 k is a b m ts →
      Seq A neg inp gl cx g s ps2 k is a b m ts := by
    intro s k is
    induction is generalizing k with
    | nil => intro a b m ts h; cases h; exact .nil
    | cons it rest ih =>
      intro a b m ts h
      cases h with
      | absent hr => exact .absent (ih hr)
      | term ht hr => exact .term ht (ih hr)
      | nt hst hcd hr => rw [applyArgs_eq_of_contains hc] at hst; exact .nt hst hcd (ih hr)
      | @butNotT _ _ _ _ ex _ _ _ _ _ _ ht hex hr =>
        refine .butNotT ht (fun hx => hex ?_) (ih hr)
        cases ex with
        | sym y =>
          cases y with
          | t _ => exact hx
          | nt m' args' => dsimp only [Excluded] at hx ⊢; rwa [applyArgs_eq_of_contains hc]
        | oneOf ys _ =>
          obtain ⟨y, hy, hsy⟩ := hx
          refine ⟨y, hy, ?_⟩
          cases y with
          | t _ => exact hsy
          | nt m' args' => dsimp only at hsy ⊢; rwa [applyArgs_eq_of_contains hc]
      | @butNotN _ _ _ _ _ ex _ _ _ _ _ _ _ hst hex hr =>
        rw [applyArgs_eq_of_contains hc] at hst
        refine .butNotN hst (fun hx => hex ?_) (ih hr)
        cases ex with
        | sym y =>
          cases y with
          | t _ => exact hx
          | nt m' args' => dsimp only [Excluded] at hx ⊢; rwa [applyArgs_eq_of_contains hc]
        | oneOf ys _ =>
          obtain ⟨y, hy, hsy⟩ := hx
          refine ⟨y, hy, ?_⟩
          cases y with
          | t _ => exact hsy
          | nt m' args' => dsimp only at hsy ⊢; rwa [applyArgs_eq_of_contains hc]
      | phrase hph hr => exact .phrase hph (ih hr)
      | look hlk hr => exact .look hlk (ih hr)
      | noLT hnl hr => exact .noLT hnl (ih hr)
      | empty hr => exact .empty (ih hr)
      | onlyIf hr => exact .onlyIf (ih hr)
  cases hs with
  | node s hsMem hgrd hpid hseq =>
    have hgrd2 : s.alt.guard.all (Guard.holds ps2) = true := by
      rw [← hgrd]; congr 1; funext g0; exact (guardHolds_eq_of_contains hc g0).symm
    exact .node s hsMem hgrd2 hpid (hseqCongr hseq)

theorem derives_congr_params {α : Type} {A : Alphabet α} {gl : GL} {cx : Ctx} {g : GrammarId}
    {inp : List α} {n : NT} {ps1 ps2 : List Param} {i j : Nat} {t : Tree}
    (hp : ∀ p, p ∈ ps1 ↔ p ∈ ps2)
    (hd : Derives gl cx g A inp n ps1 i j t) :
    ∃ t', t'.nt? = t.nt? ∧ t'.span = t.span ∧
      (∀ M st text span nd, Ecma.Model.NodeRel M st text span nd t → Ecma.Model.NodeRel M st text span nd t') ∧
      (∀ D, t.Commits gl cx g D → (∀ (a id' : Nat) (ks' : List Tree) (_k1 _k2 : Nat), D n ps2 i a (.node n id' ps2 i a ks') →
        ∃ ks'', D n ps1 i a (.node n id' ps1 i a ks'')) → t'.Commits gl cx g D) ∧
      Derives gl cx g A inp n ps2 i j t' := by
  obtain ⟨K, hK⟩ := hd
  have hstep1 := hK (max K 1) (Nat.le_max_left K 1)
  obtain ⟨k0, hk0⟩ : ∃ k0, max K 1 = k0 + 1 := ⟨max K 1 - 1, by omega⟩
  rw [hk0] at hstep1
  dsimp only [DerivesAt] at hstep1
  cases t with
  | leaf a b => cases hstep1
  | lex idx sub =>
    refine ⟨.lex idx sub, rfl, rfl, fun _ _ _ _ _ h => h, fun _ h _ => h, max K 1, fun k hk => ?_⟩
    obtain ⟨km, rfl⟩ : ∃ km, k = km + 1 := ⟨k - 1, by omega⟩
    have hsk := hK (km + 1) (Nat.le_trans (Nat.le_max_left K 1) hk)
    dsimp only [DerivesAt] at hsk ⊢
    cases hsk with
    | lex halts hinp hleaf => exact .lex halts hinp hleaf
  | node m id ps0 a b kids =>
    obtain ⟨rfl, rfl, rfl, rfl⟩ : n = m ∧ ps1 = ps0 ∧ i = a ∧ j = b :=
      match hstep1 with | .node _ _ _ _ _ => ⟨rfl, rfl, rfl, rfl⟩
    refine ⟨.node n id ps2 i j kids, rfl, rfl,
      fun _ _ _ _ _ h => nodeRel_congr_root_params hp h,
      fun D hcom hback => ?_,
      max K 1, fun k hk => ?_⟩
    · obtain ⟨hroot, hkids⟩ := hcom
      refine ⟨fun hord h' id' ks' k1 k2 hd2 hap1 hap2 => ?_, hkids⟩
      obtain ⟨ks'', hd1⟩ := hback h' id' ks' k1 k2 hd2
      exact hroot hord h' id' ks'' k1 k2 hd1 hap1 hap2
    · obtain ⟨km, rfl⟩ : ∃ km, k = km + 1 := ⟨k - 1, by omega⟩
      have hsk := hK (km + 1) (Nat.le_trans (Nat.le_max_left K 1) hk)
      exact step_congr_root_params hp hsk

/-! ## Code-point primitive matching -/

/-- `B`'s character predicates agree with `P`'s `<USP>` and `Phrase` classes. -/
def CodePrimsMatch {N : Type} (B : Builder N) (P : CodePrims) : Prop :=
  (∀ c, B.usp c = true ↔ P.usp c) ∧
  (∀ ph c, Code.phraseOk B ph c = true ↔ P.phrase ph c)

/-- `Code.condAt grp cs` agrees with `P.cond` on subtrees spanning `i .. h ≤ cs.size`. -/
def CondMatch (grp : Option (Nat → Bool)) (cs : Array Nat) (P : CodePrims) : Prop :=
  ∀ ph i h t, h ≤ cs.size → t.span = (i, h) →
    (Code.condAt grp cs ph i h = true ↔ P.cond ph cs.toList t)

theorem codePrimsMatch_engine : CodePrimsMatch Engine.builder Engine.Model.codePrims := by
  refine ⟨fun _ => Iff.rfl, fun ph c => ?_⟩
  cases ph <;> simp [Code.phraseOk, Engine.builder, Engine.Model.codePrims]

theorem codePrimsMatch_withGroup {N : Type} {B : Builder N} {P : CodePrims}
    (hm : CodePrimsMatch B P) (c : List Nat → Tree → Prop) :
    CodePrimsMatch B (P.withGroup c) :=
  hm

theorem condOk_iff_codePrims (cs : Array Nat) (ph : Phrase) (i h : Nat) (t : Tree)
    (ht : t.span = (i, h)) :
    Code.condOk cs ph i h = true ↔ Engine.Model.codePrims.cond ph cs.toList t := by
  unfold Code.condOk Engine.Model.codePrims
  dsimp only
  rw [ht, extract_toList_eq_slice]
  cases ph with
  | groupNumberAtMostCount => simp
  | _ =>
    simp only [Option.any_eq_true]
    constructor <;> rintro ⟨v, hv, hb⟩ <;> refine ⟨v, hv, ?_⟩ <;>
      (simp only [Bool.and_eq_true, Bool.not_eq_true', Bool.and_eq_false_imp, decide_eq_true_eq, decide_eq_false_iff_not] at hb ⊢; omega)

theorem condMatch_none (cs : Array Nat) :
    CondMatch none cs Engine.Model.codePrims := by
  intro ph i h t _ ht
  exact condOk_iff_codePrims cs ph i h t ht

theorem condMatch_withGroup (cs : Array Nat) (f : Nat → Bool) (c : List Nat → Tree → Prop)
    (hf : ∀ t, t.span.2 ≤ cs.size → (f (Ecma.Grammar.decimalMV (slice cs.toList t.span.1 t.span.2)) = true ↔ c cs.toList t)) :
    CondMatch (some f) cs (Engine.Model.codePrims.withGroup c) := by
  intro ph i h t hh ht
  cases ph with
  | groupNumberAtMostCount =>
    unfold Code.condAt Code.decimalMV CodePrims.withGroup
    dsimp only
    rw [extract_toList_eq_slice]
    have hsp1 : t.span.1 = i := by rw [ht]
    have hsp2 : t.span.2 = h := by rw [ht]
    rw [← hsp1, ← hsp2]
    exact hf t (hsp2 ▸ hh)
  | _ =>
    unfold Code.condAt CodePrims.withGroup
    exact condOk_iff_codePrims cs _ i h t ht

/-! ## `Code.termEnd` and `Code.startsWith` -/

theorem codeTerm_bound {N : Type} (B : Builder N) (cs : Array Nat) (x : Terminal) (i j : Nat)
    (h : Code.termEnd B cs x i = some j) :
    i < j ∧ j ≤ cs.size := by
  unfold Code.termEnd at h
  cases x with
  | text str _ =>
    dsimp only at h
    by_cases hc : (0 < (str.toList.map Char.toNat).length &&
        i + (str.toList.map Char.toNat).length ≤ cs.size &&
        (cs.extract i (i + (str.toList.map Char.toNat).length)).toList == str.toList.map Char.toNat) = true
    · simp only [hc, ↓reduceIte, Option.some.injEq] at h
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
      omega
    · simp only [hc, Bool.false_eq_true, ↓reduceIte] at h; cases h
  | cp cn =>
    dsimp only at h
    rcases opt_none_or_some cs[i]? with hnone | ⟨c, hc⟩
    · rw [hnone] at h; cases h
    · rw [hc] at h
      have hlt : i < cs.size := (Array.getElem?_eq_some_iff.mp hc).1
      dsimp only [Bind.bind, Option.bind] at h
      cases hcp : cn.codePoint with
      | some v =>
        rw [hcp] at h
        by_cases hv : (c == v) = true
        · simp only [hv, ↓reduceIte, Option.some.injEq] at h; omega
        · simp only [hv, Bool.false_eq_true, ↓reduceIte] at h; cases h
      | none =>
        rw [hcp] at h
        by_cases hu : B.usp c = true
        · simp only [hu, ↓reduceIte, Option.some.injEq] at h; omega
        · simp only [hu, Bool.false_eq_true, ↓reduceIte] at h; cases h

theorem codeTerm_sound {N : Type} {B : Builder N} {P : CodePrims}
    (hm : CodePrimsMatch B P) (cs : Array Nat) (s : Src) (k : Nat) (x : Terminal) (i j : Nat)
    (h : Code.termEnd B cs x i = some j) :
    i < j ∧ j ≤ cs.size ∧ (codeAlphabet P).term s k x (slice cs.toList i j) := by
  have ⟨hlt, hle⟩ := codeTerm_bound B cs x i j h
  refine ⟨hlt, hle, ?_⟩
  unfold Code.termEnd at h
  cases x with
  | text str _ =>
    dsimp only [codeAlphabet] at h ⊢
    by_cases hc : (0 < (str.toList.map Char.toNat).length &&
        i + (str.toList.map Char.toNat).length ≤ cs.size &&
        (cs.extract i (i + (str.toList.map Char.toNat).length)).toList == str.toList.map Char.toNat) = true
    · simp only [hc, ↓reduceIte, Option.some.injEq] at h
      subst h
      simp only [Bool.and_eq_true, beq_iff_eq] at hc
      rw [← extract_toList_eq_slice]
      exact hc.2
    · simp only [hc, Bool.false_eq_true, ↓reduceIte] at h; cases h
  | cp cn =>
    dsimp only [codeAlphabet] at h ⊢
    rcases opt_none_or_some cs[i]? with hnone | ⟨c, hc⟩
    · rw [hnone] at h; cases h
    · rw [hc] at h
      dsimp only [Bind.bind, Option.bind] at h
      have hgetL : cs.toList[i]? = some c := by simpa using hc
      cases hcp : cn.codePoint with
      | some v =>
        rw [hcp] at h
        by_cases hv : (c == v) = true
        · simp only [hv, ↓reduceIte, Option.some.injEq] at h
          subst h
          rw [beq_iff_eq] at hv; subst hv
          have hdrop : cs.toList.drop i = c :: cs.toList.drop (i + 1) := by
            obtain ⟨hi, hval⟩ := List.getElem?_eq_some_iff.mp hgetL
            rw [List.drop_eq_getElem_cons hi, hval]
          exact (slice_singleton_iff (by omega) (by simpa using hle)).mpr ⟨rfl, hgetL, hdrop⟩
        · simp only [hv, Bool.false_eq_true, ↓reduceIte] at h; cases h
      | none =>
        rw [hcp] at h
        by_cases hu : B.usp c = true
        · simp only [hu, ↓reduceIte, Option.some.injEq] at h
          subst h
          have hdrop : cs.toList.drop i = c :: cs.toList.drop (i + 1) := by
            obtain ⟨hi, hval⟩ := List.getElem?_eq_some_iff.mp hgetL
            rw [List.drop_eq_getElem_cons hi, hval]
          exact ⟨c, (slice_singleton_iff (by omega) (by simpa using hle)).mpr ⟨rfl, hgetL, hdrop⟩, (hm.1 c).mp hu⟩
        · simp only [hu, Bool.false_eq_true, ↓reduceIte] at h; cases h

theorem codeTerm_complete {N : Type} {B : Builder N} {P : CodePrims}
    (hm : CodePrimsMatch B P) (cs : Array Nat) {s : Src} {k : Nat} {x : Terminal} {i j : Nat}
    (hokx : codeLookTermOk x = true) (hj : j ≤ cs.size)
    (ht : (codeAlphabet P).term s k x (slice cs.toList i j)) :
    Code.termEnd B cs x i = some j := by
  have hne := codeTerm_nonempty hokx ht
  have ⟨hlt, _⟩ := slice_nonempty_lt hne
  have hjL : j ≤ cs.toList.length := by simpa using hj
  unfold Code.termEnd
  cases x with
  | text str _ =>
    dsimp only [codeAlphabet] at ht ⊢
    obtain ⟨hlen, _⟩ := (slice_eq_iff_drop (Nat.le_of_lt hlt) hjL).mp ht
    have hwpos : decide (0 < (str.toList.map Char.toNat).length) = true := decide_eq_true (by omega)
    have hjEq : j = i + (str.toList.map Char.toNat).length := by omega
    subst hjEq
    have hjB : decide (i + (str.toList.map Char.toNat).length ≤ cs.size) = true := decide_eq_true hj
    have hexEq : ((cs.extract i (i + (str.toList.map Char.toNat).length)).toList == str.toList.map Char.toNat) = true := by
      rw [beq_iff_eq, extract_toList_eq_slice]; exact ht
    have hc : (decide (0 < (str.toList.map Char.toNat).length) &&
        decide (i + (str.toList.map Char.toNat).length ≤ cs.size) &&
        (cs.extract i (i + (str.toList.map Char.toNat).length)).toList == str.toList.map Char.toNat) = true :=
      Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨hwpos, hjB⟩, hexEq⟩
    simp only [hc, ↓reduceIte]
  | cp cn =>
    dsimp only [codeAlphabet] at ht ⊢
    cases hcp : cn.codePoint with
    | some v =>
      rw [hcp] at ht
      obtain ⟨rfl, hgetL, _⟩ := (slice_singleton_iff (Nat.le_of_lt hlt) hjL).mp ht
      have hget : cs[i]? = some v := by simpa using hgetL
      rw [hget]; simp
    | none =>
      rw [hcp] at ht
      obtain ⟨c, hsc, husp⟩ := ht
      obtain ⟨rfl, hgetL, _⟩ := (slice_singleton_iff (Nat.le_of_lt hlt) hjL).mp hsc
      have hget : cs[i]? = some c := by simpa using hgetL
      rw [hget]; simp [(hm.1 c).mpr husp]

theorem startsWith_iff {N : Type} {B : Builder N} {P : CodePrims}
    (hm : CodePrimsMatch B P) (cs : Array Nat) (s : Src) :
    ∀ (q : List LookItem) (j : Nat),
      (q.all fun | .noLT => true | .t x => codeLookTermOk x) = true →
      (Code.startsWith B cs q j = true ↔ StartsWith (codeAlphabet P) cs.toList s q j)
  | [], _ => fun _ => by simp [Code.startsWith, StartsWith]
  | .noLT :: rest, j => fun hq => by
    simp only [List.all_cons, Bool.true_and] at hq
    simp only [Code.startsWith, StartsWith, codeAlphabet, true_and]
    exact startsWith_iff hm cs s rest j hq
  | .t x :: rest, j => fun hq => by
    simp only [List.all_cons, Bool.and_eq_true] at hq
    obtain ⟨hx, hrest⟩ := hq
    unfold Code.startsWith StartsWith
    dsimp only [codeAlphabet]
    rcases opt_none_or_some (Code.termEnd B cs x j) with hnone | ⟨h, hh⟩
    · rw [hnone]
      simp only [Bool.false_eq_true, false_iff, not_exists, not_and]
      intro h' _ hhle hterm _
      have := codeTerm_complete hm cs (s := s) (k := 0) hx (by simpa using hhle) hterm
      rw [hnone] at this; cases this
    · rw [hh]
      obtain ⟨hlt, hle, hterm⟩ := codeTerm_sound hm cs s 0 x j h hh
      simp only [Bool.and_eq_true, decide_eq_true_eq]
      constructor
      · rintro ⟨_, hsw⟩
        exact ⟨h, hlt, by simpa using hle, hterm, (startsWith_iff hm cs s rest h hrest).mp hsw⟩
      · rintro ⟨h', _, hhle', hterm', hsw'⟩
        have hh' := codeTerm_complete hm cs (s := s) (k := 0) hx (by simpa using hhle') hterm'
        have heq : h' = h := Option.some.inj (hh'.symm.trans hh)
        subst heq
        exact ⟨hlt, (startsWith_iff hm cs s rest h' hrest).mpr hsw'⟩

/-! ## `AlphaSpec` instance for `Code.alpha` -/

def codeAlphaSpec {N T : Type} (B : Builder N) (cs : Array Nat) (g : GrammarId) (cx : Ctx)
    (off : Nat) (src : Array Nat) (grp : Option (Nat → Bool)) :
    AlphaSpec B (Code.alpha (T := T) B cs g cx off src grp) cs.size where
  Inv _ := True
  Term _ _ x i j := Code.termEnd B cs x i = some j
  Leaf _ _ _ := False
  Phrase ph i j := ∃ c, cs[i]? = some c ∧ Code.phraseOk B ph c = true ∧ j = i + 1
  Cond ph a b := Code.condAt grp cs ph a b = true
  NoLT _ := True
  Starts q i := Code.startsWith B cs q i = true
  NegSpan n ps a b := Code.dec B cs g cx 16 n ps a b = true
  NegAny n a := Code.decAny B cs g cx n a = true
  SpanOf a b := (off + a, off + b)
  TextOf a b := src.extract (off + a) (off + b)
  LeafNodeRel _ _ _ _ _ := False
  inv_mono_memo _ _ _ _ _ _ _ _ := trivial
  inv_tick _ _ _ := trivial
  term_bound _ _ x i j h := codeTerm_bound B cs x i j h
  leaf_bound _ _ _ h := nomatch h
  phrase_bound _ i j h := by
    obtain ⟨c, hc, _, rfl⟩ := h
    have hlt := (Array.getElem?_eq_some_iff.mp hc).1
    omega
  term_det _ _ _ _ _ _ h1 h2 := Option.some.inj (h1.symm.trans h2)
  leaf_det _ _ _ _ h := nomatch h
  phrase_det _ _ _ _ h1 h2 := by
    obtain ⟨_, _, _, rfl⟩ := h1
    obtain ⟨_, _, _, rfl⟩ := h2
    rfl
  keepAll_sound _ _ _ _ := rfl
  hit_spec j st _ u st' hrun := by
    dsimp only [Code.alpha] at hrun
    rw [sm_run_modify] at hrun
    cases hrun
    exact ⟨trivial, rfl, rfl, rfl, rfl, rfl, rfl⟩
  term_spec _ _ x i st _ r st' hrun := by
    dsimp only [Code.alpha] at hrun
    obtain ⟨hr, rfl⟩ := sm_pure_ok hrun
    subst hr
    refine ⟨trivial, rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
    rcases opt_none_or_some (Code.termEnd B cs x i) with hnone | ⟨j, hj⟩
    · exact Or.inr ⟨hnone, fun j h => by rw [hnone] at h; cases h⟩
    · exact Or.inl ⟨j, hj, hj⟩
  leaf_spec _ _ st _ r st' hrun := by
    dsimp only [Code.alpha] at hrun
    obtain ⟨hr, rfl⟩ := sm_pure_ok hrun
    subst hr
    exact ⟨trivial, rfl, rfl, rfl, rfl, rfl, rfl, Or.inr ⟨rfl, fun _ h => h⟩⟩
  phrase_spec ph i st _ r st' hrun := by
    dsimp only [Code.alpha] at hrun
    rcases opt_none_or_some cs[i]? with hnone | ⟨c, hc⟩
    · rw [hnone] at hrun
      obtain ⟨hr, rfl⟩ := sm_pure_ok hrun
      subst hr
      exact ⟨trivial, rfl, rfl, rfl, rfl, rfl, rfl,
        Or.inr ⟨rfl, fun _ ⟨_, hc', _⟩ => by rw [hnone] at hc'; cases hc'⟩⟩
    · rw [hc] at hrun
      obtain ⟨hr, rfl⟩ := sm_pure_ok hrun
      subst hr
      refine ⟨trivial, rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
      by_cases hp : Code.phraseOk B ph c = true
      · simp only [hp, ↓reduceIte]
        exact Or.inl ⟨i + 1, rfl, c, hc, hp, rfl⟩
      · have hpF : Code.phraseOk B ph c = false := Bool.eq_false_iff.mpr hp
        rw [hpF]
        refine Or.inr ⟨rfl, fun _ ⟨c', hc', hp', _⟩ => ?_⟩
        rw [hc] at hc'; injection hc' with hcc; subst hcc; exact hp hp'
  cond_spec c a b st _ r st' hrun := by
    dsimp only [Code.alpha] at hrun
    obtain ⟨hr, rfl⟩ := sm_pure_ok hrun
    subst hr
    exact ⟨trivial, rfl, rfl, rfl, rfl, rfl, rfl, Iff.rfl⟩
  noLT_spec _ st _ r st' hrun := by
    dsimp only [Code.alpha] at hrun
    obtain ⟨hr, rfl⟩ := sm_pure_ok hrun
    subst hr
    exact ⟨trivial, rfl, rfl, rfl, rfl, rfl, rfl, ⟨fun _ => trivial, fun _ => rfl⟩⟩
  starts_spec _ _ st _ _ r st' hrun := by
    dsimp only [Code.alpha] at hrun
    obtain ⟨hr, rfl⟩ := sm_pure_ok hrun
    subst hr
    exact ⟨trivial, rfl, rfl, rfl, rfl, rfl, rfl, Iff.rfl⟩
  negSpan_spec _ _ _ _ st _ _ r st' hrun := by
    dsimp only [Code.alpha] at hrun
    obtain ⟨hr, rfl⟩ := sm_pure_ok hrun
    subst hr
    exact ⟨trivial, rfl, rfl, rfl, rfl, rfl, rfl, Iff.rfl⟩
  negAny_spec _ _ st _ _ r st' hrun := by
    dsimp only [Code.alpha] at hrun
    obtain ⟨hr, rfl⟩ := sm_pure_ok hrun
    subst hr
    exact ⟨trivial, rfl, rfl, rfl, rfl, rfl, rfl, Iff.rfl⟩
  span_spec _ _ st _ r st' hrun := by
    dsimp only [Code.alpha] at hrun
    obtain ⟨hr, rfl⟩ := sm_pure_ok hrun
    exact ⟨trivial, rfl, rfl, rfl, rfl, rfl, rfl, hr.symm⟩
  text_spec lo hi st _ r st' hrun := by
    dsimp only [Code.alpha] at hrun
    obtain ⟨hr, rfl⟩ := sm_pure_ok hrun
    subst hr
    exact ⟨trivial, rfl, rfl, rfl, rfl, rfl, rfl, view_toArray_eq_extract src (off + lo) (off + hi)⟩
  leafNode_spec _ _ _ _ st _ _ _ _ hrun := by
    dsimp only [Code.alpha] at hrun
    rw [sm_run_throw] at hrun; cases hrun

/-! ## Exactness of `Code.dec`, `Code.decSeq`, `Code.decAny`, and span clamping -/

private def posItemOk (cx : Ctx) (g : GrammarId) (f : Nat) : Item → Bool
  | .sym (.t _) _ | .phrase _ | .empty | .noLT => true
  | .sym (.nt m _) _ => posBounded cx g f m
  | _ => false

private theorem condOk_of_posItems {P : CodePrims} {inp : List Nat} {cx : Ctx} {g : GrammarId} {f : Nat}
    {is : List Item} (hpos : ∀ it ∈ is, posItemOk cx g f it = true) (t : Tree) :
    CondOk (codeAlphabet P) inp is t := by
  cases is with
  | nil => trivial
  | cons hd tl =>
    cases hd with
    | onlyIf c => have := hpos (.onlyIf c) List.mem_cons_self; cases this
    | _ => trivial

private theorem seq_masks {α : Type} {A : Alphabet α} {neg : NT → List Param → Nat → Nat → Prop}
    {inp : List α} {gl : GL} {cx : Ctx} {g : GrammarId} {s : Src} :
    ∀ {ps : List Param} {k : Nat} {is : List Item} {a b : Nat} {m : List Bool} {ts : List Tree},
      Ecma.Grammar.Seq A neg inp gl cx g s ps k is a b m ts →
      m ∈ masks ((is.filter fun | .sym _ true => true | _ => false).length) := by
  intro ps k is
  induction is generalizing k with
  | nil => intro _ _ _ _ hs0; cases hs0; simp [masks]
  | cons y ys ihy =>
    intro _ _ _ _ hs0
    cases hs0 with
    | absent hr =>
      rw [List.filter_cons_of_pos rfl, List.length_cons, masks]
      exact List.mem_append.mpr (Or.inl (List.mem_map.mpr ⟨_, ihy hr, rfl⟩))
    | @term _ _ _ _ o' _ _ _ _ _ _ _ hr =>
      cases o' with
      | false => simpa using ihy hr
      | true =>
        simp only [↓reduceIte, List.filter_cons, List.length_cons, masks]
        exact List.mem_append.mpr (Or.inr (List.mem_map.mpr ⟨_, ihy hr, rfl⟩))
    | @nt _ _ _ _ _ o' _ _ _ _ _ _ _ _ _ hr =>
      cases o' with
      | false => simpa using ihy hr
      | true =>
        simp only [↓reduceIte, List.filter_cons, List.length_cons, masks]
        exact List.mem_append.mpr (Or.inr (List.mem_map.mpr ⟨_, ihy hr, rfl⟩))
    | butNotT _ _ hr | butNotN _ _ hr | phrase _ hr | look _ hr
    | noLT _ hr | empty hr | onlyIf hr => simpa using ihy hr

private theorem decSeq_iff_seq (hok : parseTablesOk = true) {N : Type} {B : Builder N} {P : CodePrims}
    (hm : CodePrimsMatch B P) (cs : Array Nat) {cx : Ctx} {g : GrammarId} {f : Nat}
    {rec : NT → List Param → Nat → Nat → Bool}
    {neg : NT → List Param → Nat → Nat → Prop}
    (hrec : ∀ m ps' a b, posBounded cx g f m = true → b ≤ cs.size →
      (rec m ps' a b = true ↔ ∃ t, Step (codeAlphabet P) neg cs.toList Ecma.Spec.gl cx g m ps' a b t))
    (s : Src) (ps : List Param) :
    ∀ (k : Nat) (is : List Item) (i h : Nat),
      h ≤ cs.size →
      (∀ it ∈ is, srcItemTermOk it = true) →
      (∀ it ∈ is, posItemOk cx g f it = true) →
      (Code.decSeq B cs rec ps is i h = true ↔
        ∃ m kids, m ∈ masks ((is.filter fun | .sym _ true => true | _ => false).length) ∧
          Ecma.Grammar.Seq (codeAlphabet P) neg cs.toList Ecma.Spec.gl cx g s ps k is i h m kids) := by
  intro k is
  induction is generalizing k with
  | nil =>
    intro i h _ _ _
    simp only [Code.decSeq, beq_iff_eq]
    constructor
    · rintro rfl; exact ⟨[], [], by simp [masks], .nil⟩
    · rintro ⟨_, _, _, hseq⟩; cases hseq; rfl
  | cons it rest ih =>
    intro i h hh htok hpos
    have htokR : ∀ x ∈ rest, srcItemTermOk x = true := fun x hx => htok x (List.mem_cons_of_mem _ hx)
    have hposR : ∀ x ∈ rest, posItemOk cx g f x = true := fun x hx => hpos x (List.mem_cons_of_mem _ hx)
    have hpi : posItemOk cx g f it = true := hpos it List.mem_cons_self
    have hti : srcItemTermOk it = true := htok it List.mem_cons_self
    cases it with
    | sym sym0 o =>
      cases sym0 with
      | t x =>
        unfold Code.decSeq
        constructor
        · intro hd
          rcases Bool.or_eq_true_iff.mp hd with habs | hpres
          · simp only [Bool.and_eq_true] at habs
            obtain ⟨rfl, hdR⟩ := habs
            obtain ⟨m', ks', hm', hseq'⟩ := (ih (k + 1) i h hh htokR hposR).mp hdR
            refine ⟨false :: m', ks', ?_, .absent hseq'⟩
            rw [List.filter_cons_of_pos rfl, List.length_cons, masks]
            exact List.mem_append.mpr (Or.inl (List.mem_map.mpr ⟨m', hm', rfl⟩))
          · rcases opt_none_or_some (Code.termEnd B cs x i) with hnone | ⟨j, hj⟩
            · rw [hnone] at hpres; cases hpres
            · rw [hj] at hpres
              simp only [Bool.and_eq_true, decide_eq_true_eq] at hpres
              obtain ⟨hjh, hdR⟩ := hpres
              obtain ⟨_, _, hterm⟩ := codeTerm_sound hm cs s k x i j hj
              obtain ⟨m', ks', hm', hseq'⟩ := (ih (k + 1) j h hh htokR hposR).mp hdR
              refine ⟨if o then true :: m' else m', .leaf i j :: ks', ?_, .term hterm hseq'⟩
              cases o with
              | false => simpa using hm'
              | true =>
                simp only [↓reduceIte, List.filter_cons, List.length_cons, masks]
                exact List.mem_append.mpr (Or.inr (List.mem_map.mpr ⟨m', hm', rfl⟩))
        · rintro ⟨m, ks, _, hseq⟩
          cases hseq with
          | absent hseq' =>
            apply Bool.or_eq_true_iff.mpr; left
            simp only [Bool.true_and]
            exact (ih (k + 1) i h hh htokR hposR).mpr ⟨_, _, seq_masks hseq', hseq'⟩
          | @term _ _ _ _ _ _ _ j _ _ _ hterm hseq' =>
            apply Bool.or_eq_true_iff.mpr; right
            have hjh : j ≤ h := code_seq_le hok htokR hseq'
            have hjEnd := codeTerm_complete hm cs hti (Nat.le_trans hjh hh) hterm
            rw [hjEnd]
            simp only [Bool.and_eq_true, decide_eq_true_eq]
            refine ⟨hjh, (ih (k + 1) j h hh htokR hposR).mpr ⟨_, _, ?_, hseq'⟩⟩
            exact seq_masks hseq'
      | nt m args =>
        unfold Code.decSeq
        dsimp only [posItemOk] at hpi
        constructor
        · intro hd
          rcases Bool.or_eq_true_iff.mp hd with habs | hpres
          · simp only [Bool.and_eq_true] at habs
            obtain ⟨rfl, hdR⟩ := habs
            obtain ⟨m', ks', hm', hseq'⟩ := (ih (k + 1) i h hh htokR hposR).mp hdR
            refine ⟨false :: m', ks', ?_, .absent hseq'⟩
            rw [List.filter_cons_of_pos rfl, List.length_cons, masks]
            exact List.mem_append.mpr (Or.inl (List.mem_map.mpr ⟨m', hm', rfl⟩))
          · simp only [List.any_eq_true, List.mem_range, Bool.and_eq_true] at hpres
            obtain ⟨d, hdlt, hrm, hdR⟩ := hpres
            have hidh : i + d ≤ h := by omega
            obtain ⟨tm, hstm⟩ := (hrec m (applyArgs ps args) i (i + d) hpi (Nat.le_trans hidh hh)).mp hrm
            obtain ⟨m', ks', hm', hseq'⟩ := (ih (k + 1) (i + d) h hh htokR hposR).mp hdR
            refine ⟨if o then true :: m' else m', tm :: ks', ?_, .nt hstm (condOk_of_posItems hposR tm) hseq'⟩
            cases o with
            | false => simpa using hm'
            | true =>
              simp only [↓reduceIte, List.filter_cons, List.length_cons, masks]
              exact List.mem_append.mpr (Or.inr (List.mem_map.mpr ⟨m', hm', rfl⟩))
        · rintro ⟨m0, ks0, _, hseq⟩
          cases hseq with
          | absent hseq' =>
            apply Bool.or_eq_true_iff.mpr; left
            simp only [Bool.true_and]
            exact (ih (k + 1) i h hh htokR hposR).mpr ⟨_, _, seq_masks hseq', hseq'⟩
          | @nt _ _ _ _ _ _ _ _ j _ _ tm _ hstm _ hseq' =>
            apply Bool.or_eq_true_iff.mpr; right
            have hij : i ≤ j := code_step_le hok hstm
            have hjh : j ≤ h := code_seq_le hok htokR hseq'
            simp only [List.any_eq_true, List.mem_range, Bool.and_eq_true]
            refine ⟨j - i, by omega, ?_, ?_⟩
            · rw [show i + (j - i) = j from by omega]
              exact (hrec m (applyArgs ps args) i j hpi (Nat.le_trans hjh hh)).mpr ⟨tm, hstm⟩
            · rw [show i + (j - i) = j from by omega]
              exact (ih (k + 1) j h hh htokR hposR).mpr ⟨_, _, seq_masks hseq', hseq'⟩
    | phrase p =>
      unfold Code.decSeq
      constructor
      · intro hd
        rcases opt_none_or_some cs[i]? with hnone | ⟨c, hc⟩
        · rw [hnone] at hd; cases hd
        · rw [hc] at hd
          simp only [Bool.and_eq_true, decide_eq_true_eq] at hd
          obtain ⟨⟨hpok, hi1h⟩, hdR⟩ := hd
          obtain ⟨m', ks', hm', hseq'⟩ := (ih (k + 1) (i + 1) h hh htokR hposR).mp hdR
          have hgetL : cs.toList[i]? = some c := by simpa using hc
          have hdrop : cs.toList.drop i = c :: cs.toList.drop (i + 1) := by
            obtain ⟨hiL, hvL⟩ := List.getElem?_eq_some_iff.mp hgetL
            rw [List.drop_eq_getElem_cons hiL, hvL]
          have hsc : slice cs.toList i (i + 1) = [c] :=
            (slice_singleton_iff (by omega) (by simpa using Nat.le_trans hi1h hh)).mpr ⟨rfl, hgetL, hdrop⟩
          exact ⟨m', .leaf i (i + 1) :: ks', by simpa using hm', .phrase ⟨c, hsc, (hm.2 p c).mp hpok⟩ hseq'⟩
      · rintro ⟨m0, ks0, hm0, hseq⟩
        cases hseq with
        | @phrase _ _ _ _ _ _ j _ _ _ hph hseq' =>
          obtain ⟨c, hsc, hpc⟩ := hph
          have hjh : j ≤ h := code_seq_le hok htokR hseq'
          have hlt : i < j := (slice_nonempty_lt (by rw [hsc]; exact List.cons_ne_nil _ _)).1
          obtain ⟨rfl, hgetL, _⟩ := (slice_singleton_iff (Nat.le_of_lt hlt) (by simpa using Nat.le_trans hjh hh)).mp hsc
          have hc : cs[i]? = some c := by simpa using hgetL
          rw [hc]
          simp only [Bool.and_eq_true, decide_eq_true_eq]
          exact ⟨⟨(hm.2 p c).mpr hpc, hjh⟩, (ih (k + 1) (i + 1) h hh htokR hposR).mpr ⟨m0, _, seq_masks hseq', hseq'⟩⟩
    | empty =>
      unfold Code.decSeq
      constructor
      · intro hd
        obtain ⟨m', ks', hm', hseq'⟩ := (ih (k + 1) i h hh htokR hposR).mp hd
        exact ⟨m', ks', by simpa using hm', .empty hseq'⟩
      · rintro ⟨m0, ks0, _, hseq⟩
        cases hseq with
        | empty hseq' => exact (ih (k + 1) i h hh htokR hposR).mpr ⟨_, _, seq_masks hseq', hseq'⟩
    | noLT =>
      unfold Code.decSeq
      constructor
      · intro hd
        obtain ⟨m', ks', hm', hseq'⟩ := (ih (k + 1) i h hh htokR hposR).mp hd
        exact ⟨m', ks', by simpa using hm', .noLT trivial hseq'⟩
      · rintro ⟨m0, ks0, hm0, hseq⟩
        cases hseq with
        | noLT _ hseq' => exact (ih (k + 1) i h hh htokR hposR).mpr ⟨m0, ks0, by simpa using hm0, hseq'⟩
    | butNot _ _ | lookahead _ | onlyIf _ =>
      cases hpi

theorem dec_iff_step (hok : parseTablesOk = true) {N : Type} {B : Builder N} {P : CodePrims}
    (hm : CodePrimsMatch B P) (cs : Array Nat) {cx : Ctx} {g : GrammarId} :
    ∀ (f : Nat) {n : NT} {ps : List Param} {i h : Nat}
      {neg : NT → List Param → Nat → Nat → Prop},
      posBounded cx g f n = true →
      h ≤ cs.size →
      (Code.dec B cs g cx f n ps i h = true ↔
        ∃ t, Step (codeAlphabet P) neg cs.toList Ecma.Spec.gl cx g n ps i h t) := by
  intro f
  induction f with
  | zero => intro _ _ _ _ _ hpb; cases hpb
  | succ f ih =>
    intro n ps i h neg hpb hh
    unfold posBounded at hpb
    rw [glData_eq] at hpb
    unfold Code.dec
    rw [altsOf_eq hok cx g n, List.any_eq_true]
    have hrec : ∀ m ps' a b, posBounded cx g f m = true → b ≤ cs.size →
        (Code.dec B cs g cx f m ps' a b = true ↔
          ∃ t, Step (codeAlphabet P) neg cs.toList Ecma.Spec.gl cx g m ps' a b t) :=
      fun _ _ _ _ hp hb => ih hp hb
    constructor
    · rintro ⟨e, heMem, hcond⟩
      simp only [Bool.and_eq_true] at hcond
      obtain ⟨hgrd, hdSeq⟩ := hcond
      have hposE : ∀ it ∈ e.alt.rhs, posItemOk cx g f it = true := by
        intro it hit
        have hall := List.all_eq_true.mp (List.all_eq_true.mp hpb e heMem) it hit
        cases it with
        | sym sym0 o => cases sym0 <;> exact hall
        | _ => exact hall
      have htokE : ∀ it ∈ e.alt.rhs, srcItemTermOk it = true :=
        fun it hit => srcItemTermOk_of_mem hok heMem hit
      obtain ⟨mask, kids, hmask, hseq⟩ := (decSeq_iff_seq hok hm cs hrec e ps 0 e.alt.rhs i h hh htokE hposE).mp hdSeq
      obtain ⟨_, hoptsEq⟩ := alt_lhs_and_opts hok heMem
      obtain ⟨_, id, _, hid, _⟩ := prodIdOf_spec hok heMem (hoptsEq ▸ hmask)
      exact ⟨.node n id ps i h kids, .node e heMem hgrd hid hseq⟩
    · rintro ⟨t, hst⟩
      cases hst with
      | lex _ _ hl => cases hl
      | node e heMem hgrd _ hseq =>
        have hposE : ∀ it ∈ e.alt.rhs, posItemOk cx g f it = true := by
          intro it hit
          have hall := List.all_eq_true.mp (List.all_eq_true.mp hpb e heMem) it hit
          cases it with
          | sym sym0 o => cases sym0 <;> exact hall
          | _ => exact hall
        have htokE : ∀ it ∈ e.alt.rhs, srcItemTermOk it = true :=
          fun it hit => srcItemTermOk_of_mem hok heMem hit
        refine ⟨e, heMem, Bool.and_eq_true_iff.mpr ⟨hgrd, ?_⟩⟩
        exact (decSeq_iff_seq hok hm cs hrec e ps 0 e.alt.rhs i h hh htokE hposE).mpr ⟨_, _, seq_masks hseq, hseq⟩

theorem decAny_iff_step (hok : parseTablesOk = true) {N : Type} {B : Builder N} {P : CodePrims}
    (hm : CodePrimsMatch B P) (cs : Array Nat) {cx : Ctx} {g : GrammarId} {m : NT} {j : Nat}
    {neg : NT → List Param → Nat → Nat → Prop}
    (hnt : (glData.alts cx g m).isEmpty = false ∧
      (glData.alts cx g m).all (fun e => e.alt.guard.isEmpty &&
        match e.alt.rhs with | [.sym (.t x) false] => codeLookTermOk x | _ => false) = true) :
    Code.decAny B cs g cx m j = true ↔
      ∃ h t, Step (codeAlphabet P) neg cs.toList Ecma.Spec.gl cx g m [] j h t := by
  unfold Code.decAny
  rw [altsOf_eq hok cx g m, List.any_eq_true]
  rw [glData_eq] at hnt
  constructor
  · rintro ⟨e, heMem, hcond⟩
    have heOk := List.all_eq_true.mp hnt.2 e heMem
    simp only [Bool.and_eq_true, List.isEmpty_iff] at heOk
    obtain ⟨hgrdNil, hrhsOk⟩ := heOk
    rw [hgrdNil] at hcond
    generalize hrhs : e.alt.rhs = rhs0 at hrhsOk hcond
    cases rhs0 with
    | nil => cases hrhsOk
    | cons it tl =>
      cases tl with
      | cons _ _ => cases it <;> simp at hrhsOk
      | nil =>
        cases it with
        | sym sym0 o =>
          cases sym0 with
          | nt _ _ => cases o <;> cases hrhsOk
          | t x =>
            cases o with
            | true => cases hrhsOk
            | false =>
              obtain ⟨h, hh⟩ := Option.isSome_iff_exists.mp hcond
              obtain ⟨_, _, hterm⟩ := codeTerm_sound hm cs e 0 x j h hh
              obtain ⟨_, hoptsEq⟩ := alt_lhs_and_opts hok heMem
              have hm0 : ([] : List Bool) ∈ masks e.alt.opts := by
                rw [hoptsEq, hrhs]; simp [masks]
              obtain ⟨_, id, _, hid, _⟩ := prodIdOf_spec hok heMem hm0
              refine ⟨h, .node m id [] j h [.leaf j h], .node e heMem ?_ hid ?_⟩
              · rw [hgrdNil]; rfl
              · rw [hrhs]; exact .term hterm .nil
        | _ => simp at hrhsOk
  · rintro ⟨h, t, hst⟩
    cases hst with
    | lex _ _ hl => cases hl
    | node e heMem _ _ hseq =>
      have heOk := List.all_eq_true.mp hnt.2 e heMem
      simp only [Bool.and_eq_true, List.isEmpty_iff] at heOk
      obtain ⟨hgrdNil, hrhsOk⟩ := heOk
      refine ⟨e, heMem, ?_⟩
      rw [hgrdNil]
      generalize hrhs : e.alt.rhs = rhs0 at hrhsOk hseq ⊢
      cases rhs0 with
      | nil => cases hrhsOk
      | cons it tl =>
        cases tl with
        | cons _ _ => cases it <;> simp at hrhsOk
        | nil =>
          cases it with
          | sym sym0 o =>
            cases sym0 with
            | nt _ _ => cases o <;> cases hrhsOk
            | t x =>
              cases o with
              | true => cases hrhsOk
              | false =>
                dsimp only at hrhsOk ⊢
                cases hseq with
                | term hterm hnil =>
                  cases hnil
                  have hne := codeTerm_nonempty hrhsOk hterm
                  have hjLtLen : j < cs.toList.length := by
                    apply Classical.byContradiction; intro hge
                    have hdropNil : cs.toList.drop j = [] := List.drop_of_length_le (by omega)
                    apply hne
                    unfold slice; rw [hdropNil]; simp
                  have hjLe : j ≤ cs.size := by simpa using Nat.le_of_lt hjLtLen
                  have hclamped : (codeAlphabet P).term e 0 x (slice cs.toList j (min h cs.size)) := by
                    have hminJ : min j cs.toList.length = j := Nat.min_eq_left (by simpa using hjLe)
                    have hminH : min h cs.toList.length = min h cs.size := by simp
                    rw [← hminJ, ← hminH, slice_clamp_eq]
                    exact hterm
                  have hend := codeTerm_complete hm cs (s := e) (k := 0) hrhsOk (Nat.min_le_right h cs.size) hclamped
                  rw [hend]; rfl
          | _ => simp at hrhsOk

private theorem posBounded_shift_zero (hok : parseTablesOk = true) {P : CodePrims}
    {neg : NT → List Param → Nat → Nat → Prop} {inp : List Nat} {cx : Ctx} {g : GrammarId} :
    ∀ (f : Nat) {n : NT} {ps : List Param} {a1 a2 : Nat} {t : Tree} (b : Nat),
      a1 = a2 →
      posBounded cx g f n = true →
      Step (codeAlphabet P) neg inp Ecma.Spec.gl cx g n ps a1 a2 t →
      ∃ t', Step (codeAlphabet P) neg inp Ecma.Spec.gl cx g n ps b b t' := by
  intro f
  induction f with
  | zero => intro _ _ _ _ _ _ _ hpb; cases hpb
  | succ f ih =>
    intro n ps a1 a2 t b haEq hpb hst
    unfold posBounded at hpb
    rw [glData_eq] at hpb
    cases hst with
    | lex _ _ hl => cases hl
    | node s hsMem hgrd hpid hseq =>
      subst haEq
      have hposS : ∀ it ∈ s.alt.rhs, posItemOk cx g f it = true := by
        intro it hit
        have hall := List.all_eq_true.mp (List.all_eq_true.mp hpb s hsMem) it hit
        cases it with
        | sym sym0 o => cases sym0 <;> exact hall
        | _ => exact hall
      have htokS : ∀ it ∈ s.alt.rhs, srcItemTermOk it = true :=
        fun it hit => srcItemTermOk_of_mem hok hsMem hit
      have hseqShift : ∀ {k is p1 p2 m ts},
          p1 = p2 →
          (∀ it ∈ is, srcItemTermOk it = true) →
          (∀ it ∈ is, posItemOk cx g f it = true) →
          Ecma.Grammar.Seq (codeAlphabet P) neg inp Ecma.Spec.gl cx g s ps k is p1 p2 m ts →
          ∃ ts', Ecma.Grammar.Seq (codeAlphabet P) neg inp Ecma.Spec.gl cx g s ps k is b b m ts' := by
        intro k is
        induction is generalizing k with
        | nil => intro _ _ _ _ _ _ _ hs0; cases hs0; exact ⟨[], .nil⟩
        | cons it rest ihr =>
          intro p1 p2 m ts hpEq htok hpos hs0
          subst hpEq
          have htokR := fun x hx => htok x (List.mem_cons_of_mem _ hx)
          have hposR := fun x hx => hpos x (List.mem_cons_of_mem _ hx)
          have hpi := hpos it List.mem_cons_self
          have hti := htok it List.mem_cons_self
          cases hs0 with
          | absent hr =>
            obtain ⟨ts', hr'⟩ := ihr rfl htokR hposR hr
            exact ⟨ts', .absent hr'⟩
          | @term _ _ _ _ _ _ _ mid _ _ _ ht hr =>
            have hlt := (slice_nonempty_lt (codeTerm_nonempty hti ht)).1
            have hle := code_seq_le hok htokR hr
            omega
          | @nt _ _ _ _ _ _ _ _ mid _ _ _ _ hstM _ hr =>
            have hle1 := code_step_le hok hstM
            have hle2 := code_seq_le hok htokR hr
            obtain ⟨tm', hstm'⟩ := ih b (by omega) hpi hstM
            obtain ⟨ts', hr'⟩ := ihr (by omega) htokR hposR hr
            exact ⟨tm' :: ts', .nt hstm' (condOk_of_posItems hposR tm') hr'⟩
          | @phrase _ _ _ _ _ _ mid _ _ _ hph hr =>
            obtain ⟨_, hsc, _⟩ := hph
            have hlt := (slice_nonempty_lt (by rw [hsc]; exact List.cons_ne_nil _ _)).1
            have hle := code_seq_le hok htokR hr
            omega
          | noLT _ hr =>
            obtain ⟨ts', hr'⟩ := ihr rfl htokR hposR hr
            exact ⟨ts', .noLT trivial hr'⟩
          | empty hr =>
            obtain ⟨ts', hr'⟩ := ihr rfl htokR hposR hr
            exact ⟨ts', .empty hr'⟩
          | butNotT _ _ _ | butNotN _ _ _ | look _ _ | onlyIf _ => cases hpi
      obtain ⟨kids', hseq'⟩ := hseqShift rfl htokS hposS hseq
      exact ⟨.node n _ ps b b kids', .node s hsMem hgrd hpid hseq'⟩

private theorem posBounded_stretch (hok : parseTablesOk = true) {P : CodePrims}
    {neg : NT → List Param → Nat → Nat → Prop} {inp : List Nat} {cx : Ctx} {g : GrammarId} :
    ∀ (f : Nat) {n : NT} {ps : List Param} {i b0 : Nat} {t : Tree} {h : Nat},
      b0 = inp.length →
      posBounded cx g f n = true →
      i < inp.length →
      inp.length ≤ h →
      Step (codeAlphabet P) neg inp Ecma.Spec.gl cx g n ps i b0 t →
      ∃ t', Step (codeAlphabet P) neg inp Ecma.Spec.gl cx g n ps i h t' := by
  intro f
  induction f with
  | zero => intro _ _ _ _ _ _ _ hpb; cases hpb
  | succ f ih =>
    intro n ps i b0 t h hb0 hpb hilt hh hst
    unfold posBounded at hpb
    rw [glData_eq] at hpb
    cases hst with
    | lex _ _ hl => cases hl
    | node s hsMem hgrd hpid hseq =>
      have hposS : ∀ it ∈ s.alt.rhs, posItemOk cx g f it = true := by
        intro it hit
        have hall := List.all_eq_true.mp (List.all_eq_true.mp hpb s hsMem) it hit
        cases it with
        | sym sym0 o => cases sym0 <;> exact hall
        | _ => exact hall
      have htokS : ∀ it ∈ s.alt.rhs, srcItemTermOk it = true :=
        fun it hit => srcItemTermOk_of_mem hok hsMem hit
      have hseqShiftZero : ∀ {k is p1 p2 m ts},
          p1 = p2 →
          (∀ it ∈ is, srcItemTermOk it = true) →
          (∀ it ∈ is, posItemOk cx g f it = true) →
          Ecma.Grammar.Seq (codeAlphabet P) neg inp Ecma.Spec.gl cx g s ps k is p1 p2 m ts →
          ∃ ts', Ecma.Grammar.Seq (codeAlphabet P) neg inp Ecma.Spec.gl cx g s ps k is h h m ts' := by
        intro k is
        induction is generalizing k with
        | nil => intro _ _ _ _ _ _ _ hs0; cases hs0; exact ⟨[], .nil⟩
        | cons it rest ihr =>
          intro p1 p2 m ts hpEq htok hpos hs0
          subst hpEq
          have htokR := fun x hx => htok x (List.mem_cons_of_mem _ hx)
          have hposR := fun x hx => hpos x (List.mem_cons_of_mem _ hx)
          have hpi := hpos it List.mem_cons_self
          have hti := htok it List.mem_cons_self
          cases hs0 with
          | absent hr => obtain ⟨ts', hr'⟩ := ihr rfl htokR hposR hr; exact ⟨ts', .absent hr'⟩
          | term ht hr =>
            have hlt := (slice_nonempty_lt (codeTerm_nonempty hti ht)).1
            have hle := code_seq_le hok htokR hr; omega
          | @nt _ _ _ _ _ _ _ _ mid _ _ _ _ hstM _ hr =>
            have hle1 := code_step_le hok hstM
            have hle2 := code_seq_le hok htokR hr
            obtain ⟨tm', hstm'⟩ := posBounded_shift_zero hok f h (by omega) hpi hstM
            obtain ⟨ts', hr'⟩ := ihr (by omega) htokR hposR hr
            exact ⟨tm' :: ts', .nt hstm' (condOk_of_posItems hposR tm') hr'⟩
          | phrase hph hr =>
            obtain ⟨_, hsc, _⟩ := hph
            have hlt := (slice_nonempty_lt (by rw [hsc]; exact List.cons_ne_nil _ _)).1
            have hle := code_seq_le hok htokR hr; omega
          | noLT _ hr => obtain ⟨ts', hr'⟩ := ihr rfl htokR hposR hr; exact ⟨ts', .noLT trivial hr'⟩
          | empty hr => obtain ⟨ts', hr'⟩ := ihr rfl htokR hposR hr; exact ⟨ts', .empty hr'⟩
          | butNotT _ _ _ | butNotN _ _ _ | look _ _ | onlyIf _ => cases hpi
      have hseqStretch : ∀ {k is a p2 m ts},
          p2 = inp.length →
          a < inp.length →
          (∀ it ∈ is, srcItemTermOk it = true) →
          (∀ it ∈ is, posItemOk cx g f it = true) →
          Ecma.Grammar.Seq (codeAlphabet P) neg inp Ecma.Spec.gl cx g s ps k is a p2 m ts →
          ∃ ts', Ecma.Grammar.Seq (codeAlphabet P) neg inp Ecma.Spec.gl cx g s ps k is a h m ts' := by
        intro k is
        induction is generalizing k with
        | nil => intro a p2 _ _ hp2 halt _ _ hs0; cases hs0; omega
        | cons it rest ihr =>
          intro a p2 m ts hp2 halt htok hpos hs0
          have htokR := fun x hx => htok x (List.mem_cons_of_mem _ hx)
          have hposR := fun x hx => hpos x (List.mem_cons_of_mem _ hx)
          have hpi := hpos it List.mem_cons_self
          have hti := htok it List.mem_cons_self
          cases hs0 with
          | absent hr =>
            obtain ⟨ts', hr'⟩ := ihr hp2 halt htokR hposR hr
            exact ⟨ts', .absent hr'⟩
          | @term _ _ _ _ _ _ _ mid _ _ _ ht hr =>
            have hleR := code_seq_le hok htokR hr
            by_cases hmidLt : mid < inp.length
            · obtain ⟨ts', hr'⟩ := ihr hp2 hmidLt htokR hposR hr
              exact ⟨.leaf a mid :: ts', .term ht hr'⟩
            · have hmidEq : mid = inp.length := by omega
              subst hmidEq
              have hscEq : slice inp a h = slice inp a inp.length := by
                rw [← slice_clamp_eq inp a h, Nat.min_eq_left (Nat.le_of_lt halt), Nat.min_eq_right hh]
              obtain ⟨ts', hr'⟩ := hseqShiftZero hp2.symm htokR hposR hr
              exact ⟨.leaf a h :: ts', .term (hscEq ▸ ht) hr'⟩
          | @nt _ _ _ _ _ _ _ _ mid _ _ tm _ hstM _ hr =>
            have hleR := code_seq_le hok htokR hr
            by_cases hmidLt : mid < inp.length
            · obtain ⟨ts', hr'⟩ := ihr hp2 hmidLt htokR hposR hr
              exact ⟨tm :: ts', .nt hstM (condOk_of_posItems hposR tm) hr'⟩
            · obtain ⟨tm', hstm'⟩ := ih (by omega) hpi halt hh hstM
              obtain ⟨ts', hr'⟩ := hseqShiftZero (by omega) htokR hposR hr
              exact ⟨tm' :: ts', .nt hstm' (condOk_of_posItems hposR tm') hr'⟩
          | @phrase _ _ _ _ _ _ mid _ _ _ hph hr =>
            have hleR := code_seq_le hok htokR hr
            by_cases hmidLt : mid < inp.length
            · obtain ⟨ts', hr'⟩ := ihr hp2 hmidLt htokR hposR hr
              exact ⟨.leaf a mid :: ts', .phrase hph hr'⟩
            · have hmidEq : mid = inp.length := by omega
              subst hmidEq
              have hscEq : slice inp a h = slice inp a inp.length := by
                rw [← slice_clamp_eq inp a h, Nat.min_eq_left (Nat.le_of_lt halt), Nat.min_eq_right hh]
              obtain ⟨ts', hr'⟩ := hseqShiftZero hp2.symm htokR hposR hr
              exact ⟨.leaf a h :: ts', .phrase (hscEq ▸ hph) hr'⟩
          | noLT _ hr =>
            obtain ⟨ts', hr'⟩ := ihr hp2 halt htokR hposR hr
            exact ⟨ts', .noLT trivial hr'⟩
          | empty hr =>
            obtain ⟨ts', hr'⟩ := ihr hp2 halt htokR hposR hr
            exact ⟨ts', .empty hr'⟩
          | butNotT _ _ _ | butNotN _ _ _ | look _ _ | onlyIf _ => cases hpi
      obtain ⟨kids', hseq'⟩ := hseqStretch hb0 hilt htokS hposS hseq
      exact ⟨.node n _ ps i h kids', .node s hsMem hgrd hpid hseq'⟩

def clampTree (L : Nat) : Tree → Tree
  | .leaf i j => .leaf (min i L) (min j L)
  | .lex k t => .lex k (clampTree L t)
  | .node n id ps i j kids => .node n id ps (min i L) (min j L) (kids.map (clampTree L))

private theorem clampTree_span (L : Nat) : ∀ t : Tree,
    t.isLeaf = true ∨ (∃ n id ps i j kids, t = .node n id ps i j kids) →
    (clampTree L t).span = (min t.span.1 L, min t.span.2 L)
  | .leaf _ _, _ => by simp [clampTree, Tree.span]
  | .node _ _ _ _ _ _, _ => by simp [clampTree, Tree.span]
  | .lex _ _, h => by
    rcases h with hl | ⟨_, _, _, _, _, _, heq⟩
    · cases hl
    · cases heq

private theorem code_step_past_end_eq (hok : parseTablesOk = true) {P : CodePrims}
    {neg : NT → List Param → Nat → Nat → Prop} {inp : List Nat} {cx : Ctx} {g : GrammarId} :
    ∀ (sz : Nat),
      (∀ {n ps a b t}, treeSize t ≤ sz → inp.length ≤ a →
        Step (codeAlphabet P) neg inp Ecma.Spec.gl cx g n ps a b t → a = b) ∧
      (∀ {s ps k is a b m ts}, treeSize.treeListSize ts ≤ sz →
        (∀ it ∈ is, srcItemTermOk it = true) → inp.length ≤ a →
        Ecma.Grammar.Seq (codeAlphabet P) neg inp Ecma.Spec.gl cx g s ps k is a b m ts → a = b) := by
  intro sz
  induction sz using Nat.strongRecOn with
  | ind sz ih =>
    have hst : ∀ {n ps a b t}, treeSize t ≤ sz → inp.length ≤ a →
        Step (codeAlphabet P) neg inp Ecma.Spec.gl cx g n ps a b t → a = b := by
      intro n ps a b t hsz ha hs
      cases hs with
      | lex _ _ hl => cases hl
      | node s hsMem _ _ hseq =>
        dsimp only [treeSize] at hsz
        exact (ih _ (by omega)).2 (Nat.le_refl _) (fun it hit => srcItemTermOk_of_mem hok hsMem hit) ha hseq
    refine ⟨hst, ?_⟩
    intro s ps k is
    induction is generalizing k with
    | nil => intro a b _ _ _ _ _ hseq; cases hseq; rfl
    | cons it rest ihr =>
      intro a b m ts hsz htok ha hseq
      have htokR := fun x hx => htok x (List.mem_cons_of_mem _ hx)
      cases hseq with
      | absent hr => exact ihr hsz htokR ha hr
      | term ht _ =>
        have hne := codeTerm_nonempty (htok _ List.mem_cons_self) ht
        unfold slice at hne; rw [List.drop_of_length_le ha] at hne; simp at hne
      | nt hs1 _ hr =>
        dsimp only [treeSize.treeListSize, treeSize] at hsz
        have heq1 := hst (by omega) ha hs1
        subst heq1
        exact ihr (by omega) htokR ha hr
      | butNotT ht _ _ =>
        have hne := codeTerm_nonempty (htok _ List.mem_cons_self) ht
        unfold slice at hne; rw [List.drop_of_length_le ha] at hne; simp at hne
      | butNotN hs1 _ hr =>
        dsimp only [treeSize.treeListSize, treeSize] at hsz
        have heq1 := hst (by omega) ha hs1
        subst heq1
        exact ihr (by omega) htokR ha hr
      | phrase hph _ =>
        obtain ⟨_, hsc, _⟩ := hph
        unfold slice at hsc; rw [List.drop_of_length_le ha] at hsc; simp at hsc
      | look _ hr | noLT _ hr | empty hr | onlyIf hr => exact ihr hsz htokR ha hr

private theorem startsWith_clamp_iff {P : CodePrims} {inp : List Nat} {s : Src} :
    ∀ (q : List LookItem) (j : Nat),
      StartsWith (codeAlphabet P) inp s q (min j inp.length) ↔
      StartsWith (codeAlphabet P) inp s q j
  | [], _ => Iff.rfl
  | .noLT :: rest, j => by
    simp only [StartsWith, codeAlphabet, true_and]
    exact startsWith_clamp_iff rest j
  | .t x :: rest, j => by
    unfold StartsWith
    dsimp only [codeAlphabet]
    by_cases hj : j ≤ inp.length
    · rw [Nat.min_eq_left hj]
    · rw [Nat.min_eq_right (by omega)]
      constructor
      · rintro ⟨h, hlt, hle, _⟩; omega
      · rintro ⟨h, hlt, hle, _⟩; omega

/-- Clamping positions to `inp.length` preserves `Step` over `codeAlphabet P` when `P.cond` reads only
`slice inp t.span.1 t.span.2`. -/
theorem code_step_clamp (hok : parseTablesOk = true) {P : CodePrims} {cs_inp : List Nat}
    (hcond : ∀ c t1 t2, slice cs_inp t1.span.1 t1.span.2 = slice cs_inp t2.span.1 t2.span.2 →
      (P.cond c cs_inp t1 ↔ P.cond c cs_inp t2))
    {neg0 : NT → List Param → Nat → Nat → Prop} {cx : Ctx} {g : GrammarId}
    (hg : g ∈ codeGrammars) :
    ∀ (sz : Nat),
      (∀ {n ps i j t}, treeSize t ≤ sz →
        Step (codeAlphabet P)
          (fun m ps' a b => ∃ t', Step (codeAlphabet P) neg0 cs_inp Ecma.Spec.gl cx g m ps' a b t')
          cs_inp Ecma.Spec.gl cx g n ps i j t →
        Step (codeAlphabet P)
          (fun m ps' a b => ∃ t', Step (codeAlphabet P) neg0 cs_inp Ecma.Spec.gl cx g m ps' a b t')
          cs_inp Ecma.Spec.gl cx g n ps (min i cs_inp.length) (min j cs_inp.length) (clampTree cs_inp.length t)) ∧
      (∀ {s ps k is i j m ts}, treeSize.treeListSize ts ≤ sz →
        (∀ it ∈ is, srcItemTermOk it = true) →
        (∀ it ∈ is, codeItemOk cx g it = true) →
        Ecma.Grammar.Seq (codeAlphabet P)
          (fun m ps' a b => ∃ t', Step (codeAlphabet P) neg0 cs_inp Ecma.Spec.gl cx g m ps' a b t')
          cs_inp Ecma.Spec.gl cx g s ps k is i j m ts →
        Ecma.Grammar.Seq (codeAlphabet P)
          (fun m ps' a b => ∃ t', Step (codeAlphabet P) neg0 cs_inp Ecma.Spec.gl cx g m ps' a b t')
          cs_inp Ecma.Spec.gl cx g s ps k is (min i cs_inp.length) (min j cs_inp.length) m (ts.map (clampTree cs_inp.length))) := by
  let L := cs_inp.length
  let neg1 := fun m ps' a b => ∃ t', Step (codeAlphabet P) neg0 cs_inp Ecma.Spec.gl cx g m ps' a b t'
  have hexclImp : ∀ {s k ps a b base ex},
      codeItemOk cx g (.butNot base ex) = true →
      (a = b ∨ a < L) →
      Excluded (codeAlphabet P) neg1 cs_inp s k ps (min a L) (min b L) ex →
      Excluded (codeAlphabet P) neg1 cs_inp s k ps a b ex := by
    intro s k ps a b base ex hcok hab hex
    have hsymImp : ∀ (y : Sym),
        (match y with | .t _ => true | .nt m _ => posBounded cx g 16 m) = true →
        (match y with
          | .t x => (codeAlphabet P).term s k x (slice cs_inp (min a L) (min b L))
          | .nt m args => neg1 m (applyArgs ps args) (min a L) (min b L)) →
        (match y with
          | .t x => (codeAlphabet P).term s k x (slice cs_inp a b)
          | .nt m args => neg1 m (applyArgs ps args) a b) := by
      intro y hpb hsy
      cases y with
      | t x => dsimp only at hsy ⊢; rwa [slice_clamp_eq] at hsy
      | nt m args =>
        dsimp only at hpb hsy ⊢
        obtain ⟨t', hst'⟩ := hsy
        rcases hab with rfl | halt
        · exact posBounded_shift_zero hok 16 a rfl hpb hst'
        · by_cases hbL : b ≤ L
          · rw [Nat.min_eq_left (Nat.le_of_lt halt), Nat.min_eq_left hbL] at hst'
            exact ⟨t', hst'⟩
          · rw [Nat.min_eq_left (Nat.le_of_lt halt), Nat.min_eq_right (by omega)] at hst'
            exact posBounded_stretch hok 16 rfl hpb halt (by omega) hst'
    dsimp only [codeItemOk] at hcok
    cases ex with
    | sym y => exact hsymImp y hcok hex
    | oneOf ys _ =>
      obtain ⟨y, hy, hsy⟩ := hex
      exact ⟨y, hy, hsymImp y (List.all_eq_true.mp hcok y hy) hsy⟩
  intro sz
  induction sz using Nat.strongRecOn with
  | ind sz ih =>
    have hstep : ∀ {n ps i j t}, treeSize t ≤ sz →
        Step (codeAlphabet P) neg1 cs_inp Ecma.Spec.gl cx g n ps i j t →
        Step (codeAlphabet P) neg1 cs_inp Ecma.Spec.gl cx g n ps (min i L) (min j L) (clampTree L t) := by
      intro n ps i j t hsz hs
      cases hs with
      | lex _ _ hl => cases hl
      | node s hsMem hgrd hpid hseq =>
        dsimp only [treeSize] at hsz
        rw [clampTree]
        exact .node s hsMem hgrd hpid ((ih _ (by omega)).2 (Nat.le_refl _)
          (fun it hit => srcItemTermOk_of_mem hok hsMem hit)
          (fun it hit => codeItemOk_of_mem hok hg hsMem hit) hseq)
    refine ⟨hstep, ?_⟩
    intro s ps k is
    induction is generalizing k with
    | nil => intro i j _ _ _ _ _ hseq; cases hseq; exact .nil
    | cons it rest ihr =>
      intro i j m ts hsz htok hcok hseq
      have htokR := fun x hx => htok x (List.mem_cons_of_mem _ hx)
      have hcokR := fun x hx => hcok x (List.mem_cons_of_mem _ hx)
      have hti := htok it List.mem_cons_self
      have hci := hcok it List.mem_cons_self
      cases hseq with
      | absent hr =>
        exact .absent (ihr hsz htokR hcokR hr)
      | @term _ _ _ x _ _ _ h _ _ _ ht hr =>
        dsimp only [treeSize.treeListSize, treeSize] at hsz
        have ht' : (codeAlphabet P).term s k x (slice cs_inp (min i L) (min h L)) := by
          rwa [slice_clamp_eq]
        rw [List.map_cons, clampTree]
        exact .term ht' (ihr (by omega) htokR hcokR hr)
      | @nt _ _ _ _ _ _ _ _ h _ _ t0 _ hst0 hcd0 hr =>
        dsimp only [treeSize.treeListSize] at hsz
        have hst0' := hstep (by omega) hst0
        have hcd0' : CondOk (codeAlphabet P) cs_inp rest (clampTree L t0) := by
          cases rest with
          | nil => trivial
          | cons hd _ =>
            cases hd with
            | onlyIf c =>
              dsimp only [CondOk, codeAlphabet] at hcd0 ⊢
              have hspT0 : t0.span = (i, h) := by cases hst0 with | lex _ _ hl => cases hl | node _ _ _ _ _ => rfl
              have hspC : (clampTree L t0).span = (min i L, min h L) := by
                cases hst0 with | lex _ _ hl => cases hl | node _ _ _ _ _ => simp [clampTree, Tree.span]
              refine (hcond c t0 (clampTree L t0) ?_).mp hcd0
              rw [hspT0, hspC, slice_clamp_eq]
            | _ => trivial
        exact .nt hst0' hcd0' (ihr (by omega) htokR hcokR hr)
      | @butNotT _ _ _ base ex _ _ h _ _ _ ht hne hr =>
        dsimp only [treeSize.treeListSize, treeSize] at hsz
        have ht' : (codeAlphabet P).term s k base (slice cs_inp (min i L) (min h L)) := by
          rwa [slice_clamp_eq]
        have hiL : i < L := by
          apply Classical.byContradiction; intro hge
          have hneSlice := codeTerm_nonempty hti ht
          unfold slice at hneSlice; rw [List.drop_of_length_le (by omega)] at hneSlice; simp at hneSlice
        rw [List.map_cons, clampTree]
        exact .butNotT ht' (fun hex => hne (hexclImp hci (Or.inr hiL) hex)) (ihr (by omega) htokR hcokR hr)
      | @butNotN _ _ _ _ _ ex _ _ h _ _ t0 _ hst0 hne hr =>
        dsimp only [treeSize.treeListSize] at hsz
        have hab : i = h ∨ i < L := by
          by_cases hiL : i < L
          · exact Or.inr hiL
          · exact Or.inl ((code_step_past_end_eq hok (treeSize t0)).1 (Nat.le_refl _) (by omega) hst0)
        exact .butNotN (hstep (by omega) hst0) (fun hex => hne (hexclImp hci hab hex)) (ihr (by omega) htokR hcokR hr)
      | @phrase _ _ _ ph _ _ h _ _ _ hph hr =>
        dsimp only [treeSize.treeListSize, treeSize] at hsz
        have hph' : (codeAlphabet P).phrase ph (slice cs_inp (min i L) (min h L)) := by
          rwa [slice_clamp_eq]
        rw [List.map_cons, clampTree]
        exact .phrase hph' (ihr (by omega) htokR hcokR hr)
      | @look _ _ _ lk _ _ _ _ _ hlk hr =>
        have hlk' : LookOk (codeAlphabet P) neg1 cs_inp s lk (min i L) := by
          cases lk with
            | eq q => exact (startsWith_clamp_iff q i).mpr hlk
            | ne q => exact fun hsw => hlk ((startsWith_clamp_iff q i).mp hsw)
            | mem qs =>
              obtain ⟨q, hq, hsw⟩ := hlk
              exact ⟨q, hq, (startsWith_clamp_iff q i).mpr hsw⟩
            | notMem qs =>
              exact fun q hq hsw => hlk q hq ((startsWith_clamp_iff q i).mp hsw)
            | notMemNT m =>
              by_cases hiL : i ≤ L
              · rwa [Nat.min_eq_left hiL]
              · rw [Nat.min_eq_right (by omega)]
                dsimp only [codeItemOk] at hci
                rw [Bool.and_eq_true, glData_eq] at hci
                rintro ⟨h', t', hst'⟩
                cases hst' with
                | lex _ _ hl => cases hl
                | node e heMem _ _ hseqE =>
                  have heOk := List.all_eq_true.mp hci.2 e heMem
                  rw [Bool.and_eq_true] at heOk
                  obtain ⟨_, hrhsOk⟩ := heOk
                  generalize hrhs : e.alt.rhs = rhs0 at hrhsOk hseqE
                  cases rhs0 with
                  | nil => cases hrhsOk
                  | cons itE tlE =>
                    cases tlE with
                    | cons _ _ => cases itE <;> simp at hrhsOk
                    | nil =>
                      cases itE with
                      | sym symE oE =>
                        cases symE with
                        | nt _ _ => cases oE <;> cases hrhsOk
                        | t xE =>
                          cases oE with
                          | true => cases hrhsOk
                          | false =>
                            cases hseqE with
                            | term htE _ =>
                              have hneE := codeTerm_nonempty hrhsOk htE
                              unfold slice at hneE
                              rw [List.drop_of_length_le (Nat.le_refl _)] at hneE
                              simp at hneE
                      | _ => simp at hrhsOk
        exact .look hlk' (ihr hsz htokR hcokR hr)
      | noLT _ hr => exact .noLT trivial (ihr hsz htokR hcokR hr)
      | empty hr => exact .empty (ihr hsz htokR hcokR hr)
      | onlyIf hr => exact .onlyIf (ihr hsz htokR hcokR hr)

theorem derives_clamp_node (hok : parseTablesOk = true) {P : CodePrims} {inp : List Nat}
    (hcond : ∀ c t1 t2, slice inp t1.span.1 t1.span.2 = slice inp t2.span.1 t2.span.2 →
      (P.cond c inp t1 ↔ P.cond c inp t2))
    {cx : Ctx} {g : GrammarId} (hg : g ∈ codeGrammars)
    {n : NT} {id : Nat} {ps : List Param} {i h : Nat} {kids : List Tree}
    (hi : i ≤ inp.length)
    (hd : Derives Ecma.Spec.gl cx g (codeAlphabet P) inp n ps i h (.node n id ps i h kids)) :
    Derives Ecma.Spec.gl cx g (codeAlphabet P) inp n ps i (min h inp.length)
      (.node n id ps i (min h inp.length) (kids.map (clampTree inp.length))) := by
  obtain ⟨K, hK⟩ := hd
  refine ⟨max K 2, fun k hk => ?_⟩
  obtain ⟨k0, rfl⟩ : ∃ k0, k = k0 + 2 := ⟨k - 2, by omega⟩
  have hsk := hK (k0 + 2) (Nat.le_trans (Nat.le_max_left K 2) hk)
  have hcl := (code_step_clamp hok hcond hg (treeSize (.node n id ps i h kids))).1 (Nat.le_refl _) hsk
  rw [clampTree] at hcl
  rwa [Nat.min_eq_left hi] at hcl

/-! ## Equivalence between `DTree` / `PlainDerives` and `Grammar.Derives` -/

/-- Projection from `AlphaSpec`'s `DTree` to `Ecma.Grammar.Tree` for code-point grammars. -/
def DTree.toTree : DTree → Tree
  | .leaf i j => .leaf i j
  | .lex _ i _ => .lex i (.leaf 0 0)
  | .node n id _ ps i j _ kids => .node n id ps i j (kids.map DTree.toTree)

theorem DTree.toTree_isLeaf : ∀ dt : DTree, dt.toTree.isLeaf = dt.isLeaf
  | .leaf _ _ => by simp [DTree.toTree, Tree.isLeaf, DTree.isLeaf]
  | .lex _ _ _ => by simp [DTree.toTree, Tree.isLeaf, DTree.isLeaf]
  | .node _ _ _ _ _ _ _ _ => by simp [DTree.toTree, Tree.isLeaf, DTree.isLeaf]

theorem DTree.toTree_span_of_not_lex : ∀ dt : DTree,
    (∀ m a b, dt ≠ .lex m a b) → dt.toTree.span = dt.span
  | .leaf _ _, _ => by simp [DTree.toTree, Tree.span, DTree.span]
  | .lex m a b, h => absurd rfl (h m a b)
  | .node _ _ _ _ _ _ _ _, _ => by simp [DTree.toTree, Tree.span, DTree.span]

private theorem lookHolds_code_iff {N T : Type} {B : Builder N} {P : CodePrims}
    (hm : CodePrimsMatch B P) {cs : Array Nat} {g : GrammarId} {cx : Ctx}
    {off : Nat} {src : Array Nat} {grp : Option (Nat → Bool)}
    {neg0 : NT → List Param → Nat → Nat → Prop}
    (hok : parseTablesOk = true) {s : Src} {l : Lookahead} {i : Nat}
    (hci : codeItemOk cx g (.lookahead l) = true) :
    (codeAlphaSpec (T := T) B cs g cx off src grp).LookHolds l i ↔
      LookOk (codeAlphabet P)
        (fun m ps' a b => ∃ t', Step (codeAlphabet P) neg0 cs.toList Ecma.Spec.gl cx g m ps' a b t')
        cs.toList s l i := by
  dsimp only [codeItemOk] at hci
  cases l with
  | eq q =>
    simp only [lookSeqsOk, List.all_cons, List.all_nil, Bool.and_true] at hci
    exact startsWith_iff hm cs s q i hci
  | ne q =>
    simp only [lookSeqsOk, List.all_cons, List.all_nil, Bool.and_true] at hci
    exact not_congr (startsWith_iff hm cs s q i hci)
  | mem qs =>
    dsimp only [AlphaSpec.LookHolds, codeAlphaSpec, LookOk]
    exact ⟨fun ⟨q, hq, hsw⟩ => ⟨q, hq, (startsWith_iff hm cs s q i (List.all_eq_true.mp hci q hq)).mp hsw⟩,
           fun ⟨q, hq, hsw⟩ => ⟨q, hq, (startsWith_iff hm cs s q i (List.all_eq_true.mp hci q hq)).mpr hsw⟩⟩
  | notMem qs =>
    dsimp only [AlphaSpec.LookHolds, codeAlphaSpec, LookOk]
    exact ⟨fun hall q hq hsw => hall q hq ((startsWith_iff hm cs s q i (List.all_eq_true.mp hci q hq)).mpr hsw),
           fun hall q hq hsw => hall q hq ((startsWith_iff hm cs s q i (List.all_eq_true.mp hci q hq)).mp hsw)⟩
  | notMemNT m =>
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at hci
    dsimp only [AlphaSpec.LookHolds, codeAlphaSpec, LookOk]
    exact not_congr (decAny_iff_step hok hm cs hci)

def exclTermOk : Item → Bool
  | .butNot _ (.sym (.t x)) => codeLookTermOk x
  | .butNot _ (.oneOf ys _) => ys.all fun | .t x => codeLookTermOk x | .nt _ _ => true
  | _ => true

private theorem grammars_blocks_exclTermOk :
    ((glData.grammars.all fun (g, rs) => rs.all fun r => (srcsOf g r).all fun s => s.alt.rhs.all exclTermOk) &&
     (glData.blocks.all fun b => b.rules.all fun r => (srcsOf .annexB r).all fun s => s.alt.rhs.all exclTermOk)) = true := by
  decide

private theorem exclTermOk_of_mem {cx : Ctx} {g : GrammarId} {n : NT} {s : Src}
    (hs : s ∈ Ecma.Spec.gl.alts cx g n) {it : Item} (hit : it ∈ s.alt.rhs) :
    exclTermOk it = true := by
  rw [← glData_eq] at hs
  have hmem := mem_allSrcs_of_alts hs
  unfold allSrcs at hmem
  have ⟨hgAll, hbAll⟩ := Bool.and_eq_true_iff.mp grammars_blocks_exclTermOk
  rcases List.mem_append.mp hmem with h1 | h2
  · rw [List.mem_flatMap] at h1
    obtain ⟨⟨g', rs⟩, hp, hrFlat⟩ := h1
    rw [List.mem_flatMap] at hrFlat
    obtain ⟨r, hrMem, hsMem⟩ := hrFlat
    have hsOk := List.all_eq_true.mp (List.all_eq_true.mp (List.all_eq_true.mp hgAll (g', rs) hp) r hrMem) s hsMem
    exact List.all_eq_true.mp hsOk it hit
  · rw [List.mem_flatMap] at h2
    obtain ⟨b, hbMem, hrFlat⟩ := h2
    split at hrFlat
    · simp only [↓reduceIte, List.mem_flatMap] at hrFlat
      obtain ⟨r, hrMem, hsMem⟩ := hrFlat
      have hsOk := List.all_eq_true.mp (List.all_eq_true.mp (List.all_eq_true.mp hbAll b hbMem) r hrMem) s hsMem
      exact List.all_eq_true.mp hsOk it hit
    · simp at hrFlat

private theorem exclHolds_code_iff {N T : Type} {B : Builder N} {P : CodePrims}
    (hm : CodePrimsMatch B P) {cs : Array Nat} {g : GrammarId} {cx : Ctx}
    {off : Nat} {src : Array Nat} {grp : Option (Nat → Bool)}
    {neg0 : NT → List Param → Nat → Nat → Prop}
    (hok : parseTablesOk = true) {s : Src} {k : Nat} {ps : List Param} {i h : Nat}
    {base : Sym} {ex : Exclusion}
    (hh : h ≤ cs.size)
    (hti : exclTermOk (.butNot base ex) = true)
    (hci : codeItemOk cx g (.butNot base ex) = true) :
    (codeAlphaSpec (T := T) B cs g cx off src grp).ExclHolds s k ps i h ex ↔
      Excluded (codeAlphabet P)
        (fun m ps' a b => ∃ t', Step (codeAlphabet P) neg0 cs.toList Ecma.Spec.gl cx g m ps' a b t')
        cs.toList s k ps i h ex := by
  have symIff : ∀ (y : Sym),
      (match y with | .t x => codeLookTermOk x | .nt _ _ => true) = true →
      (match y with | .t _ => true | .nt m _ => posBounded cx g 16 m) = true →
      ((codeAlphaSpec (T := T) B cs g cx off src grp).SymHolds s k ps i h y ↔
        match y with
        | .t x => (codeAlphabet P).term s k x (slice cs.toList i h)
        | .nt m args => ∃ t', Step (codeAlphabet P) neg0 cs.toList Ecma.Spec.gl cx g m (applyArgs ps args) i h t') := by
    intro y hty hpb
    cases y with
    | t x =>
      dsimp only [AlphaSpec.SymHolds, codeAlphaSpec]
      exact ⟨fun ht => (codeTerm_sound hm cs s k x i h ht).2.2,
             fun ht => codeTerm_complete hm cs hty hh ht⟩
    | nt m args =>
      dsimp only [AlphaSpec.SymHolds, codeAlphaSpec, Code.alpha] at hpb ⊢
      by_cases hem : (altsOf cx g m).isEmpty = true
      · simp only [hem, Bool.not_true, Bool.false_eq_true, ↓reduceIte, false_iff]
        rintro ⟨t', hst'⟩
        cases hst' with
        | lex _ _ hl => cases hl
        | node e heMem _ _ _ =>
          rw [altsOf_eq hok, List.isEmpty_iff] at hem
          rw [hem] at heMem; cases heMem
      · have hemF : (altsOf cx g m).isEmpty = false := Bool.eq_false_iff.mpr hem
        simp only [hemF, Bool.not_false, ↓reduceIte]
        exact dec_iff_step hok hm cs 16 hpb hh
  dsimp only [exclTermOk, codeItemOk] at hti hci
  cases ex with
  | sym y =>
    cases y with
    | t x => exact symIff (.t x) hti hci
    | nt m args => exact symIff (.nt m args) rfl hci
  | oneOf ys _ =>
    dsimp only [AlphaSpec.ExclHolds, Excluded]
    exact ⟨fun ⟨y, hy, hs⟩ => ⟨y, hy, (symIff y (List.all_eq_true.mp hti y hy) (List.all_eq_true.mp hci y hy)).mp hs⟩,
           fun ⟨y, hy, hs⟩ => ⟨y, hy, (symIff y (List.all_eq_true.mp hti y hy) (List.all_eq_true.mp hci y hy)).mpr hs⟩⟩

mutual
theorem derivesWith_to_step {N T : Type} {B : Builder N} {P : CodePrims}
    {cs : Array Nat} {g : GrammarId} {cx : Ctx} {off : Nat} {src : Array Nat} {grp : Option (Nat → Bool)}
    (hok : parseTablesOk = true) (hg : g ∈ codeGrammars)
    (hm : CodePrimsMatch B P) (hc : CondMatch grp cs P)
    {neg0 : NT → List Param → Nat → Nat → Prop}
    {allow : NT → List Param → Nat → Src → Prop}
    {n : NT} {ps : List Param} {i j : Nat} {dt : DTree}
    (hi : i ≤ cs.size)
    (hd : (codeAlphaSpec (T := T) B cs g cx off src grp).DerivesWith allow n ps i j dt) :
    i ≤ j ∧ j ≤ cs.size ∧ dt.span = (i, j) ∧ (∀ m a b, dt ≠ .lex m a b) ∧
      Step (codeAlphabet P)
        (fun m ps' a b => ∃ t', Step (codeAlphabet P) neg0 cs.toList Ecma.Spec.gl cx g m ps' a b t')
        cs.toList Ecma.Spec.gl cx g n ps i j dt.toTree :=
  match hd with
  | .node s hsMem _ hgrd hpid hsw => by
    have hsSpec : s ∈ Ecma.Spec.gl.alts cx g n := (altsOf_eq hok cx g n) ▸ hsMem
    obtain ⟨_, hoptsEq⟩ := alt_lhs_and_opts hok hsSpec
    have hmMask := hoptsEq ▸ (codeAlphaSpec (T := T) B cs g cx off src grp).seqWith_masks hsw
    obtain ⟨hpeq, _, _, _, _⟩ := prodIdOf_spec hok hsSpec hmMask
    have hpidSpec : Ecma.Spec.gl.prodId s _ = some _ := hpeq.symm.trans hpid
    have ⟨hij, hjSz, hseq⟩ := seqWith_to_seq (T := T) (B := B) (off := off) (src := src) (grp := grp) (neg0 := neg0) hok hg hm hc
      (fun it hit => exclTermOk_of_mem hsSpec hit)
      (fun it hit => codeItemOk_of_mem hok hg hsSpec hit) hi hsw
    rw [DTree.toTree]
    exact ⟨hij, hjSz, rfl, (fun _ _ _ h => by cases h), Step.node s hsSpec hgrd hpidSpec hseq⟩

theorem seqWith_to_seq {N T : Type} {B : Builder N} {P : CodePrims}
    {cs : Array Nat} {g : GrammarId} {cx : Ctx} {off : Nat} {src : Array Nat} {grp : Option (Nat → Bool)}
    (hok : parseTablesOk = true) (hg : g ∈ codeGrammars)
    (hm : CodePrimsMatch B P) (hc : CondMatch grp cs P)
    {neg0 : NT → List Param → Nat → Nat → Prop}
    {allow : NT → List Param → Nat → Src → Prop}
    {s : Src} {ps : List Param} {k : Nat} {is : List Item} {i j : Nat} {m : List Bool} {ts : List DTree}
    (htok : ∀ it ∈ is, exclTermOk it = true)
    (hcok : ∀ it ∈ is, codeItemOk cx g it = true)
    (hi : i ≤ cs.size)
    (hsw : (codeAlphaSpec (T := T) B cs g cx off src grp).SeqWith allow s ps k is i j m ts) :
    i ≤ j ∧ j ≤ cs.size ∧
      Ecma.Grammar.Seq (codeAlphabet P)
        (fun m ps' a b => ∃ t', Step (codeAlphabet P) neg0 cs.toList Ecma.Spec.gl cx g m ps' a b t')
        cs.toList Ecma.Spec.gl cx g s ps k is i j m (ts.map DTree.toTree) :=
  match hsw with
  | .nil => ⟨Nat.le_refl _, hi, .nil⟩
  | .absent hr =>
    let ⟨hij, hjSz, hseqR⟩ := seqWith_to_seq (neg0 := neg0) hok hg hm hc
      (fun x hx => htok x (List.mem_cons_of_mem _ hx))
      (fun x hx => hcok x (List.mem_cons_of_mem _ hx)) hi hr
    ⟨hij, hjSz, .absent hseqR⟩
  | .term ht hr => by
    obtain ⟨hlt, hhSz, hterm⟩ := codeTerm_sound hm cs s k _ _ _ ht
    have ⟨hhj, hjSz, hseqR⟩ := seqWith_to_seq (neg0 := neg0) hok hg hm hc
      (fun x hx => htok x (List.mem_cons_of_mem _ hx))
      (fun x hx => hcok x (List.mem_cons_of_mem _ hx)) hhSz hr
    rw [List.map_cons, DTree.toTree]
    exact ⟨by omega, hjSz, .term hterm hseqR⟩
  | .nt (is := isR) (h := h) (t := t0) _ hd0 _ hcd0 hr => by
    have ⟨hih, hhSz, hsp0, hnlex0, hst0⟩ := derivesWith_to_step (neg0 := neg0) hok hg hm hc hi hd0
    have ⟨hhj, hjSz, hseqR⟩ := seqWith_to_seq (neg0 := neg0) hok hg hm hc
      (fun x hx => htok x (List.mem_cons_of_mem _ hx))
      (fun x hx => hcok x (List.mem_cons_of_mem _ hx)) hhSz hr
    have hcdOk : CondOk (codeAlphabet P) cs.toList isR t0.toTree := by
      cases isR with
      | nil => trivial
      | cons hdI _ =>
        cases hdI with
        | onlyIf ph =>
          dsimp only [AlphaSpec.CondHolds, condAfter, codeAlphaSpec] at hcd0
          exact (hc ph i h t0.toTree hhSz ((DTree.toTree_span_of_not_lex t0 hnlex0).trans hsp0)).mp hcd0
        | _ => trivial
    rw [List.map_cons]
    exact ⟨by omega, hjSz, .nt hst0 hcdOk hseqR⟩
  | .leaf _ hl _ _ _ => nomatch hl
  | .butNotT ht hne hr => by
    obtain ⟨hlt, hhSz, hterm⟩ := codeTerm_sound hm cs s k _ _ _ ht
    have hneSpec := mt (exclHolds_code_iff (T := T) (B := B) (off := off) (src := src) (grp := grp) (neg0 := neg0) hm hok hhSz
      (htok _ List.mem_cons_self) (hcok _ List.mem_cons_self)).mpr hne
    have ⟨hhj, hjSz, hseqR⟩ := seqWith_to_seq (neg0 := neg0) hok hg hm hc
      (fun x hx => htok x (List.mem_cons_of_mem _ hx))
      (fun x hx => hcok x (List.mem_cons_of_mem _ hx)) hhSz hr
    rw [List.map_cons, DTree.toTree]
    exact ⟨by omega, hjSz, .butNotT hterm hneSpec hseqR⟩
  | .butNotN _ hd0 _ hne hr => by
    have ⟨hih, hhSz, _, _, hst0⟩ := derivesWith_to_step (neg0 := neg0) hok hg hm hc hi hd0
    have hneSpec := mt (exclHolds_code_iff (T := T) (B := B) (off := off) (src := src) (grp := grp) (neg0 := neg0) hm hok hhSz
      (htok _ List.mem_cons_self) (hcok _ List.mem_cons_self)).mpr hne
    have ⟨hhj, hjSz, hseqR⟩ := seqWith_to_seq (neg0 := neg0) hok hg hm hc
      (fun x hx => htok x (List.mem_cons_of_mem _ hx))
      (fun x hx => hcok x (List.mem_cons_of_mem _ hx)) hhSz hr
    rw [List.map_cons]
    exact ⟨by omega, hjSz, .butNotN hst0 hneSpec hseqR⟩
  | .butNotLeaf _ hl _ _ _ => nomatch hl
  | .phrase (p := ph) ⟨c, hcGet, hpok, rfl⟩ hr => by
    have hltSz : i < cs.size := (Array.getElem?_eq_some_iff.mp hcGet).1
    have hhSz : i + 1 ≤ cs.size := by omega
    have hgetL : cs.toList[i]? = some c := by simpa using hcGet
    have hdrop : cs.toList.drop i = c :: cs.toList.drop (i + 1) := by
      obtain ⟨hiL, hvL⟩ := List.getElem?_eq_some_iff.mp hgetL
      rw [List.drop_eq_getElem_cons hiL, hvL]
    have hsc : slice cs.toList i (i + 1) = [c] :=
      (slice_singleton_iff (by omega) (by simpa using hhSz)).mpr ⟨rfl, hgetL, hdrop⟩
    have ⟨hhj, hjSz, hseqR⟩ := seqWith_to_seq (neg0 := neg0) hok hg hm hc
      (fun x hx => htok x (List.mem_cons_of_mem _ hx))
      (fun x hx => hcok x (List.mem_cons_of_mem _ hx)) hhSz hr
    rw [List.map_cons, DTree.toTree]
    have hphSpec : (codeAlphabet P).phrase ph (slice cs.toList i (i + 1)) := ⟨c, hsc, (hm.2 ph c).mp hpok⟩
    exact ⟨by omega, hjSz, .phrase hphSpec hseqR⟩
  | .look (l := lk) hlk hr => by
    have hlkSpec := (lookHolds_code_iff (T := T) (B := B) (off := off) (src := src) (grp := grp) (neg0 := neg0) (s := s) hm hok (hcok (.lookahead lk) List.mem_cons_self)).mp hlk
    have ⟨hij, hjSz, hseqR⟩ := seqWith_to_seq (T := T) (B := B) (off := off) (src := src) (grp := grp) (neg0 := neg0) hok hg hm hc
      (fun x hx => htok x (List.mem_cons_of_mem _ hx))
      (fun x hx => hcok x (List.mem_cons_of_mem _ hx)) hi hr
    exact ⟨hij, hjSz, .look hlkSpec hseqR⟩
  | .noLT _ hr =>
    let ⟨hij, hjSz, hseqR⟩ := seqWith_to_seq (neg0 := neg0) hok hg hm hc
      (fun x hx => htok x (List.mem_cons_of_mem _ hx))
      (fun x hx => hcok x (List.mem_cons_of_mem _ hx)) hi hr
    ⟨hij, hjSz, .noLT trivial hseqR⟩
  | .empty hr =>
    let ⟨hij, hjSz, hseqR⟩ := seqWith_to_seq (neg0 := neg0) hok hg hm hc
      (fun x hx => htok x (List.mem_cons_of_mem _ hx))
      (fun x hx => hcok x (List.mem_cons_of_mem _ hx)) hi hr
    ⟨hij, hjSz, .empty hseqR⟩
  | .onlyIf hr =>
    let ⟨hij, hjSz, hseqR⟩ := seqWith_to_seq (neg0 := neg0) hok hg hm hc
      (fun x hx => htok x (List.mem_cons_of_mem _ hx))
      (fun x hx => hcok x (List.mem_cons_of_mem _ hx)) hi hr
    ⟨hij, hjSz, .onlyIf hseqR⟩
end

theorem derivesWith_to_derives {N T : Type} {B : Builder N} {P : CodePrims}
    (hok : parseTablesOk = true) {g : GrammarId} (hg : g ∈ codeGrammars)
    (hm : CodePrimsMatch B P) {grp : Option (Nat → Bool)} {cs : Array Nat}
    (hc : CondMatch grp cs P)
    {cx : Ctx} {off : Nat} {src : Array Nat}
    {allow : NT → List Param → Nat → Src → Prop}
    {n : NT} {ps : List Param} {i j : Nat} {dt : DTree}
    (hi : i ≤ cs.size)
    (hd : (codeAlphaSpec (T := T) B cs g cx off src grp).DerivesWith allow n ps i j dt) :
    i ≤ j ∧ j ≤ cs.size ∧ Derives Ecma.Spec.gl cx g (codeAlphabet P) cs.toList n ps i j dt.toTree := by
  have ⟨hij, hjSz, _, _, _⟩ := derivesWith_to_step (neg0 := fun _ _ _ _ => False) hok hg hm hc hi hd
  refine ⟨hij, hjSz, 2, fun k hk => ?_⟩
  obtain ⟨k0, rfl⟩ : ∃ k0, k = k0 + 2 := ⟨k - 2, by omega⟩
  dsimp only [DerivesAt]
  exact (derivesWith_to_step (neg0 := fun m ps' a b => ∃ t', DerivesAt Ecma.Spec.gl cx g (codeAlphabet P) cs.toList k0 m ps' a b t')
    hok hg hm hc hi hd).2.2.2.2

theorem step_to_plainDerives {N T : Type} {B : Builder N} {P : CodePrims}
    (hok : parseTablesOk = true) {g : GrammarId} (hg : g ∈ codeGrammars)
    (hm : CodePrimsMatch B P) {grp : Option (Nat → Bool)} {cs : Array Nat}
    (hc : CondMatch grp cs P)
    {cx : Ctx} {off : Nat} {src : Array Nat}
    {neg0 : NT → List Param → Nat → Nat → Prop} :
    ∀ (sz : Nat),
      (∀ {n ps i j gt}, treeSize gt ≤ sz → j ≤ cs.size →
        Step (codeAlphabet P)
          (fun m ps' a b => ∃ t', Step (codeAlphabet P) neg0 cs.toList Ecma.Spec.gl cx g m ps' a b t')
          cs.toList Ecma.Spec.gl cx g n ps i j gt →
        ∃ dt, dt.toTree = gt ∧ (codeAlphaSpec (T := T) B cs g cx off src grp).PlainDerives n ps i j dt) ∧
      (∀ {s ps k is i j m ts}, treeSize.treeListSize ts ≤ sz → j ≤ cs.size →
        (∀ it ∈ is, srcItemTermOk it = true) →
        (∀ it ∈ is, exclTermOk it = true) →
        (∀ it ∈ is, codeItemOk cx g it = true) →
        Ecma.Grammar.Seq (codeAlphabet P)
          (fun m ps' a b => ∃ t', Step (codeAlphabet P) neg0 cs.toList Ecma.Spec.gl cx g m ps' a b t')
          cs.toList Ecma.Spec.gl cx g s ps k is i j m ts →
        ∃ dts, dts.map DTree.toTree = ts ∧
          (codeAlphaSpec (T := T) B cs g cx off src grp).SeqWith (fun _ _ _ _ => True) s ps k is i j m dts) := by
  let S := codeAlphaSpec (T := T) B cs g cx off src grp
  intro sz
  induction sz using Nat.strongRecOn with
  | ind sz ih =>
    have hstep : ∀ {n ps i j gt}, treeSize gt ≤ sz → j ≤ cs.size →
        Step (codeAlphabet P)
          (fun m ps' a b => ∃ t', Step (codeAlphabet P) neg0 cs.toList Ecma.Spec.gl cx g m ps' a b t')
          cs.toList Ecma.Spec.gl cx g n ps i j gt →
        ∃ dt, dt.toTree = gt ∧ S.PlainDerives n ps i j dt := by
      intro n ps i j gt hsz hj hs
      cases hs with
      | lex _ _ hl => cases hl
      | @node _ _ _ _ m0 kids0 id0 s hsMem hgrd hpid hseq =>
        dsimp only [treeSize] at hsz
        obtain ⟨dts, hmap, hsw⟩ := (ih _ (by omega)).2 (Nat.le_refl _) hj
          (fun it hit => srcItemTermOk_of_mem hok hsMem hit)
          (fun it hit => exclTermOk_of_mem hsMem hit)
          (fun it hit => codeItemOk_of_mem hok hg hsMem hit) hseq
        obtain ⟨_, hoptsEq⟩ := alt_lhs_and_opts hok hsMem
        obtain ⟨hpeq, _, _, _, _⟩ := prodIdOf_spec hok hsMem (hoptsEq ▸ S.seqWith_masks hsw)
        have hsAlts : s ∈ altsOf cx g n := (altsOf_eq hok cx g n).symm ▸ hsMem
        exact ⟨.node n id0 s ps i j m0 dts, by simp [DTree.toTree, hmap],
          .node s hsAlts trivial hgrd (hpeq.trans hpid) hsw⟩
    refine ⟨hstep, ?_⟩
    intro s ps k is
    induction is generalizing k with
    | nil =>
      intro i j m ts _ _ _ _ _ hseq
      cases hseq
      exact ⟨[], rfl, .nil⟩
    | cons it rest ihr =>
      intro i j m ts hsz hj htok hexok hcok hseq
      have htokR := fun x hx => htok x (List.mem_cons_of_mem _ hx)
      have hexokR := fun x hx => hexok x (List.mem_cons_of_mem _ hx)
      have hcokR := fun x hx => hcok x (List.mem_cons_of_mem _ hx)
      have hti := htok it List.mem_cons_self
      have hexi := hexok it List.mem_cons_self
      have hci := hcok it List.mem_cons_self
      cases hseq with
      | absent hr =>
        obtain ⟨dts, hmap, hsw⟩ := ihr hsz hj htokR hexokR hcokR hr
        exact ⟨dts, hmap, .absent hsw⟩
      | @term _ _ _ _ _ _ _ h _ _ _ ht hr =>
        dsimp only [treeSize.treeListSize, treeSize] at hsz
        have hhj := code_seq_le hok htokR hr
        have htEnd := codeTerm_complete hm cs hti (Nat.le_trans hhj hj) ht
        obtain ⟨dts, hmap, hsw⟩ := ihr (by omega) hj htokR hexokR hcokR hr
        exact ⟨.leaf i h :: dts, by simp [DTree.toTree, hmap], .term htEnd hsw⟩
      | @nt _ _ _ mNt _ _ _ _ h _ _ t0 _ hst0 hcd0 hr =>
        dsimp only [treeSize.treeListSize] at hsz
        have hhj := code_seq_le hok htokR hr
        have hhSz := Nat.le_trans hhj hj
        have hneAlts : (altsOf cx g mNt).isEmpty = false := by
          cases hst0 with
          | lex _ _ hl => cases hl
          | node e heMem _ _ _ =>
            rw [altsOf_eq hok]
            cases hL : Ecma.Spec.gl.alts cx g mNt with
            | nil => rw [hL] at heMem; cases heMem
            | cons _ _ => rfl
        obtain ⟨dt0, hdt0Eq, hd0⟩ := hstep (by omega) hhSz hst0
        obtain ⟨dts, hmap, hsw⟩ := ihr (by omega) hj htokR hexokR hcokR hr
        have hcdHolds : S.CondHolds rest i h := by
          cases rest with
          | nil => trivial
          | cons hdI _ =>
            cases hdI with
            | onlyIf ph =>
              dsimp only [CondOk, codeAlphabet] at hcd0
              dsimp only [AlphaSpec.CondHolds, condAfter, S, codeAlphaSpec]
              have hsp0 : t0.span = (i, h) := by cases hst0 with | lex _ _ hl => cases hl | node _ _ _ _ _ => rfl
              exact (hc ph i h t0 hhSz hsp0).mpr hcd0
            | _ => trivial
        exact ⟨dt0 :: dts, by simp [hdt0Eq, hmap], .nt hneAlts hd0 rfl hcdHolds hsw⟩
      | @butNotT _ _ _ _ _ _ _ h _ _ _ ht hne hr =>
        dsimp only [treeSize.treeListSize, treeSize] at hsz
        have hhj := code_seq_le hok htokR hr
        have hhSz := Nat.le_trans hhj hj
        have htEnd := codeTerm_complete hm cs hti hhSz ht
        have hneS := mt (exclHolds_code_iff (T := T) (B := B) (off := off) (src := src) (grp := grp) (neg0 := neg0) hm hok hhSz hexi hci).mp hne
        obtain ⟨dts, hmap, hsw⟩ := ihr (by omega) hj htokR hexokR hcokR hr
        exact ⟨.leaf i h :: dts, by simp [DTree.toTree, hmap], .butNotT htEnd hneS hsw⟩
      | @butNotN _ _ _ mNt _ _ _ _ h _ _ t0 _ hst0 hne hr =>
        dsimp only [treeSize.treeListSize] at hsz
        have hhj := code_seq_le hok htokR hr
        have hhSz := Nat.le_trans hhj hj
        have hneAlts : (altsOf cx g mNt).isEmpty = false := by
          cases hst0 with
          | lex _ _ hl => cases hl
          | node e heMem _ _ _ =>
            rw [altsOf_eq hok]
            cases hL : Ecma.Spec.gl.alts cx g mNt with
            | nil => rw [hL] at heMem; cases heMem
            | cons _ _ => rfl
        obtain ⟨dt0, hdt0Eq, hd0⟩ := hstep (by omega) hhSz hst0
        have hneS := mt (exclHolds_code_iff (T := T) (B := B) (off := off) (src := src) (grp := grp) (neg0 := neg0) hm hok hhSz hexi hci).mp hne
        obtain ⟨dts, hmap, hsw⟩ := ihr (by omega) hj htokR hexokR hcokR hr
        exact ⟨dt0 :: dts, by simp [hdt0Eq, hmap], .butNotN hneAlts hd0 rfl hneS hsw⟩
      | @phrase _ _ _ ph _ _ h _ _ _ hph hr =>
        dsimp only [treeSize.treeListSize, treeSize] at hsz
        obtain ⟨c, hsc, hpc⟩ := hph
        have hhj := code_seq_le hok htokR hr
        have hhSz := Nat.le_trans hhj hj
        have hlt : i < h := (slice_nonempty_lt (by rw [hsc]; exact List.cons_ne_nil _ _)).1
        obtain ⟨rfl, hgetL, _⟩ := (slice_singleton_iff (Nat.le_of_lt hlt) (by simpa using hhSz)).mp hsc
        have hcGet : cs[i]? = some c := by simpa using hgetL
        obtain ⟨dts, hmap, hsw⟩ := ihr (by omega) hj htokR hexokR hcokR hr
        exact ⟨.leaf i (i + 1) :: dts, by simp [DTree.toTree, hmap],
          .phrase ⟨c, hcGet, (hm.2 ph c).mpr hpc, rfl⟩ hsw⟩
      | look hlk hr =>
        have hlkS := (lookHolds_code_iff (T := T) (B := B) (off := off) (src := src) (grp := grp) (neg0 := neg0) hm hok hci).mpr hlk
        obtain ⟨dts, hmap, hsw⟩ := ihr hsz hj htokR hexokR hcokR hr
        exact ⟨dts, hmap, .look hlkS hsw⟩
      | noLT _ hr =>
        obtain ⟨dts, hmap, hsw⟩ := ihr hsz hj htokR hexokR hcokR hr
        exact ⟨dts, hmap, .noLT trivial hsw⟩
      | empty hr =>
        obtain ⟨dts, hmap, hsw⟩ := ihr hsz hj htokR hexokR hcokR hr
        exact ⟨dts, hmap, .empty hsw⟩
      | onlyIf hr =>
        obtain ⟨dts, hmap, hsw⟩ := ihr hsz hj htokR hexokR hcokR hr
        exact ⟨dts, hmap, .onlyIf hsw⟩

theorem derives_to_plainDerives {N T : Type} {B : Builder N} {P : CodePrims}
    (hok : parseTablesOk = true) {g : GrammarId} (hg : g ∈ codeGrammars)
    (hm : CodePrimsMatch B P) {grp : Option (Nat → Bool)} {cs : Array Nat}
    (hc : CondMatch grp cs P)
    {cx : Ctx} {off : Nat} {src : Array Nat}
    {n : NT} {ps : List Param} {i j : Nat} {gt : Tree}
    (hj : j ≤ cs.size)
    (hd : Derives Ecma.Spec.gl cx g (codeAlphabet P) cs.toList n ps i j gt) :
    ∃ dt, dt.toTree = gt ∧ (codeAlphaSpec (T := T) B cs g cx off src grp).PlainDerives n ps i j dt := by
  obtain ⟨K, hK⟩ := hd
  have hsk := hK (max K 2) (Nat.le_max_left K 2)
  obtain ⟨k0, hk0⟩ : ∃ k0, max K 2 = k0 + 2 := ⟨max K 2 - 2, by omega⟩
  rw [hk0] at hsk
  exact (step_to_plainDerives hok hg hm hc (treeSize gt)).1 (Nat.le_refl _) hj hsk

mutual
theorem derivesWith_toTree_inj {N T : Type} {B : Builder N}
    (hok : parseTablesOk = true)
    {cs : Array Nat} {g : GrammarId} {cx : Ctx} {off : Nat} {src : Array Nat} {grp : Option (Nat → Bool)}
    {a1 a2 : NT → List Param → Nat → Src → Prop}
    {n1 n2 : NT} {ps1 ps2 : List Param} {i1 j1 i2 j2 : Nat} {dt1 dt2 : DTree}
    (hd1 : (codeAlphaSpec (T := T) B cs g cx off src grp).DerivesWith a1 n1 ps1 i1 j1 dt1)
    (hd2 : (codeAlphaSpec (T := T) B cs g cx off src grp).DerivesWith a2 n2 ps2 i2 j2 dt2)
    (heq : dt1.toTree = dt2.toTree) :
    dt1 = dt2 :=
  match hd1, hd2 with
  | .node s1 hs1 _ _ hpid1 hsw1, .node s2 hs2 _ _ hpid2 hsw2 => by
    simp only [DTree.toTree] at heq
    injection heq with hn hid hps hi hj hkids
    subst hn; subst hid; subst hps; subst hi; subst hj
    have hs1Spec : s1 ∈ Ecma.Spec.gl.alts cx g n1 := (altsOf_eq hok cx g n1) ▸ hs1
    have hs2Spec : s2 ∈ Ecma.Spec.gl.alts cx g n1 := (altsOf_eq hok cx g n1) ▸ hs2
    obtain ⟨_, hopts1⟩ := alt_lhs_and_opts hok hs1Spec
    obtain ⟨_, hopts2⟩ := alt_lhs_and_opts hok hs2Spec
    have hm1 := (codeAlphaSpec (T := T) B cs g cx off src grp).seqWith_masks hsw1
    have hm2 := (codeAlphaSpec (T := T) B cs g cx off src grp).seqWith_masks hsw2
    obtain ⟨hpeq1, id1, P1, hid1, hpo1, _, _, _, hmask1, hfind1⟩ := prodIdOf_spec hok hs1Spec (hopts1 ▸ hm1)
    obtain ⟨hpeq2, id2, P2, hid2, hpo2, _, _, _, hmask2, hfind2⟩ := prodIdOf_spec hok hs2Spec (hopts2 ▸ hm2)
    have hidEq1 : id1 = _ := Option.some.inj ((hpeq1.trans hid1).symm.trans hpid1)
    have hidEq2 : id2 = _ := Option.some.inj ((hpeq2.trans hid2).symm.trans hpid2)
    subst hidEq1
    have hid12 : id2 = id1 := hidEq2
    subst hid12
    have hP12 : P1 = P2 := Option.some.inj (hpo1.symm.trans hpo2)
    subst hP12
    have hs12 : s1 = s2 := Option.some.inj (hfind1.symm.trans hfind2)
    have hm12 : _ = _ := hmask1.symm.trans hmask2
    subst hs12; subst hm12
    have hkidsEq := seqWith_toTree_inj hok hsw1 hsw2 rfl hkids
    rw [hkidsEq]

theorem seqWith_toTree_inj {N T : Type} {B : Builder N}
    (hok : parseTablesOk = true)
    {cs : Array Nat} {g : GrammarId} {cx : Ctx} {off : Nat} {src : Array Nat} {grp : Option (Nat → Bool)}
    {a1 a2 : NT → List Param → Nat → Src → Prop}
    {s : Src} {ps : List Param} {k : Nat} {is : List Item}
    {i1 j1 i2 j2 : Nat} {m1 m2 : List Bool} {ts1 ts2 : List DTree}
    (hsw1 : (codeAlphaSpec (T := T) B cs g cx off src grp).SeqWith a1 s ps k is i1 j1 m1 ts1)
    (hsw2 : (codeAlphaSpec (T := T) B cs g cx off src grp).SeqWith a2 s ps k is i2 j2 m2 ts2)
    (hmEq : m1 = m2)
    (htEq : ts1.map DTree.toTree = ts2.map DTree.toTree) :
    ts1 = ts2 :=
  match hsw1 with
  | .nil => by cases hsw2; rfl
  | .absent hr1 => by
    cases hsw2 with
    | absent hr2 => exact seqWith_toTree_inj hok hr1 hr2 (List.cons.inj hmEq).2 htEq
    | term _ _ => simp at hmEq
    | nt _ _ _ _ _ => simp at hmEq
    | leaf _ hl _ _ _ => exact nomatch hl
  | .term (o := o) (m := m1') _ hr1 => by
    cases hsw2 with
    | absent _ => simp at hmEq
    | term _ hr2 =>
      simp only [List.map, DTree.toTree] at htEq
      injection htEq with hleaf htl
      injection hleaf with hi hh
      subst hi; subst hh
      have hm' := by cases o with | false => exact hmEq | true => exact (List.cons.inj hmEq).2
      rw [seqWith_toTree_inj hok hr1 hr2 hm' htl]
  | .nt (o := o) (m := m1') _ hd1 _ _ hr1 => by
    cases hsw2 with
    | absent _ => simp at hmEq
    | leaf _ hl _ _ _ => exact nomatch hl
    | nt _ hd2 _ _ hr2 =>
      dsimp only [List.map] at htEq
      injection htEq with hhd htl
      have hdtEq := derivesWith_toTree_inj hok hd1 hd2 hhd
      subst hdtEq
      have hm' := by cases o with | false => exact hmEq | true => exact (List.cons.inj hmEq).2
      rw [seqWith_toTree_inj hok hr1 hr2 hm' htl]
  | .leaf _ hl _ _ _ => nomatch hl
  | .butNotT _ _ hr1 => by
    cases hsw2 with
    | butNotT _ _ hr2 =>
      simp only [List.map, DTree.toTree] at htEq
      injection htEq with hleaf htl
      injection hleaf with hi hh
      subst hi; subst hh
      rw [seqWith_toTree_inj hok hr1 hr2 hmEq htl]
  | .butNotN _ hd1 _ _ hr1 => by
    cases hsw2 with
    | butNotLeaf _ hl _ _ _ => exact nomatch hl
    | butNotN _ hd2 _ _ hr2 =>
      dsimp only [List.map] at htEq
      injection htEq with hhd htl
      have hdtEq := derivesWith_toTree_inj hok hd1 hd2 hhd
      subst hdtEq
      rw [seqWith_toTree_inj hok hr1 hr2 hmEq htl]
  | .butNotLeaf _ hl _ _ _ => nomatch hl
  | .phrase _ hr1 => by
    cases hsw2 with
    | phrase _ hr2 =>
      simp only [List.map, DTree.toTree] at htEq
      injection htEq with hleaf htl
      injection hleaf with hi hh
      subst hi; subst hh
      rw [seqWith_toTree_inj hok hr1 hr2 hmEq htl]
  | .look _ hr1 => by
    cases hsw2 with
    | look _ hr2 => exact seqWith_toTree_inj hok hr1 hr2 hmEq htEq
  | .noLT _ hr1 => by
    cases hsw2 with
    | noLT _ hr2 => exact seqWith_toTree_inj hok hr1 hr2 hmEq htEq
  | .empty hr1 => by
    cases hsw2 with
    | empty hr2 => exact seqWith_toTree_inj hok hr1 hr2 hmEq htEq
  | .onlyIf hr1 => by
    cases hsw2 with
    | onlyIf hr2 => exact seqWith_toTree_inj hok hr1 hr2 hmEq htEq
end

/-! ## B.1.2 Commitment (`GL.altPos`, `IsFirstAlt`, `Tree.Commits`, `Committed`) -/

private theorem first_split_of_mem {α : Type} [DecidableEq α] {x : α} :
    ∀ {xs : List α}, x ∈ xs → ∃ pre post, xs = pre ++ x :: post ∧ x ∉ pre
  | [], h => nomatch h
  | y :: ys, h => by
    by_cases hxy : y = x
    · subst hxy; exact ⟨[], ys, rfl, fun hm => nomatch hm⟩
    · rcases List.mem_cons.mp h with rfl | hmem
      · exact absurd rfl hxy
      · obtain ⟨pre, post, rfl, hnot⟩ := first_split_of_mem hmem
        refine ⟨y :: pre, post, rfl, fun hm => ?_⟩
        rcases List.mem_cons.mp hm with rfl | hmp
        · exact hxy rfl
        · exact hnot hmp

private theorem find_zipIdx_first {α : Type} (p : α → Bool) :
    ∀ (pre : List α) (x : α) (post : List α) (idx : Nat),
      (∀ y ∈ pre, p y = false) → p x = true →
      (((pre ++ x :: post).zipIdx idx).find? fun (y, _) => p y).map Prod.snd = some (idx + pre.length)
  | [], x, post, idx, _, hpx => by simp [hpx]
  | y :: pre, x, post, idx, hpre, hpx => by
    have hpy : p y = false := hpre y List.mem_cons_self
    simp only [List.cons_append, List.zipIdx_cons, List.find?_cons, hpy]
    rw [find_zipIdx_first p pre x post (idx + 1) (fun z hz => hpre z (List.mem_cons_of_mem _ hz)) hpx]
    simp [Nat.add_right_comm, Nat.add_assoc]

theorem altPos_of_first_split (hok : parseTablesOk = true) {cx : Ctx} {g : GrammarId}
    {n : NT} {s : Src} {m : List Bool} {id : Nat} {pre post : List Src}
    (hsplit : Ecma.Spec.gl.alts cx g n = pre ++ s :: post)
    (hnot : s ∉ pre)
    (hm : m ∈ masks s.alt.opts)
    (hpid : Ecma.Spec.gl.prodId s m = some id) :
    Ecma.Spec.gl.altPos cx g n id = some pre.length := by
  have hsMem : s ∈ Ecma.Spec.gl.alts cx g n := by rw [hsplit]; exact List.mem_append_right _ List.mem_cons_self
  obtain ⟨hpeqS, _, _, _, _⟩ := prodIdOf_spec hok hsMem hm
  obtain ⟨_, hoptsS⟩ := alt_lhs_and_opts hok hsMem
  have huniq := AlphaSpec.prodIdOf_mem_unique hok ((altsOf_eq hok cx g n).symm ▸ hsMem) (hoptsS ▸ hm) (hpeqS.trans hpid)
  unfold GL.altPos
  rw [hsplit]
  have hps : ((masks s.alt.opts).any fun m' => Ecma.Spec.gl.prodId s m' == some id) = true :=
    List.any_eq_true.mpr ⟨m, hm, beq_iff_eq.mpr hpid⟩
  have hpre : ∀ y ∈ pre, ((masks y.alt.opts).any fun m' => Ecma.Spec.gl.prodId y m' == some id) = false := by
    intro y hy
    rw [Bool.eq_false_iff, ne_eq, List.any_eq_true]
    rintro ⟨my, hmy, hpidY⟩
    rw [beq_iff_eq] at hpidY
    have hyMem : y ∈ Ecma.Spec.gl.alts cx g n := by rw [hsplit]; exact List.mem_append_left _ hy
    obtain ⟨hpeqY, idY, PY, hidY, hpoY, _, _, _, _, hfindY⟩ := prodIdOf_spec hok hyMem hmy
    have hidEq : idY = id := Option.some.inj (hidY.symm.trans hpidY)
    subst hidEq
    rw [← altsOf_eq hok cx g PY.rule.lhs] at hfindY
    obtain ⟨_, hyEqS⟩ := huniq.1 PY y hpoY hfindY
    subst hyEqS
    exact hnot hy
  simpa using find_zipIdx_first _ pre s post 0 hpre hps

theorem altPos_le_of_mem_prefix (hok : parseTablesOk = true) {cx : Ctx} {g : GrammarId}
    {n : NT} {s' : Src} {m' : List Bool} {id' : Nat} {pre tail : List Src}
    (hsplit : Ecma.Spec.gl.alts cx g n = pre ++ tail)
    (hmem : s' ∈ pre)
    (hm' : m' ∈ masks s'.alt.opts)
    (hpid' : Ecma.Spec.gl.prodId s' m' = some id') :
    ∃ k', Ecma.Spec.gl.altPos cx g n id' = some k' ∧ k' < pre.length := by
  obtain ⟨pre0, post0, rfl, hnot0⟩ := first_split_of_mem hmem
  have hsplit' : Ecma.Spec.gl.alts cx g n = pre0 ++ s' :: (post0 ++ tail) := by simp [hsplit]
  have hap := altPos_of_first_split hok hsplit' hnot0 hm' hpid'
  exact ⟨pre0.length, hap, by simp⟩

private theorem commits_all_iff {g : GrammarId} {cx : Ctx}
    {D : NT → List Param → Nat → Nat → Tree → Prop} :
    ∀ ks : List Tree, Tree.Commits.all Ecma.Spec.gl cx g D ks ↔ ∀ k ∈ ks, k.Commits Ecma.Spec.gl cx g D
  | [] => by simp [Tree.Commits.all]
  | d :: ds => by
    simp only [Tree.Commits.all, commits_all_iff ds, List.mem_cons, forall_eq_or_imp]

mutual
theorem modeDerives_true_to_commits {N T : Type} {B : Builder N} {P : CodePrims}
    (hok : parseTablesOk = true) {g : GrammarId} (hg : g ∈ codeGrammars)
    (hm : CodePrimsMatch B P) {grp : Option (Nat → Bool)} {cs : Array Nat}
    (hc : CondMatch grp cs P)
    (hcondSlice : ∀ c t1 t2, slice cs.toList t1.span.1 t1.span.2 = slice cs.toList t2.span.1 t2.span.2 →
      (P.cond c cs.toList t1 ↔ P.cond c cs.toList t2))
    {cx : Ctx} {off : Nat} {src : Array Nat}
    {n : NT} {ps : List Param} {i j : Nat} {dt : DTree}
    (hi : i ≤ cs.size)
    (hd : (codeAlphaSpec (T := T) B cs g cx off src grp).ModeDerives true n ps i j dt) :
    i ≤ j ∧ j ≤ cs.size ∧
      Derives Ecma.Spec.gl cx g (codeAlphabet P) cs.toList n ps i j dt.toTree ∧
      dt.toTree.Commits Ecma.Spec.gl cx g (Derives Ecma.Spec.gl cx g (codeAlphabet P) cs.toList) :=
  match hd with
  | .node s hsMem hal hgrd hpid hsw => by
    have ⟨hij, hjSz, hder⟩ := derivesWith_to_derives hok hg hm hc hi (.node s hsMem hal hgrd hpid hsw)
    have hkidsCom := seqWith_true_to_commits hok hg hm hc hcondSlice hi hsw
    refine ⟨hij, hjSz, hder, ?_⟩
    rw [DTree.toTree]; dsimp only [Tree.Commits]
    refine ⟨?_, (commits_all_iff _).mpr hkidsCom⟩
    intro hordN h' id' kids' k k' hder' hap hap'
    have hordC : (orderedNtsBy cx g).contains n = true := by
      rw [orderedNtsBy_eq hok, List.contains_iff_mem]; exact hordN
    dsimp only [AlphaSpec.CommitAllow, Code.alpha] at hal
    simp only [Bool.true_and, hordC, ↓reduceIte] at hal
    obtain ⟨pre, post, haltsEq, hgrdS, hexS, hnoPre⟩ := hal
    rw [altsOf_eq hok] at haltsEq
    have hsNotPre : s ∉ pre := fun hsIn => hnoPre s hsIn hgrdS hexS
    have hsSpec : s ∈ Ecma.Spec.gl.alts cx g n := (altsOf_eq hok cx g n) ▸ hsMem
    obtain ⟨_, hoptsS⟩ := alt_lhs_and_opts hok hsSpec
    have hmS := hoptsS ▸ (codeAlphaSpec (T := T) B cs g cx off src grp).seqWith_masks hsw
    obtain ⟨hpeqS, _, _, _, _⟩ := prodIdOf_spec hok hsSpec hmS
    have hapEq := altPos_of_first_split hok haltsEq hsNotPre hmS (hpeqS.symm.trans hpid)
    have hkEq : k = pre.length := Option.some.inj (hap.symm.trans hapEq)
    subst hkEq
    have hclamp' := derives_clamp_node hok hcondSlice hg (by simpa using hi) hder'
    have hminSz : min h' cs.toList.length ≤ cs.size := by
      rw [Array.length_toList]; exact Nat.min_le_right _ _
    obtain ⟨dt', hdt'Eq, hpl'⟩ := derives_to_plainDerives (T := T) (B := B) (off := off) (src := src)
      hok hg hm hc hminSz hclamp'
    cases hpl' with
    | @node _ _ _ _ m' _ id0' s' hsMem' _ hgrd' hpid' hsw' =>
      simp only [DTree.toTree] at hdt'Eq
      injection hdt'Eq with _ hid' _ _ _ _
      subst hid'
      have hsSpec' : s' ∈ Ecma.Spec.gl.alts cx g n := (altsOf_eq hok cx g n) ▸ hsMem'
      obtain ⟨_, hopts'⟩ := alt_lhs_and_opts hok hsSpec'
      have hm' := hopts' ▸ (codeAlphaSpec (T := T) B cs g cx off src grp).seqWith_masks hsw'
      obtain ⟨hpeq', _, _, _, _⟩ := prodIdOf_spec hok hsSpec' hm'
      apply Classical.byContradiction; intro hltK
      have hs'NotPre : s' ∉ pre := fun hs'In => hnoPre s' hs'In hgrd' ⟨_, _, _, hsw'⟩
      have hs'InTail : s' ∈ s :: post := by
        rw [haltsEq] at hsSpec'
        rcases List.mem_append.mp hsSpec' with h1 | h2
        · exact absurd h1 hs'NotPre
        · exact h2
      obtain ⟨pre2, post2, hsp2, hnot2⟩ := first_split_of_mem hs'InTail
      have hfull2 : Ecma.Spec.gl.alts cx g n = (pre ++ pre2) ++ s' :: post2 := by
        rw [haltsEq, hsp2, List.append_assoc]
      have hnotFull2 : s' ∉ pre ++ pre2 := by
        intro hm2; rcases List.mem_append.mp hm2 with h1 | h2
        · exact hs'NotPre h1
        · exact hnot2 h2
      have hap'Eq := altPos_of_first_split hok hfull2 hnotFull2 hm' (hpeq'.symm.trans hpid')
      have hk'Eq : k' = (pre ++ pre2).length := Option.some.inj (hap'.symm.trans hap'Eq)
      rw [hk'Eq, List.length_append] at hltK
      omega

theorem seqWith_true_to_commits {N T : Type} {B : Builder N} {P : CodePrims}
    (hok : parseTablesOk = true) {g : GrammarId} (hg : g ∈ codeGrammars)
    (hm : CodePrimsMatch B P) {grp : Option (Nat → Bool)} {cs : Array Nat}
    (hc : CondMatch grp cs P)
    (hcondSlice : ∀ c t1 t2, slice cs.toList t1.span.1 t1.span.2 = slice cs.toList t2.span.1 t2.span.2 →
      (P.cond c cs.toList t1 ↔ P.cond c cs.toList t2))
    {cx : Ctx} {off : Nat} {src : Array Nat}
    {s : Src} {ps : List Param} {k : Nat} {is : List Item} {i j : Nat} {m : List Bool} {ts : List DTree}
    (hi : i ≤ cs.size)
    (hsw : (codeAlphaSpec (T := T) B cs g cx off src grp).SeqWith
      ((codeAlphaSpec (T := T) B cs g cx off src grp).CommitAllow true) s ps k is i j m ts) :
    ∀ t ∈ ts.map DTree.toTree, t.Commits Ecma.Spec.gl cx g (Derives Ecma.Spec.gl cx g (codeAlphabet P) cs.toList) :=
  match hsw with
  | .nil => fun _ h => nomatch h
  | .absent hr => seqWith_true_to_commits hok hg hm hc hcondSlice hi hr
  | .term ht hr => by
    obtain ⟨_, hhSz, _⟩ := codeTerm_sound hm cs s k _ _ _ ht
    have htl := seqWith_true_to_commits hok hg hm hc hcondSlice hhSz hr
    intro t htMem
    rcases List.mem_cons.mp htMem with rfl | hrest
    · simp [DTree.toTree, Tree.Commits]
    · exact htl t hrest
  | .nt _ hd0 _ _ hr => by
    have ⟨_, hhSz, _, hcom0⟩ := modeDerives_true_to_commits hok hg hm hc hcondSlice hi hd0
    have htl := seqWith_true_to_commits hok hg hm hc hcondSlice hhSz hr
    intro t htMem
    rcases List.mem_cons.mp htMem with rfl | hrest
    · exact hcom0
    · exact htl t hrest
  | .leaf _ hl _ _ _ => nomatch hl
  | .butNotT ht _ hr => by
    obtain ⟨_, hhSz, _⟩ := codeTerm_sound hm cs s k _ _ _ ht
    have htl := seqWith_true_to_commits hok hg hm hc hcondSlice hhSz hr
    intro t htMem
    rcases List.mem_cons.mp htMem with rfl | hrest
    · simp [DTree.toTree, Tree.Commits]
    · exact htl t hrest
  | .butNotN _ hd0 _ _ hr => by
    have ⟨_, hhSz, _, hcom0⟩ := modeDerives_true_to_commits hok hg hm hc hcondSlice hi hd0
    have htl := seqWith_true_to_commits hok hg hm hc hcondSlice hhSz hr
    intro t htMem
    rcases List.mem_cons.mp htMem with rfl | hrest
    · exact hcom0
    · exact htl t hrest
  | .butNotLeaf _ hl _ _ _ => nomatch hl
  | .phrase ⟨_, hcGet, _, rfl⟩ hr => by
    have hhSz : i + 1 ≤ cs.size := by have := (Array.getElem?_eq_some_iff.mp hcGet).1; omega
    have htl := seqWith_true_to_commits hok hg hm hc hcondSlice hhSz hr
    intro t htMem
    rcases List.mem_cons.mp htMem with rfl | hrest
    · simp [DTree.toTree, Tree.Commits]
    · exact htl t hrest
  | .look _ hr => seqWith_true_to_commits hok hg hm hc hcondSlice hi hr
  | .noLT _ hr => seqWith_true_to_commits hok hg hm hc hcondSlice hi hr
  | .empty hr => seqWith_true_to_commits hok hg hm hc hcondSlice hi hr
  | .onlyIf hr => seqWith_true_to_commits hok hg hm hc hcondSlice hi hr
end

mutual
theorem plain_and_commits_to_modeDerives {N T : Type} {B : Builder N} {P : CodePrims}
    (hok : parseTablesOk = true) {g : GrammarId} (hg : g ∈ codeGrammars)
    (hm : CodePrimsMatch B P) {grp : Option (Nat → Bool)} {cs : Array Nat}
    (hc : CondMatch grp cs P)
    {cx : Ctx} {off : Nat} {src : Array Nat}
    {n : NT} {ps : List Param} {i j : Nat} {dt : DTree}
    (hi : i ≤ cs.size)
    (hpl : (codeAlphaSpec (T := T) B cs g cx off src grp).PlainDerives n ps i j dt)
    (hcom : orderedBy cx g = true →
      dt.toTree.Commits Ecma.Spec.gl cx g (Derives Ecma.Spec.gl cx g (codeAlphabet P) cs.toList)) :
    (codeAlphaSpec (T := T) B cs g cx off src grp).ModeDerives true n ps i j dt :=
  match hpl with
  | .node (kids := kids0) s hsMem _ hgrd hpid hsw => by
    let S := codeAlphaSpec (T := T) B cs g cx off src grp
    have hal : S.CommitAllow true n ps i s := by
      dsimp only [AlphaSpec.CommitAllow, S, codeAlphaSpec, Code.alpha]
      by_cases hordC : (orderedNtsBy cx g).contains n = true
      · simp only [Bool.true_and, hordC, ↓reduceIte]
        have hordG : orderedBy cx g = true := orderedBy_true_of_contains_orderedNts hok hordC
        have hcomNode := hcom hordG
        rw [DTree.toTree] at hcomNode
        have ⟨hrootCom, _⟩ := hcomNode
        have hordSpec : n ∈ Ecma.Spec.gl.orderedNts cx g := by
          rw [← orderedNtsBy_eq hok, ← List.contains_iff_mem]; exact hordC
        have hsSpec : s ∈ Ecma.Spec.gl.alts cx g n := (altsOf_eq hok cx g n) ▸ hsMem
        obtain ⟨pre, post, haltsEq, hsNotPre⟩ := first_split_of_mem hsSpec
        obtain ⟨_, hoptsS⟩ := alt_lhs_and_opts hok hsSpec
        have hmS := hoptsS ▸ S.seqWith_masks hsw
        obtain ⟨hpeqS, _, _, _, _⟩ := prodIdOf_spec hok hsSpec hmS
        have hapS := altPos_of_first_split hok haltsEq hsNotPre hmS (hpeqS.symm.trans hpid)
        refine ⟨pre, post, (altsOf_eq hok cx g n).trans haltsEq, hgrd, ⟨j, _, _, hsw⟩, ?_⟩
        intro s' hs'Pre hgrd' ⟨h', m', kids', hsw'⟩
        have hs'Spec : s' ∈ Ecma.Spec.gl.alts cx g n := by
          rw [haltsEq]; exact List.mem_append_left _ hs'Pre
        obtain ⟨_, hopts'⟩ := alt_lhs_and_opts hok hs'Spec
        have hm' := hopts' ▸ S.seqWith_masks hsw'
        obtain ⟨hpeq', id', _, hid', _⟩ := prodIdOf_spec hok hs'Spec hm'
        have hpl' : S.PlainDerives n ps i h' (.node n id' s' ps i h' m' kids') :=
          .node s' ((altsOf_eq hok cx g n).symm ▸ hs'Spec) trivial hgrd' (hpeq'.trans hid') hsw'
        have ⟨_, _, hder'⟩ := derivesWith_to_derives hok hg hm hc hi hpl'
        rw [DTree.toTree] at hder'
        obtain ⟨k', hap', hk'Lt⟩ := altPos_le_of_mem_prefix hok haltsEq hs'Pre hm' hid'
        have hle := hrootCom hordSpec h' id' (kids'.map DTree.toTree) pre.length k' hder' hapS hap'
        omega
      · have hordF : (orderedNtsBy cx g).contains n = false := Bool.eq_false_iff.mpr hordC
        simp only [hordF, Bool.and_false, Bool.false_eq_true, ↓reduceIte]
    have hkidsCom : orderedBy cx g = true →
        ∀ t ∈ kids0.map DTree.toTree,
          t.Commits Ecma.Spec.gl cx g (Derives Ecma.Spec.gl cx g (codeAlphabet P) cs.toList) := by
      intro hordG
      have hc0 := hcom hordG; rw [DTree.toTree] at hc0
      exact (commits_all_iff _).mp hc0.2
    exact .node s hsMem hal hgrd hpid (seqWith_plain_to_modeDerives hok hg hm hc hi hsw hkidsCom)

theorem seqWith_plain_to_modeDerives {N T : Type} {B : Builder N} {P : CodePrims}
    (hok : parseTablesOk = true) {g : GrammarId} (hg : g ∈ codeGrammars)
    (hm : CodePrimsMatch B P) {grp : Option (Nat → Bool)} {cs : Array Nat}
    (hc : CondMatch grp cs P)
    {cx : Ctx} {off : Nat} {src : Array Nat}
    {s : Src} {ps : List Param} {k : Nat} {is : List Item} {i j : Nat} {m : List Bool} {ts : List DTree}
    (hi : i ≤ cs.size)
    (hsw : (codeAlphaSpec (T := T) B cs g cx off src grp).SeqWith (fun _ _ _ _ => True) s ps k is i j m ts)
    (hcom : orderedBy cx g = true →
      ∀ t ∈ ts.map DTree.toTree, t.Commits Ecma.Spec.gl cx g (Derives Ecma.Spec.gl cx g (codeAlphabet P) cs.toList)) :
    (codeAlphaSpec (T := T) B cs g cx off src grp).SeqWith
      ((codeAlphaSpec (T := T) B cs g cx off src grp).CommitAllow true) s ps k is i j m ts :=
  match hsw with
  | .nil => .nil
  | .absent hr => .absent (seqWith_plain_to_modeDerives hok hg hm hc hi hr hcom)
  | .term ht hr => by
    obtain ⟨_, hhSz, _⟩ := codeTerm_sound hm cs s k _ _ _ ht
    exact .term ht (seqWith_plain_to_modeDerives hok hg hm hc hhSz hr
      fun ho t htMem => hcom ho t (List.mem_cons_of_mem _ htMem))
  | .nt hne hd0 hk hcd hr => by
    have ⟨_, hhSz, _⟩ := derivesWith_to_derives hok hg hm hc hi hd0
    have hd0' := plain_and_commits_to_modeDerives hok hg hm hc hi hd0
      (fun ho => hcom ho _ List.mem_cons_self)
    exact .nt hne hd0' hk hcd (seqWith_plain_to_modeDerives hok hg hm hc hhSz hr
      fun ho t htMem => hcom ho t (List.mem_cons_of_mem _ htMem))
  | .leaf _ hl _ _ _ => nomatch hl
  | .butNotT ht hex hr => by
    obtain ⟨_, hhSz, _⟩ := codeTerm_sound hm cs s k _ _ _ ht
    exact .butNotT ht hex (seqWith_plain_to_modeDerives hok hg hm hc hhSz hr
      fun ho t htMem => hcom ho t (List.mem_cons_of_mem _ htMem))
  | .butNotN hne hd0 hk hex hr => by
    have ⟨_, hhSz, _⟩ := derivesWith_to_derives hok hg hm hc hi hd0
    have hd0' := plain_and_commits_to_modeDerives hok hg hm hc hi hd0
      (fun ho => hcom ho _ List.mem_cons_self)
    exact .butNotN hne hd0' hk hex (seqWith_plain_to_modeDerives hok hg hm hc hhSz hr
      fun ho t htMem => hcom ho t (List.mem_cons_of_mem _ htMem))
  | .butNotLeaf _ hl _ _ _ => nomatch hl
  | .phrase ⟨c, hcGet, hpok, rfl⟩ hr => by
    have hhSz : i + 1 ≤ cs.size := by have := (Array.getElem?_eq_some_iff.mp hcGet).1; omega
    exact .phrase ⟨c, hcGet, hpok, rfl⟩ (seqWith_plain_to_modeDerives hok hg hm hc hhSz hr
      fun ho t htMem => hcom ho t (List.mem_cons_of_mem _ htMem))
  | .look hlk hr => .look hlk (seqWith_plain_to_modeDerives hok hg hm hc hi hr hcom)
  | .noLT hnl hr => .noLT hnl (seqWith_plain_to_modeDerives hok hg hm hc hi hr hcom)
  | .empty hr => .empty (seqWith_plain_to_modeDerives hok hg hm hc hi hr hcom)
  | .onlyIf hr => .onlyIf (seqWith_plain_to_modeDerives hok hg hm hc hi hr hcom)
end

/-! ## Relating `DNodeRel` to `Model.NodeRel` and `Code.countCapturing` to `Tree.countProds` -/

private theorem filter_map_toTree_not_isLeaf :
    ∀ ks : List DTree,
      (ks.map DTree.toTree).filter (fun t => !t.isLeaf) =
        (ks.filter fun dt => !dt.isLeaf).map DTree.toTree
  | [] => rfl
  | d :: ds => by
    simp only [List.map_cons, List.filter_cons, DTree.toTree_isLeaf]
    cases d.isLeaf <;> simp [filter_map_toTree_not_isLeaf ds]

private theorem sizeOf_filter_le {α : Type} [SizeOf α] (p : α → Bool) :
    ∀ xs : List α, sizeOf (xs.filter p) ≤ sizeOf xs
  | [] => Nat.le_refl _
  | x :: xs => by
    simp only [List.filter_cons]
    have ih := sizeOf_filter_le p xs
    cases p x <;> simp <;> omega

mutual
theorem dNodeRel_to_nodeRel {T : Type} {cs : Array Nat} {g : GrammarId} {cx : Ctx}
    {off : Nat} {src : Array Nat} {grp : Option (Nat → Bool)} {stamp : Nat}
    {nd : Engine.Model.Node} {dt : DTree}
    (hdrel : (codeAlphaSpec (T := T) Engine.builder cs g cx off src grp).DNodeRel stamp nd dt) :
    Ecma.Model.NodeRel Engine.Impl stamp src.toList (fun i j => (off + i, off + j)) nd dt.toTree :=
  match dt, hdrel with
  | _, .lex _ _ _ _ hleaf => nomatch hleaf
  | .node n id s ps i j m kids, .node hnt hprod hargs hst hsp htxt hkl => by
    have hdec : sizeOf (kids.filter fun dt => !dt.isLeaf) < sizeOf (DTree.node n id s ps i j m kids) := by
      have hle := sizeOf_filter_le (fun dt : DTree => !dt.isLeaf) kids
      simp +arith only [DTree.node.sizeOf_spec]; omega
    rw [DTree.toTree]
    rcases nd with ⟨st0, lo, hi, p0, nt0, ps0, ks0, txt0⟩
    dsimp only [Engine.builder] at hnt hprod hargs hst hsp htxt hkl
    dsimp only [codeAlphaSpec] at hsp htxt
    have hkRel := dNodeRelList_to_list hkl
    refine .node hnt hprod (by rw [hargs]; exact fun _ => Iff.rfl) hst hsp ?_ ?_ ?_ ?_ ?_
    · show Engine.Model.MathVal.int (txt0.toArray.map Engine.Impl.ofNat).size =
        Engine.Model.MathVal.int (slice src.toList (off + i) (off + j)).length
      rw [Array.size_map, htxt, ← extract_toList_eq_slice, Array.length_toList]
    · intro k
      rw [impl_seqGet_nat]
      show (txt0.toArray.map Engine.Impl.ofNat)[k]? =
        (slice src.toList (off + i) (off + j))[k]?.map Engine.Impl.ofNat
      rw [Array.getElem?_map, htxt, ← extract_toList_eq_slice, Array.getElem?_toList]
    · show Engine.Model.MathVal.int (ks0.filterMap Prod.snd).size =
        Engine.Model.MathVal.int ((kids.map DTree.toTree).filter (fun t => !t.isLeaf)).length
      rw [filter_map_toTree_not_isLeaf, ← Array.length_toList, Array.toList_filterMap, hkRel.1, List.length_map]
    · intro k
      rw [impl_seqGet_nat]
      change ((ks0.filterMap Prod.snd)[k]?.isSome = true) =
        (k < ((kids.map DTree.toTree).filter (fun t => !t.isLeaf)).length)
      rw [filter_map_toTree_not_isLeaf, ← Array.getElem?_toList, Array.toList_filterMap, List.length_map, ← hkRel.1]
      rcases opt_none_or_some ((ks0.toList.filterMap Prod.snd)[k]?) with hnone | ⟨_, hsome⟩
      · have hge := List.getElem?_eq_none_iff.mp hnone
        rw [hnone]; simp [show ¬ k < (ks0.toList.filterMap Prod.snd).length from by omega]
      · have hlt := (List.getElem?_eq_some_iff.mp hsome).1
        rw [hsome]; simp [hlt]
    · intro k tk ck htk hck
      rw [filter_map_toTree_not_isLeaf, List.getElem?_map] at htk
      rw [impl_seqGet_nat] at hck
      change (ks0.filterMap Prod.snd)[k]? = some ck at hck
      rw [← Array.getElem?_toList, Array.toList_filterMap] at hck
      rcases opt_none_or_some ((kids.filter fun dt => !dt.isLeaf)[k]?) with hnone | ⟨dtk, hdtk⟩
      · rw [hnone] at htk; cases htk
      · rw [hdtk, Option.map_some, Option.some.injEq] at htk
        subst htk
        exact hkRel.2 k ck dtk hck hdtk
termination_by sizeOf dt
decreasing_by exact hdec

theorem dNodeRelList_to_list {T : Type} {cs : Array Nat} {g : GrammarId} {cx : Ctx}
    {off : Nat} {src : Array Nat} {grp : Option (Nat → Bool)} {stamp : Nat}
    {nds : List Engine.Model.Node} {dts : List DTree}
    (hl : (codeAlphaSpec (T := T) Engine.builder cs g cx off src grp).DNodeRelList stamp nds dts) :
    nds.length = dts.length ∧
      ∀ (k : Nat) c (dt : DTree), nds[k]? = some c → dts[k]? = some dt →
        Ecma.Model.NodeRel Engine.Impl stamp src.toList (fun i j => (off + i, off + j)) c dt.toTree :=
  match dts, hl with
  | [], .nil => ⟨rfl, fun k _ _ hc _ => by simp at hc⟩
  | _ :: _, .cons hhd htl => by
    have hrHd := dNodeRel_to_nodeRel hhd
    have ⟨hlen, hrTl⟩ := dNodeRelList_to_list htl
    refine ⟨by simp [hlen], fun k c dt hc hdt => ?_⟩
    cases k with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hc hdt
      subst hc; subst hdt; exact hrHd
    | succ k' =>
      simp only [List.getElem?_cons_succ] at hc hdt
      exact hrTl k' c dt hc hdt
termination_by sizeOf dts
decreasing_by all_goals (simp_wf; omega)
end

private theorem sum_countProds_filter_not_isLeaf (ids : List Nat) :
    ∀ ks : List DTree,
      (((ks.map DTree.toTree).attach.map fun ⟨t, _⟩ => t.countProds ids)).sum =
        (((ks.filter fun dt => !dt.isLeaf).map fun dt => dt.toTree.countProds ids)).sum
  | [] => rfl
  | d :: ds => by
    have hattach : ∀ (l : List Tree),
        (l.attach.map fun ⟨t, _⟩ => t.countProds ids) = l.map (Tree.countProds ids) := by
      intro l; simp
    rw [hattach]
    have ih := sum_countProds_filter_not_isLeaf ids ds
    rw [hattach] at ih
    cases d with
    | leaf i j =>
      simp only [List.map_cons, DTree.toTree, Tree.countProds, List.sum_cons, Nat.zero_add, List.filter_cons, DTree.isLeaf, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      exact ih
    | lex n i j =>
      rw [List.map_cons, List.map_cons, List.sum_cons, List.filter_cons]
      have hnl : (!(DTree.lex n i j).isLeaf) = true := rfl
      simp only [hnl, ↓reduceIte, List.map_cons, List.sum_cons]
      exact congrArg _ ih
    | node n id s ps i j m kids =>
      rw [List.map_cons, List.map_cons, List.sum_cons, List.filter_cons]
      have hnl : (!(DTree.node n id s ps i j m kids).isLeaf) = true := rfl
      simp only [hnl, ↓reduceIte, List.map_cons, List.sum_cons]
      exact congrArg _ ih

mutual
theorem countCapturing_sound {N T : Type} {B : Builder N}
    (hok : parseTablesOk = true)
    {cs : Array Nat} {g : GrammarId} {cx : Ctx} {off : Nat} {src : Array Nat}
    {grp : Option (Nat → Bool)} {stamp : Nat}
    {d : Nat} {nd : N} {dt : DTree} {k : Nat}
    (hdrel : (codeAlphaSpec (T := T) B cs g cx off src grp).DNodeRel stamp nd dt)
    (hcnt : Code.countCapturing B d nd = .ok k) :
    k = dt.toTree.countProds Ecma.Spec.gl.capturingIds :=
  match d, hdrel with
  | 0, _ => by unfold Code.countCapturing at hcnt; cases hcnt
  | d + 1, .lex _ _ _ _ hleaf => nomatch hleaf
  | d + 1, .node (id := id) (kids := kids) _ hprod _ _ _ _ hkl => by
    unfold Code.countCapturing at hcnt
    rw [hprod] at hcnt
    have hkEq := countCapturing_list_sound hok d (if isCapturing id then 1 else 0) hkl hcnt
    have hcapEq : isCapturing id = Ecma.Spec.gl.capturingIds.contains id := by
      apply Bool.eq_iff_iff.mpr
      rw [isCapturing_iff hok id, List.contains_iff_mem]
    rw [DTree.toTree, Tree.countProds, sum_countProds_filter_not_isLeaf, hkEq, hcapEq]

theorem countCapturing_list_sound {N T : Type} {B : Builder N}
    (hok : parseTablesOk = true)
    {cs : Array Nat} {g : GrammarId} {cx : Ctx} {off : Nat} {src : Array Nat}
    {grp : Option (Nat → Bool)} {stamp : Nat}
    (d init : Nat) {nds : List N} {dts : List DTree} {out : Nat}
    (hkl : (codeAlphaSpec (T := T) B cs g cx off src grp).DNodeRelList stamp nds dts)
    (hfold : nds.foldlM (init := init) (fun a c => do let v ← Code.countCapturing B d c; pure (a + v)) = .ok out) :
    out = init + (dts.map fun dt => dt.toTree.countProds Ecma.Spec.gl.capturingIds).sum :=
  match hkl with
  | .nil => by
    simp only [List.foldlM_nil] at hfold
    cases hfold
    simp
  | .cons hhd htl => by
    simp only [List.foldlM_cons] at hfold
    rcases except_eq_err_or_ok (Code.countCapturing B d _) with ⟨err, Hc⟩ | ⟨v, Hc⟩
    · rw [Hc] at hfold; cases hfold
    · rw [Hc] at hfold
      dsimp only [Bind.bind, Except.bind, Pure.pure, Except.pure] at hfold
      have hvEq := countCapturing_sound hok hhd Hc
      have htlEq := countCapturing_list_sound hok d (init + v) htl hfold
      simp only [List.map_cons, List.sum_cons, hvEq] at htlEq ⊢
      omega
end

/-! ## `Code.parse`, `Code.groupLimit`, and `Code.run` -/

theorem code_parse_some_spec {T : Type}
    (hok : parseTablesOk = true) {g : GrammarId} (hg : g ∈ codeGrammars)
    {cs : Array Nat} {cx : Ctx} {off : Nat} {src : Array Nat}
    {stamp : Nat} {n : NT} {ps : List Param} {grp : Option (Nat → Bool)}
    {st st' : St T} {nd : Engine.Model.Node}
    (hm : st.memo = {}) (ha : st.active = {}) (hfw : st.fwd = {}) (hfi : st.first = {}) (hfar : st.far = 0)
    (hrun : (Code.parse Engine.builder cs g cx off src stamp n ps grp).run st = .ok (some nd, st')) :
    let S := codeAlphaSpec (T := T) Engine.builder cs g cx off src grp
    Engine.builder.nt nd = n.ctorIdx ∧
    Engine.builder.args nd = ps ∧
    ∃ dt,
      S.ModeDerives true n ps 0 cs.size dt ∧
      S.DNodeRel stamp nd dt ∧
      Ecma.Model.NodeRel Engine.Impl stamp src.toList (fun i j => (off + i, off + j)) nd dt.toTree ∧
      (∀ dt', S.ModeDerives true n ps 0 cs.size dt' → dt' = dt) := by
  let S := codeAlphaSpec (T := T) Engine.builder cs g cx off src grp
  unfold Code.parse at hrun
  obtain ⟨es, st1, hfe, hr1⟩ := sm_bind_ok hrun
  have hmi0 : S.MemoInv none st := AlphaSpec.MemoInv.fresh S trivial hm ha hfi hfar none
  have hna0 : ∀ x, st.active.contains x = false := fun x => by rw [ha, hs_empty]
  have ⟨hmi1, hna1, hfw1, _⟩ := S.finalEnds_spec hok (Or.inr hg) (Code.depth cs.size) n ps 0 st es st1 hmi0 hna0 hfe
  by_cases hmemSz : es.mem cs.size = true
  · simp only [hmemSz, ↓reduceIte] at hr1
    obtain ⟨ndBuilt, st2, hbld, hr2⟩ := sm_bind_ok hr1
    have hbi1 : S.BuildInv st1 := AlphaSpec.BuildInv.of_fresh_after_finalEnds hmi1 hna1 (hfw1.trans hfw)
    have ⟨_, hntB, hargsB, dt, hmd, hdrel, huniq⟩ :=
      S.build_spec hok builderSpec_engine (Or.inr hg) (Code.depth cs.size) stamp rfl (Code.depth cs.size)
        n ps 0 cs.size st1 ndBuilt st2 hbi1 hbld
    have hntChk : (Engine.builder.nt ndBuilt == n.ctorIdx) = true := beq_iff_eq.mpr hntB
    simp only [hntChk, ↓reduceIte] at hr2
    obtain ⟨hEqSome, _⟩ := sm_pure_ok hr2
    injection hEqSome with hndEq
    subst hndEq
    exact ⟨hntB, hargsB, dt, hmd, hdrel, dNodeRel_to_nodeRel hdrel, huniq⟩
  · have hmemF : es.mem cs.size = false := Bool.eq_false_iff.mpr hmemSz
    simp only [hmemF, Bool.false_eq_true, ↓reduceIte] at hr1
    obtain ⟨hEqNone, _⟩ := sm_pure_ok hr1
    cases hEqNone

theorem code_parse_none_spec {N T : Type} {B : Builder N}
    (hok : parseTablesOk = true) {g : GrammarId} (hg : g ∈ codeGrammars)
    {cs : Array Nat} {cx : Ctx} {off : Nat} {src : Array Nat}
    {stamp : Nat} {n : NT} {ps : List Param} {grp : Option (Nat → Bool)}
    {st st' : St T}
    (hm : st.memo = {}) (ha : st.active = {}) (hfi : st.first = {}) (hfar : st.far = 0)
    (hrun : (Code.parse B cs g cx off src stamp n ps grp).run st = .ok (none, st')) :
    ∀ dt, ¬ (codeAlphaSpec (T := T) B cs g cx off src grp).ModeDerives true n ps 0 cs.size dt := by
  let S := codeAlphaSpec (T := T) B cs g cx off src grp
  unfold Code.parse at hrun
  obtain ⟨es, st1, hfe, hr1⟩ := sm_bind_ok hrun
  have hmi0 : S.MemoInv none st := AlphaSpec.MemoInv.fresh S trivial hm ha hfi hfar none
  have hna0 : ∀ x, st.active.contains x = false := fun x => by rw [ha, hs_empty]
  have ⟨_, _, _, hesIff⟩ := S.finalEnds_spec hok (Or.inr hg) (Code.depth cs.size) n ps 0 st es st1 hmi0 hna0 hfe
  by_cases hmemSz : es.mem cs.size = true
  · simp only [hmemSz, ↓reduceIte] at hr1
    obtain ⟨ndBuilt, st2, _, hr2⟩ := sm_bind_ok hr1
    obtain ⟨_, hr3⟩ := sm_unless_throw_jp hr2
    obtain ⟨hEq, _⟩ := sm_pure_ok hr3; cases hEq
  · intro dt hmd
    exact hmemSz ((hesIff cs.size).mpr ⟨dt, hmd⟩)

theorem orderedBy_true_imp_regExp (hok : parseTablesOk = true) {cx : Ctx} {g : GrammarId}
    (ho : orderedBy cx g = true) : g = .regExp := by
  rw [orderedBy_eq hok] at ho
  unfold GL.ordered GL.overlays at ho
  by_cases hany : (!cx.annexB.any) = true
  · simp [hany] at ho
  · simp only [hany, Bool.false_eq_true, ↓reduceIte, List.any_eq_true, List.mem_filterMap] at ho
    obtain ⟨⟨b, m⟩, ⟨b0, _, hfb⟩, hkind⟩ := ho
    cases hbk : b0.kind with
    | main | supplemental _ => rw [hbk] at hfb; cases hfb
    | overlay sec md cd =>
      rw [hbk] at hfb
      by_cases hif : (overlayGrammar sec == g && cx.annexB.has sec && condHolds cx cd) = true
      · simp only [hif, ↓reduceIte] at hfb
        injection hfb with hbm
        injection hbm with hbEq _
        subst hbEq
        rw [hbk] at hkind
        cases sec <;> simp [overlayGrammar] at hkind hif
        exact hif.1.1.symm
      · simp only [hif, Bool.false_eq_true, ↓reduceIte] at hfb; cases hfb

private theorem condSlice_codePrims (inp : List Nat) :
    ∀ c (t1 t2 : Tree), slice inp t1.span.1 t1.span.2 = slice inp t2.span.1 t2.span.2 →
      (Engine.Model.codePrims.cond c inp t1 ↔ Engine.Model.codePrims.cond c inp t2) := by
  intro c t1 t2 hsc
  unfold Engine.Model.codePrims
  dsimp only
  rw [hsc]

private theorem condSlice_withGroup (inp : List Nat) (C : List Nat → Tree → Prop)
    (hC : ∀ t1 t2 : Tree, slice inp t1.span.1 t1.span.2 = slice inp t2.span.1 t2.span.2 → (C inp t1 ↔ C inp t2)) :
    ∀ c (t1 t2 : Tree), slice inp t1.span.1 t1.span.2 = slice inp t2.span.1 t2.span.2 →
      ((Engine.Model.codePrims.withGroup C).cond c inp t1 ↔
        (Engine.Model.codePrims.withGroup C).cond c inp t2) := by
  intro c t1 t2 hsc
  have hbase := condSlice_codePrims inp c t1 t2 hsc
  cases c <;> simp only [CodePrims.withGroup]
  any_goals exact hbase
  exact hC t1 t2 hsc

theorem groupLimit_spec (hok : parseTablesOk = true) {cs : Array Nat} {cx : Ctx}
    {f : Nat → Bool}
    (hgl : Code.groupLimit Engine.builder cs .regExp cx = .ok f) :
    CondMatch (some f) cs (Engine.Model.codePrims.withGroup (groupCond Ecma.Spec.gl cx Engine.Model.codePrims)) ∧
    (∀ c (t1 t2 : Tree), slice cs.toList t1.span.1 t1.span.2 = slice cs.toList t2.span.1 t2.span.2 →
      ((Engine.Model.codePrims.withGroup (groupCond Ecma.Spec.gl cx Engine.Model.codePrims)).cond c cs.toList t1 ↔
        (Engine.Model.codePrims.withGroup (groupCond Ecma.Spec.gl cx Engine.Model.codePrims)).cond c cs.toList t2)) := by
  have hgReg : GrammarId.regExp ∈ codeGrammars := by simp [codeGrammars]
  have hsliceGrp : ∀ c (t1 t2 : Tree), slice cs.toList t1.span.1 t1.span.2 = slice cs.toList t2.span.1 t2.span.2 →
      ((Engine.Model.codePrims.withGroup (groupCond Ecma.Spec.gl cx Engine.Model.codePrims)).cond c cs.toList t1 ↔
        (Engine.Model.codePrims.withGroup (groupCond Ecma.Spec.gl cx Engine.Model.codePrims)).cond c cs.toList t2) :=
    condSlice_withGroup cs.toList _ (fun t1 t2 hsc => by unfold groupCond; rw [hsc])
  refine ⟨?_, hsliceGrp⟩
  let P1 := Engine.Model.codePrims.withGroup (fun _ _ => True)
  have hm1 : CodePrimsMatch Engine.builder P1 := codePrimsMatch_withGroup codePrimsMatch_engine _
  have hc1 : CondMatch (some fun _ => true) cs P1 :=
    condMatch_withGroup cs (fun _ => true) (fun _ _ => True) (fun _ _ => ⟨fun _ => trivial, fun _ => rfl⟩)
  have hslice1 := condSlice_withGroup cs.toList (fun _ _ => True) (fun _ _ _ => Iff.rfl)
  unfold Code.groupLimit Code.runWith StateT.run' at hgl
  rcases except_eq_err_or_ok (Code.parse (T := Unit) Engine.builder cs .regExp cx 0 cs 0 .Pattern [] (some fun _ => true)
      { steps := Code.budget cs.size }) with ⟨err1, Hrun1⟩ | ⟨⟨optNd, st1'⟩, Hrun1⟩
  · rw [Hrun1] at hgl; cases hgl
  · rw [Hrun1] at hgl
    dsimp only [Functor.map, Except.map, Bind.bind, Except.bind] at hgl
    cases optNd with
    | some ndP =>
      dsimp only at hgl
      rcases except_eq_err_or_ok (Code.countCapturing Engine.builder (Code.depth cs.size) ndP) with ⟨errC, Hcnt⟩ | ⟨kCap, Hcnt⟩
      · rw [Hcnt] at hgl; cases hgl
      · rw [Hcnt] at hgl
        injection hgl with hfEq
        subst hfEq
        obtain ⟨_, _, dtP, hmdP, hdrelP, _, huniqP⟩ :=
          code_parse_some_spec hok hgReg rfl rfl rfl rfl rfl Hrun1
        have hkEq := countCapturing_sound hok hdrelP Hcnt
        have ⟨_, _, hderP, hcomP⟩ := modeDerives_true_to_commits hok hgReg hm1 hc1 hslice1 (Nat.zero_le _) hmdP
        have hCommittedP : Committed Ecma.Spec.gl cx P1 .regExp .Pattern [] cs.toList dtP.toTree := ⟨hderP, hcomP⟩
        apply condMatch_withGroup
        intro t _
        unfold groupCond
        rw [hkEq, decide_eq_true_eq]
        constructor
        · intro hle
          exact ⟨dtP.toTree, hCommittedP, hle⟩
        · rintro ⟨T, ⟨hderT, hcomT⟩, hleT⟩
          obtain ⟨dtT, hdtTEq, hplT⟩ := derives_to_plainDerives (T := Unit) (B := Engine.builder)
            (off := 0) (src := cs) hok hgReg hm1 hc1 (by simp) hderT
          have hmdT := plain_and_commits_to_modeDerives hok hgReg hm1 hc1 (Nat.zero_le _) hplT
            (fun _ => hdtTEq.symm ▸ hcomT)
          have hdtEq := huniqP dtT hmdT
          have hTEq : T = dtP.toTree := hdtTEq.symm.trans (congrArg DTree.toTree hdtEq)
          rwa [← hTEq]
    | none =>
      injection hgl with hfEq
      subst hfEq
      have hno1 := code_parse_none_spec hok hgReg rfl rfl rfl rfl Hrun1
      apply condMatch_withGroup
      intro t _
      simp only [Bool.false_eq_true, false_iff]
      rintro ⟨T, ⟨hderT, hcomT⟩, _⟩
      obtain ⟨dtT, hdtTEq, hplT⟩ := derives_to_plainDerives (T := Unit) (B := Engine.builder)
        (off := 0) (src := cs) hok hgReg hm1 hc1 (by simp) hderT
      have hmdT := plain_and_commits_to_modeDerives hok hgReg hm1 hc1 (Nat.zero_le _) hplT
        (fun _ => hdtTEq.symm ▸ hcomT)
      exact hno1 dtT hmdT

theorem code_run_some_spec (hok : parseTablesOk = true) {g : GrammarId} (hg : g ∈ codeGrammars)
    {cs : Array Nat} {cx : Ctx} {stamp : Nat} {n : NT} {ps : List Param} {nd : Engine.Model.Node}
    (hrun : Code.run Engine.builder cs g cx stamp n ps = .ok (some nd)) :
    ∃ t,
      ParsesCode Ecma.Spec.gl cx Engine.Model.codePrims g n ps cs.toList t ∧
      Ecma.Model.NodeRel Engine.Impl stamp cs.toList (fun i j => (i, j)) nd t := by
  unfold Code.run at hrun
  unfold ParsesCode
  by_cases hord : orderedBy cx g = true
  · have hgEq : g = .regExp := orderedBy_true_imp_regExp hok hord
    subst hgEq
    have hordSpec : Ecma.Spec.gl.ordered cx .regExp = true := (orderedBy_eq hok cx .regExp) ▸ hord
    simp only [hord, Bool.not_true, Bool.false_eq_true, ↓reduceIte, hordSpec] at hrun ⊢
    rcases except_eq_err_or_ok (Code.groupLimit Engine.builder cs .regExp cx) with ⟨errG, Hgl⟩ | ⟨f, Hgl⟩
    · rw [Hgl] at hrun; cases hrun
    · rw [Hgl] at hrun
      dsimp only [Bind.bind, Except.bind] at hrun
      unfold Code.runWith StateT.run' at hrun
      rcases except_eq_err_or_ok (Code.parse (T := Unit) Engine.builder cs .regExp cx 0 cs stamp n ps (some f)
          { steps := Code.budget cs.size }) with ⟨errP, Hp⟩ | ⟨⟨optN, st'⟩, Hp⟩
      · rw [Hp] at hrun; cases hrun
      · rw [Hp] at hrun
        injection hrun with hoptEq
        subst hoptEq
        obtain ⟨hcF, hsliceF⟩ := groupLimit_spec hok Hgl
        have hmF := codePrimsMatch_withGroup codePrimsMatch_engine (groupCond Ecma.Spec.gl cx Engine.Model.codePrims)
        obtain ⟨_, _, dt, hmd, _, hnrel, _⟩ := code_parse_some_spec hok hg rfl rfl rfl rfl rfl Hp
        have ⟨_, _, hder, hcom⟩ := modeDerives_true_to_commits hok hg hmF hcF hsliceF (Nat.zero_le _) hmd
        have hnrel0 : Ecma.Model.NodeRel Engine.Impl stamp cs.toList (fun i j => (i, j)) nd dt.toTree := by
          simpa using hnrel
        exact ⟨dt.toTree, ⟨by simpa using hder, hcom⟩, hnrel0⟩
  · have hordF : orderedBy cx g = false := Bool.eq_false_iff.mpr hord
    have hordSpec : Ecma.Spec.gl.ordered cx g = false := (orderedBy_eq hok cx g) ▸ hordF
    simp only [hordF, Bool.not_false, ↓reduceIte, hordSpec, Bool.false_eq_true] at hrun ⊢
    unfold StateT.run' at hrun
    rcases except_eq_err_or_ok (Code.parse (T := Unit) Engine.builder cs g cx 0 cs stamp n ps none
        { steps := Code.budget cs.size }) with ⟨errP, Hp⟩ | ⟨⟨optN, st'⟩, Hp⟩
    · rw [Hp] at hrun; cases hrun
    · rw [Hp] at hrun
      injection hrun with hoptEq
      subst hoptEq
      obtain ⟨_, _, dt, hmd, _, hnrel, _⟩ := code_parse_some_spec hok hg rfl rfl rfl rfl rfl Hp
      have ⟨_, _, hder⟩ := derivesWith_to_derives hok hg codePrimsMatch_engine (condMatch_none cs) (Nat.zero_le _) hmd
      have hnrel0 : Ecma.Model.NodeRel Engine.Impl stamp cs.toList (fun i j => (i, j)) nd dt.toTree := by
        simpa using hnrel
      exact ⟨dt.toTree, by simpa using hder, hnrel0⟩

theorem code_run_none_spec (hok : parseTablesOk = true) {g : GrammarId} (hg : g ∈ codeGrammars)
    {cs : Array Nat} {cx : Ctx} {stamp : Nat} {n : NT} {ps : List Param}
    (hrun : Code.run Engine.builder cs g cx stamp n ps = .ok none) :
    ∀ t, ¬ ParsesCode Ecma.Spec.gl cx Engine.Model.codePrims g n ps cs.toList t := by
  unfold Code.run at hrun
  unfold ParsesCode
  by_cases hord : orderedBy cx g = true
  · have hgEq : g = .regExp := orderedBy_true_imp_regExp hok hord
    subst hgEq
    have hordSpec : Ecma.Spec.gl.ordered cx .regExp = true := (orderedBy_eq hok cx .regExp) ▸ hord
    simp only [hord, Bool.not_true, Bool.false_eq_true, ↓reduceIte, hordSpec] at hrun ⊢
    rcases except_eq_err_or_ok (Code.groupLimit Engine.builder cs .regExp cx) with ⟨errG, Hgl⟩ | ⟨f, Hgl⟩
    · rw [Hgl] at hrun; cases hrun
    · rw [Hgl] at hrun
      dsimp only [Bind.bind, Except.bind] at hrun
      unfold Code.runWith StateT.run' at hrun
      rcases except_eq_err_or_ok (Code.parse (T := Unit) Engine.builder cs .regExp cx 0 cs stamp n ps (some f)
          { steps := Code.budget cs.size }) with ⟨errP, Hp⟩ | ⟨⟨optN, st'⟩, Hp⟩
      · rw [Hp] at hrun; cases hrun
      · rw [Hp] at hrun
        injection hrun with hoptEq
        subst hoptEq
        obtain ⟨hcF, _⟩ := groupLimit_spec hok Hgl
        have hmF := codePrimsMatch_withGroup codePrimsMatch_engine (groupCond Ecma.Spec.gl cx Engine.Model.codePrims)
        have hno := code_parse_none_spec hok hg rfl rfl rfl rfl Hp
        rintro t ⟨hderT, hcomT⟩
        obtain ⟨dtT, hdtTEq, hplT⟩ := derives_to_plainDerives (T := Unit) (B := Engine.builder)
          (off := 0) (src := cs) hok hg hmF hcF (by simp) hderT
        have hmdT := plain_and_commits_to_modeDerives hok hg hmF hcF (Nat.zero_le _) hplT
          (fun _ => hdtTEq.symm ▸ hcomT)
        exact hno dtT hmdT
  · have hordF : orderedBy cx g = false := Bool.eq_false_iff.mpr hord
    have hordSpec : Ecma.Spec.gl.ordered cx g = false := (orderedBy_eq hok cx g) ▸ hordF
    simp only [hordF, Bool.not_false, ↓reduceIte, hordSpec, Bool.false_eq_true] at hrun ⊢
    unfold StateT.run' at hrun
    rcases except_eq_err_or_ok (Code.parse (T := Unit) Engine.builder cs g cx 0 cs stamp n ps none
        { steps := Code.budget cs.size }) with ⟨errP, Hp⟩ | ⟨⟨optN, st'⟩, Hp⟩
    · rw [Hp] at hrun; cases hrun
    · rw [Hp] at hrun
      injection hrun with hoptEq
      subst hoptEq
      have hno := code_parse_none_spec hok hg rfl rfl rfl rfl Hp
      intro t hderT
      obtain ⟨dtT, _, hplT⟩ := derives_to_plainDerives (T := Unit) (B := Engine.builder)
        (off := 0) (src := cs) hok hg codePrimsMatch_engine (condMatch_none cs) (by simp) hderT
      have hmdT := plain_and_commits_to_modeDerives hok hg codePrimsMatch_engine (condMatch_none cs)
        (Nat.zero_le _) hplT (fun ho => by rw [hordF] at ho; cases ho)
      exact hno dtT hmdT

/-! ## `verifyCodeNode` soundness and `noFirst` completeness -/

private theorem condOk_of_noCondAfter {P : CodePrims} {inp : List Nat} {is : List Item}
    (h : noCondAfter is = true) (t : Tree) :
    CondOk (codeAlphabet P) inp is t := by
  cases is with
  | nil => trivial
  | cons hd _ =>
    cases hd with
    | onlyIf _ => cases h
    | _ => trivial

theorem verifyCodeNode_step_sound (hok : parseTablesOk = true)
    (cs : Array Nat) (cx : Ctx) (g : GrammarId) (st : Nat)
    {neg : NT → List Param → Nat → Nat → Prop} :
    ∀ (fuel : Nat) (nd : Engine.Model.Node) (t : Tree),
      Engine.verifyCodeNode cs cx g st fuel nd = some t →
      ∃ lhs, lhs.ctorIdx = Engine.Impl.nodeNt nd ∧
        t.span = Engine.Impl.nodeSpan nd ∧
        (∃ id kids, t = .node lhs id (Engine.Impl.nodeArgs nd) (Engine.Impl.nodeSpan nd).1 (Engine.Impl.nodeSpan nd).2 kids) ∧
        Step (codeAlphabet Engine.Model.codePrims) neg cs.toList Ecma.Spec.gl cx g
          lhs (Engine.Impl.nodeArgs nd) (Engine.Impl.nodeSpan nd).1 (Engine.Impl.nodeSpan nd).2 t ∧
        Ecma.Model.NodeRel Engine.Impl st cs.toList (fun i j => (i, j)) nd t := by
  intro fuel
  induction fuel with
  | zero => intro _ _ h; unfold Engine.verifyCodeNode at h; cases h
  | succ fuel ihFuel =>
    have viSound : ∀ (s : Src) (ps : List Param) (is : List Item) (k : Nat)
        (ms : List Bool) (ks : List (Nat × Option Engine.Model.Node)) (pos endPos : Nat) (ts : List Tree),
        Engine.verifyCodeNode.verifyItems cs cx g st fuel ps is ms ks pos = some (endPos, ts) →
        ms ∈ masks ((is.filter fun | .sym _ true => true | _ => false).length) ∧
        Ecma.Grammar.Seq (codeAlphabet Engine.Model.codePrims) neg cs.toList Ecma.Spec.gl cx g s ps k is pos endPos ms ts ∧
        (ks.filterMap Prod.snd).length = (ts.filter fun t => !t.isLeaf).length ∧
        (∀ (idx : Nat) tk ck, (ts.filter fun t => !t.isLeaf)[idx]? = some tk →
          (ks.filterMap Prod.snd)[idx]? = some ck →
          Ecma.Model.NodeRel Engine.Impl st cs.toList (fun i j => (i, j)) ck tk) := by
      intro s ps is
      induction is with
      | nil =>
        intro k ms ks pos endPos ts hv
        cases ms with
        | cons _ _ => simp [Engine.verifyCodeNode.verifyItems] at hv
        | nil =>
          cases ks with
          | cons _ _ => simp [Engine.verifyCodeNode.verifyItems] at hv
          | nil =>
            unfold Engine.verifyCodeNode.verifyItems at hv
            injection hv with hp; injection hp with he1 he2; subst he1; subst he2
            exact ⟨by simp [masks], .nil, rfl, fun idx _ _ ht _ => by simp at ht⟩
      | cons it is ihIs =>
        intro k ms ks pos endPos ts hv
        cases it with
        | sym sym0 o =>
          cases sym0 with
          | t x =>
            cases o with
            | false =>
              unfold Engine.verifyCodeNode.verifyItems at hv
              rcases opt_none_or_some (Code.termEnd Engine.builder cs x pos) with hnone | ⟨j, hj⟩
              · rw [hnone] at hv; cases hv
              · rw [hj] at hv; dsimp only [Bind.bind, Option.bind] at hv
                rcases opt_none_or_some (Engine.verifyCodeNode.verifyItems cs cx g st fuel ps is ms ks j) with Hvi | ⟨⟨e, ts'⟩, Hvi⟩
                · rw [Hvi] at hv; cases hv
                · rw [Hvi] at hv; dsimp only [Bind.bind, Option.bind, Pure.pure] at hv
                  injection hv with hp; injection hp with he1 he2; subst he1; subst he2
                  obtain ⟨_, _, hterm⟩ := codeTerm_sound codePrimsMatch_engine cs s k x pos j hj
                  have ⟨hm, hseq, hlen, hrel⟩ := ihIs (k + 1) ms ks j e ts' Hvi
                  exact ⟨by simpa using hm, .term hterm hseq, by simpa [Tree.isLeaf] using hlen, by simpa [Tree.isLeaf] using hrel⟩
            | true =>
              cases ms with
              | nil => simp [Engine.verifyCodeNode.verifyItems] at hv
              | cons mb ms' =>
                cases mb with
                | false =>
                  unfold Engine.verifyCodeNode.verifyItems at hv
                  have ⟨hm, hseq, hlen, hrel⟩ := ihIs (k + 1) ms' ks pos endPos ts hv
                  refine ⟨?_, .absent hseq, hlen, hrel⟩
                  rw [List.filter_cons_of_pos rfl, List.length_cons, masks]
                  exact List.mem_append.mpr (Or.inl (List.mem_map.mpr ⟨ms', hm, rfl⟩))
                | true =>
                  unfold Engine.verifyCodeNode.verifyItems at hv
                  rcases opt_none_or_some (Code.termEnd Engine.builder cs x pos) with hnone | ⟨j, hj⟩
                  · rw [hnone] at hv; cases hv
                  · rw [hj] at hv; dsimp only [Bind.bind, Option.bind] at hv
                    rcases opt_none_or_some (Engine.verifyCodeNode.verifyItems cs cx g st fuel ps is ms' ks j) with Hvi | ⟨⟨e, ts'⟩, Hvi⟩
                    · rw [Hvi] at hv; cases hv
                    · rw [Hvi] at hv; dsimp only [Bind.bind, Option.bind, Pure.pure] at hv
                      injection hv with hp; injection hp with he1 he2; subst he1; subst he2
                      obtain ⟨_, _, hterm⟩ := codeTerm_sound codePrimsMatch_engine cs s k x pos j hj
                      have ⟨hm, hseq, hlen, hrel⟩ := ihIs (k + 1) ms' ks j e ts' Hvi
                      refine ⟨?_, .term hterm hseq, by simpa [Tree.isLeaf] using hlen, by simpa [Tree.isLeaf] using hrel⟩
                      simp only [List.filter_cons, ↓reduceIte, List.length_cons, masks]
                      exact List.mem_append.mpr (Or.inr (List.mem_map.mpr ⟨ms', hm, rfl⟩))
          | nt m args =>
            cases o with
            | false =>
              cases ks with
              | nil => simp [Engine.verifyCodeNode.verifyItems] at hv
              | cons kslot ks' =>
                rcases kslot with ⟨kt, optC⟩
                cases optC with
                | none => simp [Engine.verifyCodeNode.verifyItems] at hv
                | some c =>
                  unfold Engine.verifyCodeNode.verifyItems at hv
                  obtain ⟨hg1, hv⟩ := Engine.Impl.guard_bind_some hv
                  simp only [Bool.and_eq_true, beq_iff_eq] at hg1
                  obtain ⟨⟨⟨⟨_, hntC⟩, hnoC⟩, hargsC⟩, hposC⟩ := hg1
                  rcases opt_none_or_some (Engine.verifyCodeNode cs cx g st fuel c) with Hvc | ⟨tc, Hvc⟩
                  · rw [Hvc] at hv; cases hv
                  · rw [Hvc] at hv; dsimp only [Bind.bind, Option.bind] at hv
                    rcases opt_none_or_some (Engine.verifyCodeNode.verifyItems cs cx g st fuel ps is ms ks' (Engine.builder.span c).2) with Hvi | ⟨⟨e, ts'⟩, Hvi⟩
                    · rw [Hvi] at hv; cases hv
                    · rw [Hvi] at hv; dsimp only [Bind.bind, Option.bind, Pure.pure] at hv
                      injection hv with hp; injection hp with he1 he2; subst he1; subst he2
                      have ⟨lhsC, hlhsC, _, ⟨idC, kidsC, htcEq⟩, hstC, hrelC⟩ := ihFuel c tc Hvc
                      have hntEq : Engine.Impl.nodeNt c = Engine.builder.nt c := by cases c; rfl
                      have hargsEq : Engine.Impl.nodeArgs c = Engine.builder.args c := by cases c; rfl
                      have hspEq : Engine.Impl.nodeSpan c = Engine.builder.span c := by cases c; rfl
                      have hlhsM : lhsC = m := nt_ctorIdx_inj (hlhsC.trans (hntEq.trans hntC))
                      subst lhsC
                      rw [hargsEq, hargsC, hspEq, hposC] at hstC
                      have htcNotLeaf : (!tc.isLeaf) = true := by rw [htcEq]; rfl
                      have ⟨hm, hseq, hlen, hrel⟩ := ihIs (k + 1) ms ks' (Engine.builder.span c).2 e ts' Hvi
                      refine ⟨by simpa using hm, Seq.nt (o := false) hstC (condOk_of_noCondAfter hnoC tc) hseq, by simp [htcNotLeaf, hlen], ?_⟩
                      intro idx tk ck htk hck
                      simp only [List.filter_cons, htcNotLeaf, ↓reduceIte, List.filterMap_cons] at htk hck
                      cases idx with
                      | zero =>
                        simp only [List.getElem?_cons_zero, Option.some.injEq] at htk hck
                        subst htk; subst hck; exact hrelC
                      | succ idx' =>
                        simp only [List.getElem?_cons_succ] at htk hck
                        exact hrel idx' tk ck htk hck
            | true =>
              cases ms with
              | nil => simp [Engine.verifyCodeNode.verifyItems] at hv
              | cons mb ms' =>
                cases mb with
                | false =>
                  cases ks with
                  | nil => simp [Engine.verifyCodeNode.verifyItems] at hv
                  | cons kslot ks' =>
                    rcases kslot with ⟨kt, optC⟩
                    cases optC with
                    | some _ => simp [Engine.verifyCodeNode.verifyItems] at hv
                    | none =>
                      unfold Engine.verifyCodeNode.verifyItems at hv
                      obtain ⟨_, hv⟩ := Engine.Impl.guard_bind_some hv
                      have ⟨hm, hseq, hlen, hrel⟩ := ihIs (k + 1) ms' ks' pos endPos ts hv
                      refine ⟨?_, .absent hseq, by simpa using hlen, by simpa using hrel⟩
                      rw [List.filter_cons_of_pos rfl, List.length_cons, masks]
                      exact List.mem_append.mpr (Or.inl (List.mem_map.mpr ⟨ms', hm, rfl⟩))
                | true =>
                  cases ks with
                  | nil => simp [Engine.verifyCodeNode.verifyItems] at hv
                  | cons kslot ks' =>
                    rcases kslot with ⟨kt, optC⟩
                    cases optC with
                    | none => simp [Engine.verifyCodeNode.verifyItems] at hv
                    | some c =>
                      unfold Engine.verifyCodeNode.verifyItems at hv
                      obtain ⟨hg1, hv⟩ := Engine.Impl.guard_bind_some hv
                      simp only [Bool.and_eq_true, beq_iff_eq] at hg1
                      obtain ⟨⟨⟨⟨_, hntC⟩, hnoC⟩, hargsC⟩, hposC⟩ := hg1
                      rcases opt_none_or_some (Engine.verifyCodeNode cs cx g st fuel c) with Hvc | ⟨tc, Hvc⟩
                      · rw [Hvc] at hv; cases hv
                      · rw [Hvc] at hv; dsimp only [Bind.bind, Option.bind] at hv
                        rcases opt_none_or_some (Engine.verifyCodeNode.verifyItems cs cx g st fuel ps is ms' ks' (Engine.builder.span c).2) with Hvi | ⟨⟨e, ts'⟩, Hvi⟩
                        · rw [Hvi] at hv; cases hv
                        · rw [Hvi] at hv; dsimp only [Bind.bind, Option.bind, Pure.pure] at hv
                          injection hv with hp; injection hp with he1 he2; subst he1; subst he2
                          have ⟨lhsC, hlhsC, _, ⟨idC, kidsC, htcEq⟩, hstC, hrelC⟩ := ihFuel c tc Hvc
                          have hntEq : Engine.Impl.nodeNt c = Engine.builder.nt c := by cases c; rfl
                          have hargsEq : Engine.Impl.nodeArgs c = Engine.builder.args c := by cases c; rfl
                          have hspEq : Engine.Impl.nodeSpan c = Engine.builder.span c := by cases c; rfl
                          have hlhsM : lhsC = m := nt_ctorIdx_inj (hlhsC.trans (hntEq.trans hntC))
                          subst lhsC
                          rw [hargsEq, hargsC, hspEq, hposC] at hstC
                          have htcNotLeaf : (!tc.isLeaf) = true := by rw [htcEq]; rfl
                          have ⟨hm, hseq, hlen, hrel⟩ := ihIs (k + 1) ms' ks' (Engine.builder.span c).2 e ts' Hvi
                          refine ⟨?_, Seq.nt (o := true) hstC (condOk_of_noCondAfter hnoC tc) hseq, by simp [htcNotLeaf, hlen], ?_⟩
                          · simp only [List.filter_cons, ↓reduceIte, List.length_cons, masks]
                            exact List.mem_append.mpr (Or.inr (List.mem_map.mpr ⟨ms', hm, rfl⟩))
                          · intro idx tk ck htk hck
                            simp only [List.filter_cons, htcNotLeaf, ↓reduceIte, List.filterMap_cons] at htk hck
                            cases idx with
                            | zero =>
                              simp only [List.getElem?_cons_zero, Option.some.injEq] at htk hck
                              subst htk; subst hck; exact hrelC
                            | succ idx' =>
                              simp only [List.getElem?_cons_succ] at htk hck
                              exact hrel idx' tk ck htk hck
        | empty =>
          unfold Engine.verifyCodeNode.verifyItems at hv
          have ⟨hm, hseq, hlen, hrel⟩ := ihIs (k + 1) ms ks pos endPos ts hv
          exact ⟨by simpa using hm, .empty hseq, hlen, hrel⟩
        | butNot _ _ | phrase _ | lookahead _ | noLT | onlyIf _ =>
          simp [Engine.verifyCodeNode.verifyItems] at hv
    intro nd t hv0
    rcases nd with ⟨st', lo, hi, pid, nt, ps, kids, txt⟩
    unfold Engine.verifyCodeNode at hv0
    obtain ⟨hg1, hv⟩ := Engine.Impl.guard_bind_some hv0
    clear hv0
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hg1
    obtain ⟨⟨⟨hstEq, hloHi⟩, hhiSz⟩, htxtEq⟩ := hg1
    subst st'
    rcases opt_none_or_some (prodOf pid) with hnoneP | ⟨P, hpo⟩
    · rw [hnoneP] at hv; cases hv
    · rw [hpo] at hv; dsimp only [Bind.bind, Option.bind] at hv
      obtain ⟨hlhsNt, hv⟩ := Engine.Impl.guard_bind_some hv
      rw [beq_iff_eq] at hlhsNt
      rcases opt_none_or_some ((altsOf cx g P.rule.lhs).find? fun e =>
          e.grammar == P.grammar && e.idx == P.alt && e.rule == P.rule) with hnoneS | ⟨s, hsFind⟩
      · rw [hnoneS] at hv; cases hv
      · rw [hsFind] at hv; dsimp only [Bind.bind, Option.bind] at hv
        obtain ⟨hg2, hv⟩ := Engine.Impl.guard_bind_some hv
        simp only [Bool.and_eq_true, beq_iff_eq] at hg2
        obtain ⟨hgrd, hpidOf⟩ := hg2
        rcases opt_none_or_some (Engine.verifyCodeNode.verifyItems cs cx g st fuel ps s.alt.rhs P.mask kids.toList lo) with Hvi | ⟨⟨endPos, ts⟩, Hvi⟩
        · rw [Hvi] at hv; cases hv
        · rw [Hvi] at hv; dsimp only [Bind.bind, Option.bind] at hv
          obtain ⟨hendEq, hv⟩ := Engine.Impl.guard_bind_some hv
          rw [beq_iff_eq] at hendEq; subst hendEq
          injection hv with htEq; subst htEq
          have hsMem : s ∈ Ecma.Spec.gl.alts cx g P.rule.lhs :=
            (altsOf_eq hok cx g P.rule.lhs) ▸ List.mem_of_find?_eq_some hsFind
          have ⟨hmask, hseq, hlenK, hkRel⟩ := viSound s ps s.alt.rhs 0 P.mask kids.toList lo endPos ts Hvi
          obtain ⟨_, hoptsS⟩ := alt_lhs_and_opts hok hsMem
          obtain ⟨hpeq, _, _, _, _⟩ := prodIdOf_spec hok hsMem (hoptsS ▸ hmask)
          have hpidSpec : Ecma.Spec.gl.prodId s P.mask = some pid := hpeq.symm.trans hpidOf
          refine ⟨P.rule.lhs, hlhsNt, rfl, ⟨pid, ts, rfl⟩, .node s hsMem hgrd hpidSpec hseq, ?_⟩
          refine .node hlhsNt.symm rfl (fun _ => Iff.rfl) rfl rfl ?_ ?_ ?_ ?_ ?_
          · show Engine.Model.MathVal.int (txt.toArray.map Engine.Impl.ofNat).size =
              Engine.Model.MathVal.int (slice cs.toList lo endPos).length
            rw [Array.size_map, htxtEq, ← extract_toList_eq_slice, Array.length_toList]
          · intro k
            rw [impl_seqGet_nat]
            show (txt.toArray.map Engine.Impl.ofNat)[k]? =
              (slice cs.toList lo endPos)[k]?.map Engine.Impl.ofNat
            rw [Array.getElem?_map, htxtEq, ← extract_toList_eq_slice, Array.getElem?_toList]
          · show Engine.Model.MathVal.int (kids.filterMap Prod.snd).size =
              Engine.Model.MathVal.int (ts.filter (fun t => !t.isLeaf)).length
            rw [← Array.length_toList, Array.toList_filterMap, hlenK]
          · intro k
            rw [impl_seqGet_nat]
            change ((kids.filterMap Prod.snd)[k]?.isSome = true) = (k < (ts.filter (fun t => !t.isLeaf)).length)
            rw [← Array.getElem?_toList, Array.toList_filterMap, ← hlenK]
            rcases opt_none_or_some ((kids.toList.filterMap Prod.snd)[k]?) with hnone | ⟨_, hsome⟩
            · have hge := List.getElem?_eq_none_iff.mp hnone
              rw [hnone]; simp [show ¬ k < (kids.toList.filterMap Prod.snd).length from by omega]
            · have hlt := (List.getElem?_eq_some_iff.mp hsome).1
              rw [hsome]; simp [hlt]
          · intro k tk ck htk hck
            rw [impl_seqGet_nat] at hck
            change (kids.filterMap Prod.snd)[k]? = some ck at hck
            rw [← Array.getElem?_toList, Array.toList_filterMap] at hck
            exact hkRel k tk ck htk hck

theorem verifyCodeNode_sound (hok : parseTablesOk = true)
    {cs : Array Nat} {cx : Ctx} {g : GrammarId} {st fuel : Nat}
    {goal : NT} {ps : List Param} {nd : Engine.Model.Node} {t : Tree}
    (hnt : Engine.builder.nt nd = goal.ctorIdx)
    (hargs : ∀ p, p ∈ Engine.builder.args nd ↔ p ∈ ps)
    (hsp : Engine.builder.span nd = (0, cs.size))
    (hv : Engine.verifyCodeNode cs cx g st fuel nd = some t) :
    ∃ t',
      Derives Ecma.Spec.gl cx g (codeAlphabet Engine.Model.codePrims) cs.toList goal ps 0 cs.size t' ∧
      Ecma.Model.NodeRel Engine.Impl st cs.toList (fun i j => (i, j)) nd t' := by
  have ⟨lhs, hlhsIdx, _, ⟨id, kids, htEq⟩, _, hrel0⟩ :=
    verifyCodeNode_step_sound (neg := fun _ _ _ _ => False) hok cs cx g st fuel nd t hv
  have hntEq : Engine.Impl.nodeNt nd = Engine.builder.nt nd := by cases nd; rfl
  have hargsEq : Engine.Impl.nodeArgs nd = Engine.builder.args nd := by cases nd; rfl
  have hspEq : Engine.Impl.nodeSpan nd = Engine.builder.span nd := by cases nd; rfl
  have hlhsGoal : lhs = goal := nt_ctorIdx_inj (hlhsIdx.trans (hntEq.trans hnt))
  subst lhs
  have hder0 : Derives Ecma.Spec.gl cx g (codeAlphabet Engine.Model.codePrims) cs.toList
      goal (Engine.Impl.nodeArgs nd) 0 cs.size t := by
    refine ⟨1, fun k hk => ?_⟩
    obtain ⟨k0, rfl⟩ : ∃ k0, k = k0 + 1 := ⟨k - 1, by omega⟩
    dsimp only [DerivesAt]
    have ⟨lhs', hlhs', _, _, hst', _⟩ :=
      verifyCodeNode_step_sound (neg := fun m ps' a b => ∃ t', DerivesAt Ecma.Spec.gl cx g (codeAlphabet Engine.Model.codePrims) cs.toList k0 m ps' a b t')
        hok cs cx g st fuel nd t hv
    have hlhsEq' : lhs' = goal := nt_ctorIdx_inj (hlhs'.trans (hntEq.trans hnt))
    subst lhs'
    rw [hspEq, hsp] at hst'
    exact hst'
  have hp : ∀ p, p ∈ Engine.Impl.nodeArgs nd ↔ p ∈ ps := by rw [hargsEq]; exact hargs
  obtain ⟨t', _, _, hrelMap, _, hder'⟩ := derives_congr_params hp hder0
  exact ⟨t', hder', hrelMap _ _ _ _ _ hrel0⟩

/-- Completeness of `Engine.noFirst`: when `Engine.noFirst goal cs = true`, no grammar in
`GrammarCtx.Parses` derives `(goal, ps)` over `cs.toList`. -/
theorem noFirst_complete (hok : parseTablesOk = true)
    {cx : Ctx} {P : CodePrims} {strict : Bool} {goal : NT} {ps : List Param} {cs : Array Nat}
    (hno : Engine.noFirst goal.ctorIdx cs = true) :
    ∀ t, ¬ ({ gl := Ecma.Spec.gl, cx := cx, P := P, strict := strict } : Ecma.GrammarCtx).Parses goal ps cs.toList t := by
  unfold Engine.noFirst Engine.firstSet at hno
  by_cases hgIdx : (goal.ctorIdx == NT.StringLiteral.ctorIdx) = true
  · simp only [hgIdx, ↓reduceIte] at hno
    have hgoal : goal = .StringLiteral := nt_ctorIdx_inj (beq_iff_eq.mp hgIdx)
    subst hgoal
    rcases opt_none_or_some cs[0]? with hnone | ⟨c, hc0⟩
    · rw [hnone] at hno; cases hno
    · rw [hc0] at hno
      dsimp only at hno
      simp only [Bool.not_eq_true', List.contains_cons, List.contains_nil, Bool.or_false, Bool.or_eq_false_iff,
        beq_eq_false_iff_ne] at hno
      obtain ⟨hne34, hne39⟩ := hno
      obtain ⟨hrSyn, hrLex, _, _, hordLex, _, _, hstrAlts, _⟩ := fast_invariants hok cx
      intro t hp
      unfold Ecma.GrammarCtx.Parses at hp
      have hnoSyn : (Ecma.Spec.gl.rulesOf .syntactic).any (·.lhs == .StringLiteral) = false := by
        rw [Bool.eq_false_iff, ne_eq]; intro h
        have := ruleNt_of_rulesOf hok h
        rw [hrSyn] at this; cases this
      simp only [hnoSyn, Bool.false_eq_true, ↓reduceIte] at hp
      obtain ⟨g, hgMem, hgRule, hpCode⟩ := hp
      have hgEq : g = .lexical := by
        have h1 := ruleNt_of_rulesOf hok hgRule
        have hmem : (g, NT.StringLiteral) ∈ codeGrammars.filterMap (fun g' => (ruleNt g' NT.StringLiteral.ctorIdx).map ((g', ·))) := by
          rw [List.mem_filterMap]
          exact ⟨g, hgMem, by rw [h1]; rfl⟩
        rw [hrLex, List.mem_singleton] at hmem
        injection hmem
      subst hgEq
      unfold ParsesCode at hpCode
      rw [← orderedBy_eq hok cx .lexical, hordLex] at hpCode
      simp only [Bool.false_eq_true, ↓reduceIte] at hpCode
      obtain ⟨K, hK⟩ := hpCode
      have hstep := hK (max K 2) (Nat.le_max_left K 2)
      obtain ⟨k0, hk0⟩ : ∃ k0, max K 2 = k0 + 2 := ⟨max K 2 - 2, by omega⟩
      rw [hk0] at hstep
      dsimp only [DerivesAt] at hstep
      generalize hi0 : (0 : Nat) = i0 at hstep
      generalize hj0 : cs.toList.length = j0 at hstep
      cases hstep with
      | lex _ _ hl => cases hl
      | node s hsMem _ _ hseq =>
        subst hi0; subst hj0
        have haltShape := hstrAlts s hsMem
        have htokS : ∀ it ∈ s.alt.rhs, srcItemTermOk it = true :=
          fun it hit => srcItemTermOk_of_mem hok hsMem hit
        generalize hrhs : s.alt.rhs = rhs0 at haltShape hseq
        cases rhs0 with
        | nil => cases haltShape
        | cons it rest =>
          have htokR : ∀ x ∈ rest, srcItemTermOk x = true :=
            fun x hx => htokS x (hrhs ▸ List.mem_cons_of_mem _ hx)
          cases it with
          | sym sym0 o =>
            cases sym0 with
            | nt _ _ => cases o <;> cases haltShape
            | t x =>
              cases o with
              | true => simp at haltShape
              | false =>
                cases x with
                | cp _ => simp at haltShape
                | text str b =>
                  by_cases hstrQ : str = "\""
                  · subst hstrQ
                    cases hseq with
                    | @term _ _ _ _ _ _ _ h _ _ _ ht hr =>
                      have hle := code_seq_le hok htokR hr
                      dsimp only [codeAlphabet] at ht
                      have hsc : slice cs.toList 0 h = [34] := ht
                      have hlt := (slice_nonempty_lt (by rw [hsc]; exact List.cons_ne_nil _ _)).1
                      obtain ⟨_, hget0, _⟩ := (slice_singleton_iff (Nat.le_of_lt hlt) hle).mp hsc
                      have hcEq : cs[0]? = some 34 := by simpa using hget0
                      rw [hc0] at hcEq; injection hcEq with hcVal
                      exact hne34 hcVal
                  · by_cases hstrS : str = "'"
                    · subst hstrS
                      cases hseq with
                      | @term _ _ _ _ _ _ _ h _ _ _ ht hr =>
                        have hle := code_seq_le hok htokR hr
                        dsimp only [codeAlphabet] at ht
                        have hsc : slice cs.toList 0 h = [39] := ht
                        have hlt := (slice_nonempty_lt (by rw [hsc]; exact List.cons_ne_nil _ _)).1
                        obtain ⟨_, hget0, _⟩ := (slice_singleton_iff (Nat.le_of_lt hlt) hle).mp hsc
                        have hcEq : cs[0]? = some 39 := by simpa using hget0
                        rw [hc0] at hcEq; injection hcEq with hcVal
                        exact hne39 hcVal
                    · simp [hstrQ, hstrS] at haltShape
          | _ => simp at haltShape
  · simp only [hgIdx, Bool.false_eq_true, ↓reduceIte] at hno

end Engine.Parse




