module

public import Engine.Parse.Syntax
public import Engine.Proofs.Parse.Tables
public import Engine.Proofs.Parse.Kernel
public import Engine.Proofs.Parse.SearchEnds
public import Engine.Proofs.Parse.Search
public import Engine.Proofs.Parse.Code
public import Engine.Proofs.Parse.Lex
public import Engine.Proofs.Parse.Strict

@[expose] public section

/-!
# Soundness and completeness of the syntactic parser with left-to-right ASI (`Engine.Parse.Syntax`)

Proves:
1. `synAlphaSpec`: instantiates `AlphaSpec` for `Syntax.alpha` over token boundaries `2 * p + v`.
2. Equivalence between `(synAlphaSpec ...).PlainDerives` / `SpecHit` and `Ecma.Grammar.SynDerives` /
   `SynHit`, plus exactness of `Syntax.insertion` against `NextASI` and determinism of `ValidASI`.
3. Bidirectional token-stream bridge (`tokBnd`) between boundary-indexed derivations (`DTree`) and
   token-indexed derivations (`Tree` over `(els, toks)`) preserving `Scans`, `GoalsAt`, `tokensOf`,
   `ASIOk`, `Sentence`, `ForHeadersExplicit`, `Model.NodeRel`, and `NonStrictOk`.
4. `syntax_run_some_spec` and `syntax_run_none_spec`: full soundness, uniqueness (for strictness
   completeness), and completeness of `Syntax.run`.
-/

namespace Engine.Parse

open Ecma.Grammar Search

abbrev firstOf : NT → Bool := Lex.firstOf

private theorem forKeep_two_mul (lhs m : NT) (x : Nat) : forKeep lhs m (2 * x) = true := by
  unfold forKeep
  simp

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

/-! ## Section 1: Boundary, `vsPending`, `SynLook`, `ScanTok`, and lexical tree helpers -/

theorem vsPending_iff (vs : List (Nat × Bool)) (i : Nat) :
    vsPending vs i = true ↔ i % 2 = 0 ∧ ∃ pb ∈ vs, pb.1 = i / 2 := by
  unfold vsPending
  simp only [Bool.and_eq_true, beq_iff_eq, List.any_eq_true]

theorem vsPending_odd (vs : List (Nat × Bool)) {i : Nat} (hodd : i % 2 = 1) :
    vsPending vs i = false := by
  cases hp : vsPending vs i with
  | false => rfl
  | true => obtain ⟨hev, _⟩ := (vsPending_iff vs i).mp hp; omega

theorem synLook_div2 (vs : List (Nat × Bool)) (i : Nat) :
    (SynLook vs i) / 2 = i / 2 := by
  unfold SynLook
  by_cases hp : vsPending vs i = true
  · simp only [hp, ↓reduceIte]
    obtain ⟨heven, _⟩ := (vsPending_iff vs i).mp hp
    omega
  · simp [hp]

theorem vsPending_synLook_false (vs : List (Nat × Bool)) (i : Nat) :
    vsPending vs (SynLook vs i) = false := by
  unfold SynLook
  by_cases hp : vsPending vs i = true
  · simp only [hp, ↓reduceIte]
    obtain ⟨heven, _⟩ := (vsPending_iff vs i).mp hp
    exact vsPending_odd vs (by omega)
  · simp only [hp, Bool.false_eq_true, ↓reduceIte]

theorem vsParen_eq_of_mem {vs : List (Nat × Bool)}
    (huniq : ∀ p b1 b2, (p, b1) ∈ vs → (p, b2) ∈ vs → b1 = b2)
    {p : Nat} {b : Bool} (hmem : (p, b) ∈ vs) :
    vsParen vs p = b := by
  unfold vsParen
  cases b with
  | true =>
    exact List.any_eq_true.mpr ⟨(p, true), hmem, by simp⟩
  | false =>
    rw [Bool.eq_false_iff, ne_eq, List.any_eq_true]
    rintro ⟨⟨q, b'⟩, hqm, hqb⟩
    simp only [Bool.and_eq_true, beq_iff_eq] at hqb
    obtain ⟨rfl, rfl⟩ := hqb
    exact Bool.false_ne_true (huniq q false true hmem hqm)

theorem mem_vs_of_vsPending {vs : List (Nat × Bool)}
    (huniq : ∀ p b1 b2, (p, b1) ∈ vs → (p, b2) ∈ vs → b1 = b2)
    {i : Nat} (hp : vsPending vs i = true) :
    i % 2 = 0 ∧ (i / 2, vsParen vs (i / 2)) ∈ vs := by
  obtain ⟨heven, ⟨p, b⟩, hmem, hpEq⟩ := (vsPending_iff vs i).mp hp
  dsimp only at hpEq; subst hpEq
  rw [vsParen_eq_of_mem huniq hmem]
  exact ⟨heven, hmem⟩

theorem scanTok_span_unique (hok : parseTablesOk = true) {cx : Ctx} {cs : Array Nat}
    (hcp : ∀ c ∈ cs.toList, c ≤ 0x10FFFF) {first : Bool} {lg : NT}
    {p a1 b1 a2 b2 : Nat} {lt1 lt2 : Bool} {tr1 tr2 : Tree}
    (h1 : ScanTok Ecma.Spec.gl cx Engine.Model.codePrims cs.toList first lg p a1 b1 lt1 tr1)
    (h2 : ScanTok Ecma.Spec.gl cx Engine.Model.codePrims cs.toList first lg p a2 b2 lt2 tr2) :
    a1 = a2 ∧ b1 = b2 ∧ lt1 = lt2 := by
  obtain ⟨htr1, _, hb1Len, _, hder1, hmax1, _⟩ := h1
  obtain ⟨htr2, _, hb2Len, _, hder2, hmax2, _⟩ := h2
  obtain ⟨rfl, rfl⟩ := trivia_unique hok hcp htr1 htr2
  have hle1 : b1 ≤ b2 := Classical.byContradiction fun hgt =>
    hmax2 b1 (by omega) hb1Len ⟨tr1, hder1⟩
  have hle2 : b2 ≤ b1 := Classical.byContradiction fun hgt =>
    hmax1 b2 (by omega) hb2Len ⟨tr2, hder2⟩
  exact ⟨rfl, by omega, rfl⟩

theorem slice_head_getElem? {cs : Array Nat} {a b c0 : Nat} {rest : List Nat}
    (hab : a < b) (hb : b ≤ cs.size) (hsc : slice cs.toList a b = c0 :: rest) :
    cs[a]? = some c0 := by
  have haLt : a < cs.toList.length := by rw [Array.length_toList]; omega
  have hh : (slice cs.toList a b).head? = some c0 := by rw [hsc]; rfl
  unfold slice at hh
  obtain ⟨d, hd⟩ : ∃ d, b - a = d + 1 := ⟨b - a - 1, by omega⟩
  rw [hd, List.drop_eq_getElem_cons haLt, List.take_succ_cons, List.head?_cons, Option.some.injEq] at hh
  rw [Array.getElem?_eq_getElem (by omega), Option.some.injEq]
  simpa using hh

theorem derives_code_nt? {cx : Ctx} {P : CodePrims} {g : GrammarId} {inp : List Nat}
    {n : NT} {ps : List Param} {i j : Nat} {t : Tree}
    (hd : Derives Ecma.Spec.gl cx g (codeAlphabet P) inp n ps i j t) :
    t.nt? = some n := by
  obtain ⟨K, hK⟩ := hd
  have hs := hK (max K 1) (Nat.le_max_left K 1)
  obtain ⟨k0, hk0⟩ : ∃ k0, max K 1 = k0 + 1 := ⟨max K 1 - 1, by omega⟩
  rw [hk0] at hs
  cases hs with
  | node _ _ _ _ _ => rfl
  | lex _ _ hl => cases hl

/-! ## Section 2: `Syntax.lexP`, `Syntax.lex`, `Syntax.leafOf`, and `synAlphaSpec` -/

theorem lexP_spec {cs : Array Nat} {first : Bool} {cx : Ctx} {goal : NT} {p : Nat}
    {st st' : St (Syntax.Memo Engine.builder cs first cx)}
    {res : {r : Lex.Lexed // Lex.lexAtPure Engine.builder cs first cx goal p = .ok r}}
    (hrun : (Syntax.lexP Engine.builder cs first cx goal p).run st = .ok (res, st')) :
    st'.memo = st.memo ∧ st'.active = st.active ∧ st'.reads = st.reads ∧
    st'.fwd = st.fwd ∧ st'.first = st.first ∧ st'.far = st.far := by
  unfold Syntax.lexP at hrun
  obtain ⟨_, _, hget, hrun⟩ := sm_bind_ok hrun
  cases hget
  have hjp : ((match h : Lex.lexAtPure Engine.builder cs first cx goal p with
      | .ok r => do
        modify fun s => { s with toks := s.toks.insert (p, goal.ctorIdx) (.tok p goal r h) }
        pure ⟨r, h⟩
      | .error e => throw e) : SM (Syntax.Memo Engine.builder cs first cx) _).run st = .ok (res, st') →
      st'.memo = st.memo ∧ st'.active = st.active ∧ st'.reads = st.reads ∧
      st'.fwd = st.fwd ∧ st'.first = st.first ∧ st'.far = st.far := by
    intro hr
    split at hr
    · obtain ⟨_, s2, hm, hp⟩ := sm_bind_ok hr
      rw [sm_run_modify] at hm; cases hm
      obtain ⟨_, rfl⟩ := sm_pure_ok hp
      exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
    · rw [sm_run_throw] at hr; cases hr
  rcases htk : st.toks[(p, goal.ctorIdx)]? with _ | entry
  · rw [htk] at hrun; dsimp only at hrun; exact hjp hrun
  · rw [htk] at hrun
    cases entry with
    | leaf _ _ _ _ => dsimp only at hrun; exact hjp hrun
    | tok p' g' r0 h0 =>
      dsimp only at hrun
      by_cases hk : p' = p ∧ g' = goal
      · simp only [hk, and_self, ↓reduceDIte] at hrun
        obtain ⟨_, rfl⟩ := sm_pure_ok hrun
        exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
      · simp only [hk, ↓reduceDIte] at hrun
        exact hjp hrun

theorem lex_spec {cs : Array Nat} {first : Bool} {cx : Ctx} {goal : NT} {p : Nat}
    {st st' : St (Syntax.Memo Engine.builder cs first cx)} {r : Lex.Lexed}
    (hrun : (Syntax.lex Engine.builder cs first cx goal p).run st = .ok (r, st')) :
    st'.memo = st.memo ∧ st'.active = st.active ∧ st'.reads = st.reads ∧
    st'.fwd = st.fwd ∧ st'.first = st.first ∧ st'.far = st.far ∧
    ∃ r0, r = Syntax.tokOf r0 ∧ Lex.lexAtPure Engine.builder cs first cx goal p = .ok r0 := by
  unfold Syntax.lex at hrun
  obtain ⟨⟨r0, hr0⟩, s1, hlp, hp⟩ := sm_bind_ok hrun
  obtain ⟨rfl, rfl⟩ := sm_pure_ok hp
  have ⟨hm, ha, hrd, hfw, hfi, hfar⟩ := lexP_spec hlp
  exact ⟨hm, ha, hrd, hfw, hfi, hfar, r0, rfl, hr0⟩

theorem tokOf_eq_tok_iff {r0 : Lex.Lexed} {t : Lex.Tok} :
    Syntax.tokOf r0 = .tok t ↔ r0 = .tok t := by
  cases r0 <;> simp [Syntax.tokOf]

theorem tokOf_eq_eof_iff {r0 : Lex.Lexed} {lt : Bool} :
    Syntax.tokOf r0 = .eof lt ↔ r0 = .eof lt := by
  cases r0 <;> simp [Syntax.tokOf]

theorem lexAtPureSpec_tok {cx : Ctx} {cs : Array Nat} {first : Bool} {goal : NT} {pos : Nat}
    {tok : Lex.Tok} (hsp : LexAtPureSpec cx cs first goal pos (.tok tok)) :
    let sk := Lex.skip Engine.builder cs first cx pos
    Trivia Ecma.Spec.gl cx Engine.Model.codePrims cs.toList first pos sk.1 sk.2 ∧
    tok.i = sk.1 ∧ tok.lt = sk.2 ∧ pos ≤ sk.1 ∧ sk.1 < tok.j ∧ tok.j ≤ cs.size ∧
    (∃ tr, ScanTok Ecma.Spec.gl cx Engine.Model.codePrims cs.toList first goal pos sk.1 tok.j sk.2 tr ∧
      tr.has .NumericLiteral sk.1 tok.j = (tok.cls == .NumericLiteral)) ∧
    (∀ a b lt0 tr,
      ScanTok Ecma.Spec.gl cx Engine.Model.codePrims cs.toList first goal pos a b lt0 tr →
      a = sk.1 ∧ b = tok.j ∧ lt0 = sk.2) :=
  hsp

theorem lexAtPureSpec_eof {cx : Ctx} {cs : Array Nat} {first : Bool} {goal : NT} {pos : Nat}
    {lt0 : Bool} (hsp : LexAtPureSpec cx cs first goal pos (.eof lt0)) :
    let sk := Lex.skip Engine.builder cs first cx pos
    Trivia Ecma.Spec.gl cx Engine.Model.codePrims cs.toList first pos sk.1 sk.2 ∧
    lt0 = sk.2 ∧ cs.size ≤ sk.1 ∧
    (∀ a b lt1 tr, ¬ ScanTok Ecma.Spec.gl cx Engine.Model.codePrims cs.toList first goal pos a b lt1 tr) :=
  hsp

theorem lexAtPureSpec_not_tok {cx : Ctx} {cs : Array Nat} {first : Bool} {goal : NT} {p : Nat}
    {r0 : Lex.Lexed} (hsp : LexAtPureSpec cx cs first goal p r0)
    (hnot : ∀ t, Syntax.tokOf r0 ≠ .tok t) :
    ∀ a b lt0 tr, ¬ ScanTok Ecma.Spec.gl cx Engine.Model.codePrims cs.toList first goal p a b lt0 tr :=
  match r0, hsp with
  | .eof _, h => h.2.2.2
  | .bad _, h => h.2.2.2
  | .follow _, h => h.2.2.2.2
  | .tok t, _ => absurd rfl (hnot t)

theorem leafOf_spec (hok : parseTablesOk = true) {cx : Ctx} {cs : Array Nat}
    (hcp : ∀ c ∈ cs.toList, c ≤ 0x10FFFF) {first : Bool} {n : NT} {p : Nat}
    {r0 : Lex.Lexed} {opt : Option Nat}
    (hlex : Lex.lexAtPure Engine.builder cs first cx (Syntax.goalOf n) p = .ok r0)
    (hlf : Syntax.leafOf Engine.builder cs cx n r0 = .ok opt) :
    (∃ a b lt tr t,
      opt = some (2 * b) ∧
      ScanTok Ecma.Spec.gl cx Engine.Model.codePrims cs.toList first (lexicalGoalOf n) p a b lt tr ∧
      Derives Ecma.Spec.gl cx .lexical (codeAlphabet Engine.Model.codePrims) (slice cs.toList a b) n [] 0 (b - a) t) ∨
    (opt = none ∧ ∀ a b lt tr t,
      ScanTok Ecma.Spec.gl cx Engine.Model.codePrims cs.toList first (lexicalGoalOf n) p a b lt tr →
      ¬ Derives Ecma.Spec.gl cx .lexical (codeAlphabet Engine.Model.codePrims) (slice cs.toList a b) n [] 0 (b - a) t) := by
  have hsp := lexAtPure_ok_spec hok hcp (isSynLexGoal_lexicalGoalOf n) hlex
  have hgLex : GrammarId.lexical ∈ codeGrammars := by decide
  have hordLex : orderedBy cx .lexical = false := (fast_invariants hok cx).2.2.2.2.1
  cases r0 with
  | eof _ | bad _ | follow _ =>
    dsimp only [Syntax.leafOf, pure, Except.pure] at hlf
    injection hlf with hoptEq
    refine Or.inr ⟨hoptEq.symm, fun a b lt tr _ hscan _ => ?_⟩
    exact lexAtPureSpec_not_tok hsp (fun _ h => by cases h) a b lt tr hscan
  | tok tok =>
    obtain ⟨_, htiEq, _, _, hkLtJ, hjSz, ⟨tr0, hscan0, _⟩, huniq0⟩ := lexAtPureSpec_tok hsp
    dsimp only [Syntax.leafOf] at hlf
    rw [StateT.run'_eq] at hlf
    rcases except_eq_err_or_ok
        ((Code.parse (T := Unit) Engine.builder (cs.extract tok.i tok.j) .lexical cx tok.i cs 0 n []).run
          { steps := Code.budget (tok.j - tok.i) }) with ⟨err, Hrun⟩ | ⟨⟨resC, stEnd⟩, Hrun⟩
    · rw [Hrun] at hlf; cases hlf
    · rw [Hrun] at hlf
      dsimp only [Except.map, Bind.bind, Except.bind, pure, Except.pure] at hlf
      have hexSz : (cs.extract tok.i tok.j).size = tok.j - tok.i := by
        rw [Array.size_extract, Nat.min_eq_left hjSz]
      cases resC with
      | some nd =>
        injection hlf with hoptEq
        obtain ⟨_, _, dt, hmd, _, _, _⟩ := code_parse_some_spec hok hgLex rfl rfl rfl rfl rfl Hrun
        have ⟨_, _, hder⟩ := derivesWith_to_derives hok hgLex codePrimsMatch_engine
          (condMatch_none (cs.extract tok.i tok.j)) (Nat.zero_le _) hmd
        rw [extract_toList_eq_slice, hexSz, htiEq] at hder
        exact Or.inl ⟨(Lex.skip Engine.builder cs first cx p).1, tok.j,
          (Lex.skip Engine.builder cs first cx p).2, tr0, dt.toTree, hoptEq.symm, hscan0, hder⟩
      | none =>
        injection hlf with hoptEq
        have hno := code_parse_none_spec hok hgLex rfl rfl rfl rfl Hrun
        refine Or.inr ⟨hoptEq.symm, fun a b lt tr t hscan hder => ?_⟩
        obtain ⟨rfl, rfl, rfl⟩ := huniq0 a b lt tr hscan
        rw [← htiEq, ← extract_toList_eq_slice, ← hexSz] at hder
        obtain ⟨dtT, _, hplT⟩ := derives_to_plainDerives (T := Unit) (B := Engine.builder)
          (off := tok.i) (src := cs)
          hok hgLex codePrimsMatch_engine (condMatch_none _) (by simp) hder
        exact hno dtT ((codeAlphaSpec (T := Unit) Engine.builder (cs.extract tok.i tok.j) .lexical cx tok.i cs none).derivesWith_mono_allow
          (fun _ _ _ _ _ => by
            simp only [AlphaSpec.CommitAllow, Code.alpha,
              orderedNts_nil_of_ordered_false hok hordLex, List.contains_nil,
              Bool.and_false, Bool.false_eq_true, ↓reduceIte]) hplT)

/-- Fast syntactic terminal match using `virtualOk` (equated with `SynTerm` via `virtualOk_iff` on valid `Src`s). -/
def SynTermFast (cx : Ctx) (cs : Array Nat) (first : Bool) (vs : List (Nat × Bool))
    (s : Src) (k : Nat) (x : Terminal) (i j : Nat) : Prop :=
  match x with
  | .text str _ =>
    if vsPending vs i then
      str = ";" ∧ virtualOk s k (vsParen vs (i / 2)) = true ∧ j = i + 1
    else
      ∃ a b lt tr,
        ScanTok Ecma.Spec.gl cx Engine.Model.codePrims cs.toList first .InputElementDiv (i / 2) a b lt tr ∧
        noCross vs (i / 2) b = true ∧
        slice cs.toList a b = str.toList.map Char.toNat ∧
        j = 2 * b
  | .cp _ => False

theorem synTermFast_iff_synTerm (hok : parseTablesOk = true) {cx : Ctx} {cs : Array Nat}
    {first : Bool} {vs : List (Nat × Bool)} {n : NT} {s : Src}
    (hs : s ∈ Ecma.Spec.gl.alts cx .syntactic n) {k : Nat} (hk : k < s.alt.rhs.length)
    (x : Terminal) (i j : Nat) :
    SynTermFast cx cs first vs s k x i j ↔
      SynTerm Ecma.Spec.gl cx Engine.Model.codePrims cs.toList first vs s k x i j := by
  unfold SynTermFast SynTerm
  cases x with
  | cp _ => exact Iff.rfl
  | text str _ =>
    by_cases hp : vsPending vs i = true
    · simp only [hp, ↓reduceIte, virtualOk_iff hok hs hk]
    · simp [hp]

/-- Pure span computation of `Syntax.span`. -/
def synSpanOf (cs : Array Nat) (first : Bool) (cx : Ctx) (lo hi : Nat) : Nat × Nat :=
  let (k, _) := Lex.skip Engine.builder cs first cx (lo / 2)
  if hi / 2 > lo / 2 then (k, hi / 2)
  else if k < cs.size then (k, k) else (lo / 2, lo / 2)

/-- Specification of `Syntax.alpha.leafNode` at `(stamp, n, a, b)`. -/
def SynLeafNodeRel (cs : Array Nat) (first : Bool) (cx : Ctx) (vs : List (Nat × Bool))
    (stamp : Nat) (n : NT) (a b : Nat) (nd : Engine.Model.Node) : Prop :=
  vsPending vs a = false ∧
  ∃ a0 b0 lt tr tLex,
    b = 2 * b0 ∧
    noCross vs (a / 2) b0 = true ∧
    ScanTok Ecma.Spec.gl cx Engine.Model.codePrims cs.toList first (lexicalGoalOf n) (a / 2) a0 b0 lt tr ∧
    synSpanOf cs first cx a b = (a0, b0) ∧
    Derives Ecma.Spec.gl cx .lexical (codeAlphabet Engine.Model.codePrims) (slice cs.toList a0 b0) n [] 0 (b0 - a0) tLex ∧
    Ecma.Model.NodeRel Engine.Impl stamp cs.toList (fun i j => (a0 + i, a0 + j)) nd tLex

def synAlphaSpec (hok : parseTablesOk = true) {cs : Array Nat}
    (hcp : ∀ c ∈ cs.toList, c ≤ 0x10FFFF) (first : Bool) (cx : Ctx) (stamp : Nat)
    (vs : List (Nat × Bool)) (hvs : ∀ pb ∈ vs, pb.1 ≤ cs.size) :
    AlphaSpec Engine.builder (Syntax.alpha Engine.builder cs first cx stamp vs) (2 * cs.size + 2) where
  Inv _ := True
  Term := SynTermFast cx cs first vs
  Leaf := SynLeaf Ecma.Spec.gl cx Engine.Model.codePrims cs.toList first vs
  Phrase _ _ _ := False
  Cond _ _ _ := False
  NoLT := SynNoLT Ecma.Spec.gl cx Engine.Model.codePrims cs.toList first vs
  Starts := SynStarts Ecma.Spec.gl cx Engine.Model.codePrims cs.toList first vs
  NegSpan _ _ _ _ := False
  NegAny _ _ := False
  SpanOf := synSpanOf cs first cx
  TextOf lo hi := let (i, j) := synSpanOf cs first cx lo hi; cs.extract i j
  LeafNodeRel := SynLeafNodeRel cs first cx vs
  LeafStamp := some stamp
  inv_mono_memo _ _ _ _ _ _ _ _ := trivial
  inv_tick _ _ _ := trivial
  term_bound s k x i j h := by
    unfold SynTermFast at h
    cases x with
    | cp _ => cases h
    | text str _ =>
      by_cases hp : vsPending vs i = true
      · simp only [hp, ↓reduceIte] at h
        obtain ⟨_, _, rfl⟩ := h
        obtain ⟨heven, pb, hmem, hpEq⟩ := (vsPending_iff vs i).mp hp
        have hle := hvs pb hmem
        omega
      · simp only [hp, Bool.false_eq_true, ↓reduceIte] at h
        obtain ⟨a, b, lt, _, ⟨htr, hab, hbLen, _⟩, _, _, rfl⟩ := h
        have hsk := (trivia_eq_skip hok hcp).mp htr
        have hik := (skip_spec (cx := cx) hok hcp first (i / 2)).1
        rw [hsk] at hik
        have hbSz : b ≤ cs.size := by simpa using hbLen
        omega
  leaf_bound n i j h := by
    obtain ⟨_, a, b, lt, _, _, ⟨htr, hab, hbLen, _⟩, _, _, rfl⟩ := h
    have hsk := (trivia_eq_skip hok hcp).mp htr
    have hik := (skip_spec (cx := cx) hok hcp first (i / 2)).1
    rw [hsk] at hik
    have hbSz : b ≤ cs.size := by simpa using hbLen
    omega
  phrase_bound _ _ _ h := nomatch h
  term_det s k x i j1 j2 h1 h2 := by
    unfold SynTermFast at h1 h2
    cases x with
    | cp _ => cases h1
    | text str _ =>
      by_cases hp : vsPending vs i = true
      · simp only [hp, ↓reduceIte] at h1 h2; omega
      · simp only [hp, Bool.false_eq_true, ↓reduceIte] at h1 h2
        obtain ⟨a1, b1, lt1, tr1, hsc1, _, _, rfl⟩ := h1
        obtain ⟨a2, b2, lt2, tr2, hsc2, _, _, rfl⟩ := h2
        obtain ⟨_, rfl, _⟩ := scanTok_span_unique hok hcp hsc1 hsc2
        rfl
  leaf_det n i j1 j2 h1 h2 := by
    obtain ⟨_, a1, b1, lt1, tr1, _, hsc1, _, _, rfl⟩ := h1
    obtain ⟨_, a2, b2, lt2, tr2, _, hsc2, _, _, rfl⟩ := h2
    obtain ⟨_, rfl, _⟩ := scanTok_span_unique hok hcp hsc1 hsc2
    rfl
  phrase_det _ _ _ _ h := nomatch h
  keepAll_sound lhs n j h := by
    dsimp only [Syntax.alpha] at h ⊢
    unfold forKeep
    by_cases heq : (lhs == .ForStatement && n == .LexicalDeclaration) = true
    · simp [heq] at h
    · simp [heq]
  hit_spec j st _ _ st' hrun := by
    dsimp only [Syntax.alpha] at hrun
    rw [sm_run_modify] at hrun; cases hrun
    exact ⟨trivial, rfl, rfl, rfl, rfl, rfl, rfl⟩
  term_spec s k x i st _ r st' hrun := by
    dsimp only [Syntax.alpha] at hrun
    unfold Syntax.term at hrun
    cases x with
    | cp _ =>
      obtain ⟨rfl, rfl⟩ := sm_pure_ok hrun
      exact ⟨trivial, rfl, rfl, rfl, rfl, rfl, rfl, Or.inr ⟨rfl, fun _ h => h⟩⟩
    | text str b0 =>
      dsimp only [Syntax.pending] at hrun
      by_cases hp : vsPending vs i = true
      · simp only [hp, ↓reduceIte] at hrun
        obtain ⟨hrEq, rfl⟩ := sm_pure_ok hrun
        subst hrEq
        refine ⟨trivial, rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
        by_cases hc : (str == ";" && virtualOk s k (vsParen vs (i / 2))) = true
        · simp only [hc, ↓reduceIte]
          simp only [Bool.and_eq_true, beq_iff_eq] at hc
          exact Or.inl ⟨i + 1, rfl, by simp [SynTermFast, hp, hc.1, hc.2]⟩
        · simp only [hc, Bool.false_eq_true, ↓reduceIte]
          refine Or.inr ⟨trivial, fun j htm => ?_⟩
          simp only [SynTermFast, hp, ↓reduceIte] at htm
          exact hc (Bool.and_eq_true_iff.mpr ⟨beq_iff_eq.mpr htm.1, htm.2.1⟩)
      · have hpF : vsPending vs i = false := Bool.eq_false_iff.mpr hp
        simp only [hpF, Bool.false_eq_true, ↓reduceIte] at hrun
        obtain ⟨lx, s1, hlxRun, hr1⟩ := sm_bind_ok hrun
        have ⟨hm, ha, hrd, hfw, hfi, hfar, r0, hr0Eq, hlex0⟩ := lex_spec hlxRun
        have hsp0 := lexAtPure_ok_spec hok hcp (by decide : isSynLexGoal .InputElementDiv = true) hlex0
        subst hr0Eq
        cases hlx : Syntax.tokOf r0 with
        | eof _ | bad _ | follow _ =>
          rw [hlx] at hr1; dsimp only at hr1
          obtain ⟨rfl, rfl⟩ := sm_pure_ok hr1
          refine ⟨trivial, hm, ha, hrd, hfw, hfi, hfar, Or.inr ⟨rfl, fun j htm => ?_⟩⟩
          simp only [SynTermFast, hpF, Bool.false_eq_true, ↓reduceIte] at htm
          obtain ⟨a, b, lt, tr, hscan, _⟩ := htm
          exact lexAtPureSpec_not_tok hsp0 (fun _ ht => by rw [hlx] at ht; cases ht) a b lt tr hscan
        | tok tok =>
          rw [hlx] at hr1; dsimp only at hr1
          obtain ⟨hrEq, rfl⟩ := sm_pure_ok hr1
          subst hrEq
          have hr0Tok : r0 = .tok tok := tokOf_eq_tok_iff.mp hlx
          subst hr0Tok
          obtain ⟨_, htiEq, _, _, _, _, ⟨tr0, hscan0, _⟩, huniq0⟩ := lexAtPureSpec_tok hsp0
          refine ⟨trivial, hm, ha, hrd, hfw, hfi, hfar, ?_⟩
          by_cases hc : (noCross vs (i / 2) tok.j && Syntax.textIs cs tok str) = true
          · simp only [hc, ↓reduceIte]
            obtain ⟨hnc0, htxt0⟩ := Bool.and_eq_true_iff.mp hc
            unfold Syntax.textIs at htxt0
            rw [extract_toList_eq_slice, htiEq, beq_iff_eq] at htxt0
            refine Or.inl ⟨2 * tok.j, rfl, ?_⟩
            simp only [SynTermFast, hpF, Bool.false_eq_true, ↓reduceIte]
            exact ⟨_, tok.j, _, tr0, hscan0, hnc0, htxt0, rfl⟩
          · simp only [hc, Bool.false_eq_true, ↓reduceIte]
            refine Or.inr ⟨trivial, fun j htm => ?_⟩
            simp only [SynTermFast, hpF, Bool.false_eq_true, ↓reduceIte] at htm
            obtain ⟨a, b, lt, tr, hscan, hnc, htxt, _⟩ := htm
            obtain ⟨rfl, rfl, _⟩ := huniq0 a b lt tr hscan
            exact hc (Bool.and_eq_true_iff.mpr ⟨hnc, by unfold Syntax.textIs; rw [extract_toList_eq_slice, htiEq, htxt]; exact beq_self_eq_true _⟩)
  leaf_spec n i st _ r st' hrun := by
    dsimp only [Syntax.alpha] at hrun
    unfold Syntax.leaf Syntax.pending at hrun
    by_cases hp : vsPending vs i = true
    · simp only [hp, ↓reduceIte] at hrun
      obtain ⟨rfl, rfl⟩ := sm_pure_ok hrun
      exact ⟨trivial, rfl, rfl, rfl, rfl, rfl, rfl,
        Or.inr ⟨rfl, fun _ hl => by unfold SynLeaf at hl; rw [hp] at hl; exact nomatch hl.1⟩⟩
    · have hpF : vsPending vs i = false := Bool.eq_false_iff.mpr hp
      simp only [hpF, Bool.false_eq_true, ↓reduceIte] at hrun
      obtain ⟨_, _, hget, hrun⟩ := sm_bind_ok hrun
      cases hget
      have hfinish : ∀ (rBase : Option Nat) (sEnd : St _),
          sEnd.memo = st.memo → sEnd.active = st.active → sEnd.reads = st.reads →
          sEnd.fwd = st.fwd → sEnd.first = st.first → sEnd.far = st.far →
          (∃ t0, Lex.lexAtPure Engine.builder cs first cx (Syntax.goalOf n) (i / 2) = .ok t0 ∧
            Syntax.leafOf Engine.builder cs cx n t0 = .ok rBase) →
          r = rBase.filter (fun b => noCross vs (i / 2) (b / 2)) →
          st' = sEnd →
          True ∧ st'.memo = st.memo ∧ st'.active = st.active ∧ st'.reads = st.reads ∧
          st'.fwd = st.fwd ∧ st'.first = st.first ∧ st'.far = st.far ∧
          ((∃ j, r = some j ∧ SynLeaf Ecma.Spec.gl cx Engine.Model.codePrims cs.toList first vs n i j) ∨
           (r = none ∧ ∀ j, ¬ SynLeaf Ecma.Spec.gl cx Engine.Model.codePrims cs.toList first vs n i j)) := by
        intro rBase sEnd hm ha hrd hfw hfi hfar ⟨t0, hlex0, hlf0⟩ hrEq hstEq
        subst hstEq; subst hrEq
        refine ⟨trivial, hm, ha, hrd, hfw, hfi, hfar, ?_⟩
        rcases leafOf_spec hok hcp hlex0 hlf0 with ⟨a, b, lt, tr, t, rfl, hscan, hder⟩ | ⟨rfl, hno⟩
        · dsimp only [Option.filter]
          simp only [show (2 * b) / 2 = b from by omega]
          by_cases hnc : noCross vs (i / 2) b = true
          · simp only [hnc, ↓reduceIte]
            exact Or.inl ⟨2 * b, rfl, hpF, a, b, lt, tr, t, hscan, hnc, hder, rfl⟩
          · simp only [hnc, Bool.false_eq_true, ↓reduceIte]
            refine Or.inr ⟨trivial, fun j ⟨_, a', b', lt', tr', _, hscan', hnc', _, _⟩ => ?_⟩
            obtain ⟨_, rfl, _⟩ := scanTok_span_unique hok hcp hscan hscan'
            exact hnc hnc'
        · refine Or.inr ⟨rfl, fun j ⟨_, a', b', lt', tr', t', hscan', _, hder', _⟩ => ?_⟩
          exact hno a' b' lt' tr' t' hscan' hder'
      let compute : SM (Syntax.Memo Engine.builder cs first cx) (Option Nat) := do
        let ⟨t0, ht0⟩ ← Syntax.lexP Engine.builder cs first cx (Syntax.goalOf n) (i / 2)
        match hr : Syntax.leafOf Engine.builder cs cx n t0 with
        | .ok rBase =>
          modify fun st0 => { st0 with leaves := st0.leaves.insert (n.ctorIdx, i / 2) (.leaf n (i / 2) rBase ⟨t0, ht0, hr⟩) }
          return rBase.filter fun b => noCross vs (i / 2) (b / 2)
        | .error e => throw e
      have hcomp : compute.run st = .ok (r, st') →
          True ∧ st'.memo = st.memo ∧ st'.active = st.active ∧ st'.reads = st.reads ∧
          st'.fwd = st.fwd ∧ st'.first = st.first ∧ st'.far = st.far ∧
          ((∃ j, r = some j ∧ SynLeaf Ecma.Spec.gl cx Engine.Model.codePrims cs.toList first vs n i j) ∨
           (r = none ∧ ∀ j, ¬ SynLeaf Ecma.Spec.gl cx Engine.Model.codePrims cs.toList first vs n i j)) := by
        intro hcRun
        dsimp only [compute] at hcRun
        obtain ⟨⟨t0, ht0⟩, s1, hlp, hr1⟩ := sm_bind_ok hcRun
        have ⟨hm1, ha1, hrd1, hfw1, hfi1, hfar1⟩ := lexP_spec hlp
        split at hr1
        · next rBase hlf0 =>
          obtain ⟨_, s2, hmod, hp2⟩ := sm_bind_ok hr1
          rw [sm_run_modify] at hmod; cases hmod
          obtain ⟨rfl, rfl⟩ := sm_pure_ok hp2
          exact hfinish rBase { s1 with leaves := s1.leaves.insert (n.ctorIdx, i / 2) (.leaf n (i / 2) rBase ⟨t0, ht0, hlf0⟩) }
            hm1 ha1 hrd1 hfw1 hfi1 hfar1 ⟨t0, ht0, hlf0⟩ rfl rfl
        · rw [sm_run_throw] at hr1; cases hr1
      rcases hlv : st.leaves[(n.ctorIdx, i / 2)]? with _ | entry
      · rw [hlv] at hrun; exact hcomp hrun
      · rw [hlv] at hrun
        cases entry with
        | tok _ _ _ _ => exact hcomp hrun
        | leaf n' p' rBase hwit =>
          dsimp only at hrun
          by_cases hk : n' = n ∧ p' = i / 2
          · simp only [hk, and_self, ↓reduceIte] at hrun
            obtain ⟨hrEq, hstEq⟩ := sm_pure_ok hrun
            rcases hk with ⟨rfl, rfl⟩
            exact hfinish rBase st rfl rfl rfl rfl rfl rfl hwit hrEq.symm hstEq
          · simp only [hk, ↓reduceIte] at hrun
            exact hcomp hrun
  phrase_spec _ _ _ _ _ _ hrun := by
    dsimp only [Syntax.alpha] at hrun
    obtain ⟨rfl, rfl⟩ := sm_pure_ok hrun
    exact ⟨trivial, rfl, rfl, rfl, rfl, rfl, rfl, Or.inr ⟨rfl, fun _ h => h⟩⟩
  cond_spec _ _ _ _ _ _ _ hrun := by
    dsimp only [Syntax.alpha] at hrun
    obtain ⟨rfl, rfl⟩ := sm_pure_ok hrun
    exact ⟨trivial, rfl, rfl, rfl, rfl, rfl, rfl, by simp⟩
  noLT_spec i st _ r st' hrun := by
    dsimp only [Syntax.alpha] at hrun
    unfold Syntax.noLT Syntax.pending at hrun
    by_cases hp : vsPending vs i = true
    · simp only [hp, ↓reduceIte] at hrun
      obtain ⟨rfl, rfl⟩ := sm_pure_ok hrun
      exact ⟨trivial, rfl, rfl, rfl, rfl, rfl, rfl, ⟨fun _ => Or.inl hp, fun _ => rfl⟩⟩
    · have hpF : vsPending vs i = false := Bool.eq_false_iff.mpr hp
      simp only [hpF, Bool.false_eq_true, ↓reduceIte] at hrun
      obtain ⟨hrEq, rfl⟩ := sm_pure_ok hrun
      subst hrEq
      refine ⟨trivial, rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
      unfold SynNoLT
      rw [hpF]
      have htrSk := (skip_spec (cx := cx) hok hcp first (i / 2)).2.2.2.1
      simp only [Bool.false_eq_true, false_or, Bool.or_eq_true, decide_eq_true_eq,
        Bool.not_eq_true', Array.length_toList]
      constructor
      · intro hcond
        exact ⟨(Lex.skip Engine.builder cs first cx (i / 2)).1,
          (Lex.skip Engine.builder cs first cx (i / 2)).2, htrSk, hcond⟩
      · rintro ⟨k, lt, htr, hcond⟩
        obtain ⟨rfl, rfl⟩ := trivia_unique hok hcp htrSk htr
        exact hcond
  starts_spec q i st _ hwf r st' hrun := by
    dsimp only [Syntax.alpha] at hrun
    induction q generalizing i st r st' with
    | nil =>
      dsimp only [Syntax.starts, SynStarts] at hrun ⊢
      obtain ⟨rfl, rfl⟩ := sm_pure_ok hrun
      exact ⟨trivial, rfl, rfl, rfl, rfl, rfl, rfl, Iff.intro (fun _ => trivial) (fun _ => rfl)⟩
    | cons it rest ih =>
      have hwfRest : (Syntax.alpha Engine.builder cs first cx stamp vs).g = .syntactic →
          lookSeqsOk synLookTermOk [rest] = true := fun hg => by
        have h := hwf hg
        simp only [lookSeqsOk, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true] at h ⊢
        exact h.2
      cases it with
      | noLT =>
        dsimp only [Syntax.starts, Syntax.look, SynStarts] at hrun ⊢
        obtain ⟨b, s1, hnl, hr1⟩ := sm_bind_ok hrun
        have hnlSpec : s1.memo = st.memo ∧ s1.active = st.active ∧ s1.reads = st.reads ∧
            s1.fwd = st.fwd ∧ s1.first = st.first ∧ s1.far = st.far ∧
            (b = true ↔ SynNoLT Ecma.Spec.gl cx Engine.Model.codePrims cs.toList first vs (SynLook vs i)) := by
          unfold Syntax.noLT Syntax.pending at hnl
          rw [vsPending_synLook_false, synLook_div2] at hnl
          simp only [Bool.false_eq_true, ↓reduceIte] at hnl
          obtain ⟨hbEq, rfl⟩ := sm_pure_ok hnl
          subst hbEq
          refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
          unfold SynNoLT
          rw [vsPending_synLook_false, synLook_div2]
          have htrSk := (skip_spec (cx := cx) hok hcp first (i / 2)).2.2.2.1
          simp only [Bool.false_eq_true, false_or, Bool.or_eq_true, decide_eq_true_eq,
            Bool.not_eq_true', Array.length_toList]
          exact ⟨fun hc => ⟨_, _, htrSk, hc⟩,
            fun ⟨k, lt, htr, hc⟩ => let ⟨hk, hl⟩ := trivia_unique hok hcp htrSk htr; hk ▸ hl ▸ hc⟩
        obtain ⟨hm1, ha1, hrd1, hfw1, hfi1, hfar1, hbIff⟩ := hnlSpec
        cases b with
        | true =>
          simp only [↓reduceIte] at hr1
          have ⟨_, hm2, ha2, hrd2, hfw2, hfi2, hfar2, hrIff⟩ := ih i s1 hwfRest r st' hr1
          exact ⟨trivial, hm2.trans hm1, ha2.trans ha1, hrd2.trans hrd1, hfw2.trans hfw1,
            hfi2.trans hfi1, hfar2.trans hfar1,
            Iff.intro (fun hr => ⟨hbIff.mp rfl, hrIff.mp hr⟩) (fun ⟨_, hs⟩ => hrIff.mpr hs)⟩
        | false =>
          simp only [Bool.false_eq_true, ↓reduceIte] at hr1
          obtain ⟨rfl, rfl⟩ := sm_pure_ok hr1
          exact ⟨trivial, hm1, ha1, hrd1, hfw1, hfi1, hfar1,
            Iff.intro (fun h => by cases h) (fun ⟨hnl', _⟩ => absurd (hbIff.mpr hnl') Bool.false_ne_true)⟩
      | t x =>
        cases x with
        | cp _ =>
          dsimp only [Syntax.starts, SynStarts] at hrun ⊢
          obtain ⟨rfl, rfl⟩ := sm_pure_ok hrun
          exact ⟨trivial, rfl, rfl, rfl, rfl, rfl, rfl, by simp⟩
        | text str b0 =>
          dsimp only [Syntax.starts, SynStarts] at hrun ⊢
          unfold Syntax.look at hrun
          simp only [synLook_div2] at hrun ⊢
          obtain ⟨lx, s1, hlxRun, hr1⟩ := sm_bind_ok hrun
          have ⟨hm1, ha1, hrd1, hfw1, hfi1, hfar1, r0, hr0Eq, hlex0⟩ := lex_spec hlxRun
          have hsp0 := lexAtPure_ok_spec hok hcp (by decide : isSynLexGoal .InputElementDiv = true) hlex0
          subst hr0Eq
          cases hlx : Syntax.tokOf r0 with
          | eof _ | bad _ | follow _ =>
            rw [hlx] at hr1; dsimp only at hr1
            obtain ⟨rfl, rfl⟩ := sm_pure_ok hr1
            refine ⟨trivial, hm1, ha1, hrd1, hfw1, hfi1, hfar1, Iff.intro (fun h => by cases h) ?_⟩
            rintro ⟨a, b, lt, tr, hscan, _⟩
            exact absurd hscan (lexAtPureSpec_not_tok hsp0 (fun _ ht => by rw [hlx] at ht; cases ht) a b lt tr)
          | tok tok =>
            rw [hlx] at hr1; dsimp only at hr1
            have hr0Tok : r0 = .tok tok := tokOf_eq_tok_iff.mp hlx
            subst hr0Tok
            obtain ⟨_, htiEq, _, _, _, _, ⟨tr0, hscan0, _⟩, huniq0⟩ := lexAtPureSpec_tok hsp0
            by_cases hc : (noCross vs (i / 2) tok.j && Syntax.textIs cs tok str) = true
            · simp only [hc, ↓reduceIte] at hr1
              obtain ⟨hnc0, htxt0⟩ := Bool.and_eq_true_iff.mp hc
              unfold Syntax.textIs at htxt0
              rw [extract_toList_eq_slice, htiEq, beq_iff_eq] at htxt0
              have ⟨_, hm2, ha2, hrd2, hfw2, hfi2, hfar2, hrIff⟩ := ih (2 * tok.j) s1 hwfRest r st' hr1
              refine ⟨trivial, hm2.trans hm1, ha2.trans ha1, hrd2.trans hrd1, hfw2.trans hfw1,
                hfi2.trans hfi1, hfar2.trans hfar1, ?_⟩
              constructor
              · intro hr
                exact ⟨_, tok.j, _, tr0, hscan0, hnc0, htxt0, hrIff.mp hr⟩
              · rintro ⟨a, b, lt, tr, hscan, _, _, hrest⟩
                obtain ⟨rfl, rfl, _⟩ := huniq0 a b lt tr hscan
                exact hrIff.mpr hrest
            · simp only [hc, Bool.false_eq_true, ↓reduceIte] at hr1
              obtain ⟨rfl, rfl⟩ := sm_pure_ok hr1
              refine ⟨trivial, hm1, ha1, hrd1, hfw1, hfi1, hfar1, Iff.intro (fun h => by cases h) ?_⟩
              rintro ⟨a, b, lt, tr, hscan, hnc, htxt, _⟩
              obtain ⟨rfl, rfl, _⟩ := huniq0 a b lt tr hscan
              exact absurd (Bool.and_eq_true_iff.mpr ⟨hnc, by unfold Syntax.textIs; rw [extract_toList_eq_slice, htiEq, htxt]; exact beq_self_eq_true _⟩) hc
  negSpan_spec _ _ _ _ _ _ _ _ _ hrun := by
    dsimp only [Syntax.alpha] at hrun
    obtain ⟨rfl, rfl⟩ := sm_pure_ok hrun
    exact ⟨trivial, rfl, rfl, rfl, rfl, rfl, rfl, by simp⟩
  negAny_spec _ _ _ _ _ _ _ hrun := by
    dsimp only [Syntax.alpha] at hrun
    obtain ⟨rfl, rfl⟩ := sm_pure_ok hrun
    exact ⟨trivial, rfl, rfl, rfl, rfl, rfl, rfl, by simp⟩
  span_spec lo hi st _ r st' hrun := by
    dsimp only [Syntax.alpha] at hrun
    unfold Syntax.span at hrun
    unfold synSpanOf
    by_cases hgt : hi / 2 > lo / 2
    · simp only [hgt, ↓reduceIte] at hrun ⊢
      obtain ⟨rfl, rfl⟩ := sm_pure_ok hrun
      exact ⟨trivial, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    · simp only [hgt, ↓reduceIte] at hrun ⊢
      obtain ⟨hrEq, rfl⟩ := sm_pure_ok hrun
      exact ⟨trivial, rfl, rfl, rfl, rfl, rfl, rfl, hrEq.symm⟩
  text_spec lo hi st _ r st' hrun := by
    dsimp only [Syntax.alpha] at hrun
    obtain ⟨⟨spI, spJ⟩, s1, hsp, hp⟩ := sm_bind_ok hrun
    have hspEq : (spI, spJ) = synSpanOf cs first cx lo hi ∧ s1 = st := by
      unfold Syntax.span at hsp
      unfold synSpanOf
      by_cases hgt : hi / 2 > lo / 2
      · simp only [hgt, ↓reduceIte] at hsp ⊢
        obtain ⟨heq, rfl⟩ := sm_pure_ok hsp; exact ⟨heq.symm, rfl⟩
      · simp only [hgt, ↓reduceIte] at hsp ⊢
        obtain ⟨heq, rfl⟩ := sm_pure_ok hsp; exact ⟨heq.symm, rfl⟩
    obtain ⟨hspPair, rfl⟩ := hspEq
    obtain ⟨hrEq, rfl⟩ := sm_pure_ok hp
    subst hrEq
    dsimp only
    rcases hspVal : synSpanOf cs first cx lo hi with ⟨i0, j0⟩
    rw [hspVal] at hspPair
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj hspPair
    exact ⟨trivial, rfl, rfl, rfl, rfl, rfl, rfl, view_toArray_eq_extract cs spI spJ⟩
  leafNode_spec stampArg n a b st hstmp _ nd st' hrun := by
    dsimp only [Option.all] at hstmp
    have hstmpEq : stamp = stampArg := beq_iff_eq.mp hstmp
    subst hstmpEq
    dsimp only [Syntax.alpha] at hrun
    obtain ⟨hpF, hr1⟩ := sm_ite_throw_jp hrun
    have hpF' : vsPending vs a = false := Bool.eq_false_iff.mpr hpF
    obtain ⟨lx, s1, hlxRun, hr2⟩ := sm_bind_ok hr1
    have ⟨hm, ha, hrd, hfw, hfi, hfar, r0, hr0Eq, hlex0⟩ := lex_spec hlxRun
    have hsp0 := lexAtPure_ok_spec hok hcp (isSynLexGoal_lexicalGoalOf n) hlex0
    subst hr0Eq
    cases hlx : Syntax.tokOf r0 with
    | eof _ | bad _ | follow _ =>
      rw [hlx] at hr2; dsimp only at hr2; rw [sm_run_throw] at hr2; cases hr2
    | tok tok =>
      rw [hlx] at hr2; dsimp only at hr2
      have hr0Tok : r0 = .tok tok := tokOf_eq_tok_iff.mp hlx
      subst hr0Tok
      obtain ⟨hbChk, hr3⟩ := sm_unless_throw_jp hr2
      simp only [Bool.and_eq_true, beq_iff_eq] at hbChk
      obtain ⟨hbEq, hnc⟩ := hbChk
      subst hbEq
      obtain ⟨_, htiEq, hltEq, ha2Le, hkLtJ, hjSz, ⟨tr0, hscan0, _⟩, _⟩ := lexAtPureSpec_tok hsp0
      rw [StateT.run'_eq] at hr3
      rcases except_eq_err_or_ok
          ((Code.parse (T := Unit) Engine.builder (cs.extract tok.i tok.j) .lexical cx tok.i cs stamp n []).run
            { steps := Code.budget (tok.j - tok.i) }) with ⟨err, Hc⟩ | ⟨⟨resC, sEnd⟩, Hc⟩
      · rw [Hc] at hr3; dsimp only [Functor.map, Except.map] at hr3; rw [sm_run_throw] at hr3; cases hr3
      · rw [Hc] at hr3; dsimp only [Functor.map, Except.map] at hr3
        cases resC with
        | none => rw [sm_run_throw] at hr3; cases hr3
        | some node =>
          obtain ⟨hndEq, rfl⟩ := sm_pure_ok hr3
          subst hndEq
          have hgLex : GrammarId.lexical ∈ codeGrammars := by decide
          obtain ⟨hntN, hargsN, dt, hmd, hdrel, hnrel, _⟩ :=
            code_parse_some_spec hok hgLex rfl rfl rfl rfl rfl Hc
          have hexSz : (cs.extract tok.i tok.j).size = tok.j - tok.i := by
            rw [Array.size_extract, Nat.min_eq_left hjSz]
          have ⟨_, _, hder⟩ := derivesWith_to_derives hok hgLex codePrimsMatch_engine
            (condMatch_none (cs.extract tok.i tok.j)) (Nat.zero_le _) hmd
          rw [extract_toList_eq_slice, hexSz] at hder
          have hspAndSt : Engine.builder.span node = (tok.i, tok.j) ∧ Engine.builder.stamp node = stamp := by
            cases hmd with
            | node _ _ _ _ _ _ =>
              cases hdrel with
              | node _ _ _ hstN hspN _ _ =>
                dsimp only [codeAlphaSpec] at hspN
                rw [hexSz, Nat.add_zero, show tok.i + (tok.j - tok.i) = tok.j from by omega] at hspN
                exact ⟨hspN, hstN⟩
          have hsynSpan : synSpanOf cs first cx a (2 * tok.j) = (tok.i, tok.j) := by
            unfold synSpanOf
            have hgt : (2 * tok.j) / 2 > a / 2 := by omega
            simp only [hgt, ↓reduceIte]
            exact Prod.ext htiEq.symm (by omega)
          rw [htiEq] at hder hnrel hsynSpan hspAndSt
          refine ⟨trivial, hm, ha, hrd, hfw, hfi, hfar, hntN, hargsN,
            hspAndSt.1.trans hsynSpan.symm, hspAndSt.2,
            ⟨hpF', _, tok.j, _, tr0, dt.toTree, hscan0, hnc, hder, rfl⟩,
            ⟨hpF', _, tok.j, _, tr0, dt.toTree, rfl, hnc, hscan0, hsynSpan, hder, hnrel⟩⟩

/-! ### Syntactic height bound on `DTree` built by `Search.build` -/

mutual
def dtreeSynHeight : DTree → Nat
  | .node _ _ _ _ _ _ _ kids => dtreeSynHeightKids kids + 1
  | _ => 1

def dtreeSynHeightKids : List DTree → Nat
  | [] => 0
  | k :: ks => max (if k.isLeaf then 0 else dtreeSynHeight k) (dtreeSynHeightKids ks)
end

private theorem splits_kid_rule_run {N T : Type} {A : Alpha N T} {size D : Nat}
    {child : NT → List Param → Nat → Nat → SM T N}
    {s : Src} {k : Nat} {ps : List Param} {m : NT} {args : List Arg}
    {next : Option Item} {cur : Nat} {ex : Option Exclusion}
    (hem : (altsOf A.cx A.g m).isEmpty = false) :
    ∀ (cands : List Nat) (st1 : St T) (present : List (Nat × SM T (Piece N))) (st2 : St T),
      (splits A (finalEnds A size D) child s k ps (.nt m args) next cur ex cands).run st1 = .ok (present, st2) →
      ∀ h mkP, (h, mkP) ∈ present →
        ∀ s0 pc s1, mkP.run s0 = .ok (pc, s1) →
          ∃ cNd, pc = .kid cNd h cur ∧ (child m (applyArgs ps args) h cur).run s0 = .ok (cNd, s1) := by
  intro cands
  induction cands with
  | nil =>
    intro st1 present st2 hrun
    dsimp only [splits] at hrun
    obtain ⟨rfl, _⟩ := sm_pure_ok hrun
    intro _ _ hm; cases hm
  | cons h0 hs ih =>
    intro st1 present st2 hrun
    dsimp only [splits] at hrun
    have hoe := AlphaSpec.sm_opt_excl A s k ps h0 cur ex _ hrun
    have hstep1 : ∃ skip sMid,
        (if skip = true then splits A (finalEnds A size D) child s k ps (.nt m args) next cur ex hs
         else
           have ps' := applyArgs ps args
           have isRule := !(altsOf A.cx A.g m).isEmpty
           have __do_jp := fun (hit? : Option (SM T (Piece N))) => do
             let rest ← splits A (finalEnds A size D) child s k ps (.nt m args) next cur ex hs
             pure (match hit? with | some mkPiece => (h0, mkPiece) :: rest | none => rest)
           have __do_jp1 := fun (ok : Bool) =>
             have __do_jp2 := fun (cr : Bool) =>
               have ok := ok && A.keep s.rule.lhs m cur && cr
               if ok = true then do
                 let hit? ← pure (some (if isRule = true then return Piece.kid (← child m ps' h0 cur) h0 cur
                                        else return Piece.kid (← A.leafNode m h0 cur) h0 cur))
                 __do_jp hit?
               else do let hit? ← pure none; __do_jp hit?
             match next with
             | some (.onlyIf c) =>
               if ok = true then do let cr ← A.cond c h0 cur; __do_jp2 cr
               else do let cr ← pure true; __do_jp2 cr
             | _ => do let cr ← pure true; __do_jp2 cr
           if isRule = true then do
             let es ← finalEnds A size D m ps' h0
             let ok ← pure (es.mem cur)
             __do_jp1 ok
           else do
             let r ← A.leaf m h0
             let ok ← pure (r == some cur)
             __do_jp1 ok).run sMid = .ok (present, st2) := by
      cases ex with
      | none => exact ⟨false, st1, hoe⟩
      | some _ => obtain ⟨skip, sMid, _, hr⟩ := hoe; exact ⟨skip, sMid, hr⟩
    obtain ⟨skip, sMid, hr1⟩ := hstep1
    cases skip with
    | true =>
      simp only [↓reduceIte] at hr1
      exact ih sMid present st2 hr1
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte, hem, Bool.not_false] at hr1
      obtain ⟨es, sA, _, hr2⟩ := sm_bind_ok hr1
      obtain ⟨ok0, sB, hpOk, hr3⟩ := sm_bind_ok hr2
      obtain ⟨rfl, hsb⟩ := sm_pure_ok hpOk; subst sB
      have hjp2 : ∀ (cr : Bool) (sC : St T),
          (if (es.mem cur && A.keep s.rule.lhs m cur && cr) = true then do
             let hit? ← pure (some (do let c ← child m (applyArgs ps args) h0 cur; pure (Piece.kid c h0 cur)))
             let rest ← splits A (finalEnds A size D) child s k ps (.nt m args) next cur ex hs
             pure (match hit? with | some mkPiece => (h0, mkPiece) :: rest | none => rest)
           else do
             let hit? ← pure none
             let rest ← splits A (finalEnds A size D) child s k ps (.nt m args) next cur ex hs
             pure (match hit? with | some mkPiece => (h0, mkPiece) :: rest | none => rest)).run sC = .ok (present, st2) →
          ∀ h mkP, (h, mkP) ∈ present →
            ∀ s0 pc s1, mkP.run s0 = .ok (pc, s1) →
              ∃ cNd, pc = .kid cNd h cur ∧ (child m (applyArgs ps args) h cur).run s0 = .ok (cNd, s1) := by
        intro cr sC hrC
        by_cases hokC : (es.mem cur && A.keep s.rule.lhs m cur && cr) = true
        · simp only [hokC, ↓reduceIte] at hrC
          obtain ⟨hit?, sD, hpH, hrD⟩ := sm_bind_ok hrC
          obtain ⟨rfl, hsd⟩ := sm_pure_ok hpH; subst sD
          obtain ⟨rest, sE, hspR, hpR⟩ := sm_bind_ok hrD
          obtain ⟨rfl, hse⟩ := sm_pure_ok hpR; subst sE
          intro h mkP hmem s0 pc s1 hmk
          rcases List.mem_cons.mp hmem with heq | htl
          · obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
            obtain ⟨cNd, _, hcRun, hpK⟩ := sm_bind_ok hmk
            obtain ⟨rfl, hsm⟩ := sm_pure_ok hpK; subst hsm
            exact ⟨cNd, rfl, hcRun⟩
          · exact ih sC rest st2 hspR h mkP htl s0 pc s1 hmk
        · simp only [hokC, Bool.false_eq_true, ↓reduceIte] at hrC
          obtain ⟨hit?, sD, hpH, hrD⟩ := sm_bind_ok hrC
          obtain ⟨rfl, hsd⟩ := sm_pure_ok hpH; subst sD
          obtain ⟨rest, sE, hspR, hpR⟩ := sm_bind_ok hrD
          obtain ⟨rfl, hse⟩ := sm_pure_ok hpR; subst sE
          exact ih sC rest st2 hspR
      cases next with
      | none =>
        obtain ⟨cr, sC, hpCr, hrC⟩ := sm_bind_ok hr3
        obtain ⟨rfl, hsc⟩ := sm_pure_ok hpCr; subst sC
        exact hjp2 true sA hrC
      | some nx =>
        cases nx with
        | onlyIf cond =>
          dsimp only at hr3
          by_cases hmem : es.mem cur = true
          · simp only [hmem, ↓reduceIte] at hr3
            obtain ⟨cr, sC, _, hrC⟩ := sm_bind_ok hr3
            exact hjp2 cr sC (by simpa [hmem] using hrC)
          · simp only [hmem, Bool.false_eq_true, ↓reduceIte] at hr3
            obtain ⟨cr, sC, hpCr, hrC⟩ := sm_bind_ok hr3
            obtain ⟨rfl, hsc⟩ := sm_pure_ok hpCr; subst sC
            exact hjp2 true sA (by simpa [hmem] using hrC)
        | _ =>
          obtain ⟨cr, sC, hpCr, hrC⟩ := sm_bind_ok hr3
          obtain ⟨rfl, hsc⟩ := sm_pure_ok hpCr; subst sC
          exact hjp2 true sA hrC

theorem build_dtreeSynHeight {T : Type} {A : Alpha Engine.Model.Node T} {size : Nat}
    (S : AlphaSpec Engine.builder A size)
    (hok : parseTablesOk = true) (hg : A.g = .syntactic ∨ A.g ∈ codeGrammars)
    (D stamp : Nat) (hstmp : S.LeafStamp.all (· == stamp) = true) :
    ∀ (d : Nat) (n : NT) (ps : List Param) (i j : Nat) (st : St T) (nd : Engine.Model.Node) (st' : St T),
      S.BuildInv st →
      (build A Engine.builder size D stamp d n ps i j).run st = .ok (nd, st') →
      ∀ dt, S.ModeDerives true n ps i j dt → dtreeSynHeight dt ≤ d + 1 := by
  intro d
  induction d with
  | zero =>
    intro _ _ _ _ _ _ _ _ hrun
    dsimp only [build] at hrun; rw [sm_run_throw] at hrun; cases hrun
  | succ d0 ih =>
    intro n ps i j st nd st' hb hrun dt hdt
    have hchild : S.ChildSpec stamp (build A Engine.builder size D stamp d0) :=
      fun m ps' h c st0 nd0 st0' hb0 hcRun =>
        S.build_spec hok builderSpec_engine hg D stamp hstmp d0 m ps' h c st0 nd0 st0' hb0 hcRun
    have ⟨_, _, _, dt0, _, _, huniq⟩ :=
      S.build_spec hok builderSpec_engine hg D stamp hstmp (d0 + 1) n ps i j st nd st' hb hrun
    have hdtEq := huniq dt hdt
    subst hdtEq
    -- Unpack `build (d0 + 1)` -> `buildStep` -> `pick` -> `buildRhs`:
    change (buildStep A Engine.builder size D stamp (build A Engine.builder size D stamp d0) n ps i j).run st = .ok (nd, st') at hrun
    unfold buildStep at hrun
    by_cases hem : (altsOf A.cx A.g n).isEmpty = true
    · have hrun' := AlphaSpec.sm_ite_true hrun hem
      rw [sm_run_throw] at hrun'; cases hrun'
    · have hemf : (altsOf A.cx A.g n).isEmpty = false := Bool.eq_false_iff.mpr hem
      have hr1 := AlphaSpec.sm_ite_false hrun hemf
      obtain ⟨found, st1, hpickRun, hr2⟩ := sm_bind_ok hr1
      rcases found with _ | ⟨e, fw⟩
      · rw [sm_run_throw] at hr2; cases hr2
      · have ⟨hb1, heMem, heAllow, heGrd, hjMem, hfsv, hopv, _⟩ :=
          S.pick_spec hok hg D n ps i j st e fw st1 hb hpickRun
        obtain ⟨rTriple, st2, hrhsRun, hr3⟩ := sm_bind_ok hr2
        rcases rTriple with ⟨cur, pieces, mask⟩
        have ⟨_, hcurInI, _, ts_built, hswBuilt, _⟩ :=
          S.buildRhs_spec hok hg D stamp hchild n e ps j hstmp 0 e.alt.rhs (.single i) fw.sets fw.last fw.prov
            st1 cur pieces mask st2 hb1 (fun it hit => itemWF_of_mem A hok hg heMem hit)
            hfsv hopv hjMem hrhsRun
        rw [Ends.mem_single] at hcurInI
        have hr4 := AlphaSpec.sm_ite_true hr3 hcurInI
        rw [beq_iff_eq] at hcurInI; subst cur
        -- Prove by induction on `is` that `buildRhs` produces `ts` with `dtreeSynHeightKids ts ≤ d0 + 1`:
        have hrhsH : ∀ (k : Nat) (is : List Item) (P : Ends) (sets : List Ends) (last : Ends)
            (provs : Option (List (Std.HashMap Nat (List Nat))))
            (s0 : St T) (c0 : Nat) (pcs0 : List (Piece Engine.Model.Node)) (m0 : List Bool) (s1 : St T),
            S.BuildInv s0 →
            (∀ it ∈ is, ItemWF A it) →
            S.FwdSetsValid (S.SpanOfAllow (S.CommitAllow true)) e ps k is P sets last →
            S.OptProvValid (S.SpanOfAllow (S.CommitAllow true)) e ps k is sets provs →
            last.mem j = true →
            (buildRhs A (finalEnds A size D) (build A Engine.builder size D stamp d0) n e ps j k is sets provs).run s0 =
              .ok ((c0, pcs0, m0), s1) →
            ∀ ts0, S.SeqWith (S.CommitAllow true) e ps k is c0 j m0 ts0 →
              dtreeSynHeightKids ts0 ≤ d0 + 1 := by
          intro k is
          induction is generalizing k with
          | nil =>
            intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ts0 hsw0
            cases hsw0; exact Nat.zero_le _
          | cons it rest ihR =>
            intro P sets last provs s0 c0 pcs0 m0 s1 hb0 hwf0 hfsv0 hopv0 hlast0 hrun0 ts0 hsw0
            have ⟨_, hcurP0, _, _, _, _⟩ :=
              S.buildRhs_spec hok hg D stamp hchild n e ps j hstmp k (it :: rest) P sets last provs
                s0 c0 pcs0 m0 s1 hb0 hwf0 hfsv0 hopv0 hlast0 hrun0
            cases sets with
            | nil => cases hfsv0
            | cons before restSets =>
              cases hfsv0 with
              | cons P' _ hP' hfsvRest =>
                dsimp only [buildRhs] at hrun0
                obtain ⟨restProvs, hpspec, hrA⟩ := AlphaSpec.sm_uncons_provs_ex provs _ hrun0
                have hopvRest : S.OptProvValid (S.SpanOfAllow (S.CommitAllow true)) e ps (k + 1) rest restSets restProvs := by
                  cases provs with
                  | none => dsimp only [AlphaSpec.ProvsStepSpec] at hpspec; subst hpspec; trivial
                  | some pms =>
                    cases pms with
                    | nil => exact False.elim hpspec
                    | cons _ _ =>
                      dsimp only [AlphaSpec.ProvsStepSpec] at hpspec; subst hpspec
                      cases hopv0 with | cons _ hpms => exact hpms
                obtain ⟨rTrip1, sMid, hrecRun, hrB⟩ := sm_bind_ok hrA
                rcases rTrip1 with ⟨cur1, pieces1, mask1⟩
                have ⟨hbMid, _, _, ts1, hsw1, huniq1⟩ :=
                  S.buildRhs_spec hok hg D stamp hchild n e ps j hstmp (k + 1) rest P' restSets last restProvs
                    s0 cur1 pieces1 mask1 sMid hb0 (fun it' h => hwf0 it' (List.mem_cons_of_mem _ h))
                    hfsvRest hopvRest hlast0 hrecRun
                have hts1H : dtreeSynHeightKids ts1 ≤ d0 + 1 :=
                  ihR (k + 1) P' restSets last restProvs s0 cur1 pieces1 mask1 sMid hb0
                    (fun it' h => hwf0 it' (List.mem_cons_of_mem _ h)) hfsvRest hopvRest hlast0 hrecRun ts1 hsw1
                match hsw0 with
                | .absent hswR =>
                  obtain ⟨_, _, htsEq⟩ := huniq1 c0 _ _ ((hP' c0).mpr ⟨c0, hcurP0, Or.inl ⟨rfl, rfl⟩⟩) hswR
                  exact htsEq ▸ hts1H
                | .look hlk hswR =>
                  obtain ⟨_, _, htsEq⟩ := huniq1 c0 _ _ ((hP' c0).mpr ⟨c0, hcurP0, rfl, hlk⟩) hswR
                  exact htsEq ▸ hts1H
                | .noLT hnl hswR =>
                  obtain ⟨_, _, htsEq⟩ := huniq1 c0 _ _ ((hP' c0).mpr ⟨c0, hcurP0, rfl, hnl⟩) hswR
                  exact htsEq ▸ hts1H
                | .empty hswR =>
                  obtain ⟨_, _, htsEq⟩ := huniq1 c0 _ _ ((hP' c0).mpr ⟨c0, hcurP0, rfl⟩) hswR
                  exact htsEq ▸ hts1H
                | .onlyIf hswR =>
                  obtain ⟨_, _, htsEq⟩ := huniq1 c0 _ _ ((hP' c0).mpr ⟨c0, hcurP0, rfl⟩) hswR
                  exact htsEq ▸ hts1H
                | .term (h := mid) ht hswR =>
                  obtain ⟨hmidEq, _, htsEq⟩ := huniq1 mid _ _ ((hP' mid).mpr ⟨c0, hcurP0, Or.inr ht⟩) hswR
                  subst hmidEq; subst htsEq
                  rw [dtreeSynHeightKids]
                  exact Nat.max_le.mpr ⟨Nat.zero_le _, hts1H⟩
                | .butNotT (h := mid) ht hex hswR =>
                  obtain ⟨hmidEq, _, htsEq⟩ := huniq1 mid _ _ ((hP' mid).mpr ⟨c0, hcurP0, ht, hex⟩) hswR
                  subst hmidEq; subst htsEq
                  rw [dtreeSynHeightKids]
                  exact Nat.max_le.mpr ⟨Nat.zero_le _, hts1H⟩
                | .phrase (h := mid) hph hswR =>
                  obtain ⟨hmidEq, _, htsEq⟩ := huniq1 mid _ _ ((hP' mid).mpr ⟨c0, hcurP0, hph⟩) hswR
                  subst hmidEq; subst htsEq
                  rw [dtreeSynHeightKids]
                  exact Nat.max_le.mpr ⟨Nat.zero_le _, hts1H⟩
                | .leaf (n := m) (args := args) (o := o) (h := mid) hemM hl hk hch hswR =>
                  have hmStep : S.ItemMatch (S.SpanOfAllow (S.CommitAllow true)) e k ps (.sym (.nt m args) o) rest.head? c0 mid :=
                    ⟨hk, (S.condOpt_head rest c0 mid).mpr hch, by simp [hemM, hl]⟩
                  obtain ⟨hmidEq, _, htsEq⟩ := huniq1 mid _ _ ((hP' mid).mpr ⟨c0, hcurP0, Or.inr hmStep⟩) hswR
                  subst hmidEq; subst htsEq
                  rw [dtreeSynHeightKids]
                  exact Nat.max_le.mpr ⟨Nat.succ_le_succ (Nat.zero_le _), hts1H⟩
                | .butNotLeaf (n := m) (args := args) (ex := ex) (h := mid) hemM hl hk hex hswR =>
                  have hmStep : S.ItemMatch (S.SpanOfAllow (S.CommitAllow true)) e k ps (.butNot (.nt m args) ex) none c0 mid :=
                    ⟨hk, hex, by simp [hemM, hl]⟩
                  obtain ⟨hmidEq, _, htsEq⟩ := huniq1 mid _ _ ((hP' mid).mpr ⟨c0, hcurP0, hmStep⟩) hswR
                  subst hmidEq; subst htsEq
                  rw [dtreeSynHeightKids]
                  exact Nat.max_le.mpr ⟨Nat.succ_le_succ (Nat.zero_le _), hts1H⟩
                | .nt (n := m) (args := args) (o := o) (h := mid) (t := tC) hemM hdC hk hch hswR =>
                  have hmStep : S.ItemMatch (S.SpanOfAllow (S.CommitAllow true)) e k ps (.sym (.nt m args) o) rest.head? c0 mid :=
                    ⟨hk, (S.condOpt_head rest c0 mid).mpr hch, by simp only [hemM, Bool.not_false, ↓reduceIte]; exact ⟨_, hdC⟩⟩
                  obtain ⟨hmidEq, _, htsEq⟩ := huniq1 mid _ _ ((hP' mid).mpr ⟨c0, hcurP0, Or.inr hmStep⟩) hswR
                  subst hmidEq; subst htsEq
                  dsimp only at hrB
                  obtain ⟨present, s2, hspRun, hrC⟩ := sm_bind_ok hrB
                  have ⟨hb2, _, _⟩ :=
                    S.splits_spec hok hg D stamp hchild e k ps (.nt m args) o rest.head? mid none trivial hstmp
                      (AlphaSpec.candsOf provs before mid) sMid present s2 hbMid hspRun
                  obtain ⟨_, hrD⟩ := sm_ite_throw_jp hrC
                  cases habs : (o && before.mem mid) with
                  | true =>
                    have hrD' := AlphaSpec.sm_ite_true hrD habs
                    obtain ⟨hpEq, _⟩ := sm_pure_ok hrD'
                    obtain ⟨_, hpEq2⟩ := Prod.mk.inj hpEq.symm
                    obtain ⟨_, hmEq⟩ := Prod.mk.inj hpEq2
                    have hoT : o = true := (Bool.and_eq_true_iff.mp habs).1
                    subst hoT; cases hmEq
                  | false =>
                    have hrD' := AlphaSpec.sm_ite_false hrD habs
                    cases hprL : present with
                    | nil => rw [hprL] at hrD'; dsimp only [List.head?] at hrD'; rw [sm_run_throw] at hrD'; cases hrD'
                    | cons hdPr tlPr =>
                      rcases hdPr with ⟨hSplit, mkP⟩
                      rw [hprL] at hrD'; dsimp only [List.head?] at hrD'
                      obtain ⟨pc, s3, hmkRun, hrE⟩ := sm_bind_ok hrD'
                      obtain ⟨hpEq, _⟩ := sm_pure_ok hrE
                      obtain ⟨hhEq, _⟩ := Prod.mk.inj hpEq.symm
                      subst hhEq
                      obtain ⟨cNd, _, hcRun⟩ := splits_kid_rule_run hemM (AlphaSpec.candsOf provs before mid) sMid _ s2 hspRun c0 mkP
                        (hprL ▸ List.mem_cons_self ..) s2 pc s3 hmkRun
                      have hcH := ih m (applyArgs ps args) c0 mid s2 cNd s3 hb2 hcRun tC hdC
                      have hisL : tC.isLeaf = false := by cases hdC; rfl
                      rw [dtreeSynHeightKids, hisL]
                      exact Nat.max_le.mpr ⟨hcH, hts1H⟩
                | .butNotN (n := m) (args := args) (ex := ex) (h := mid) (t := tC) hemM hdC hk hex hswR =>
                  have hmStep : S.ItemMatch (S.SpanOfAllow (S.CommitAllow true)) e k ps (.butNot (.nt m args) ex) none c0 mid :=
                    ⟨hk, hex, by simp only [hemM, Bool.not_false, ↓reduceIte]; exact ⟨_, hdC⟩⟩
                  obtain ⟨hmidEq, _, htsEq⟩ := huniq1 mid _ _ ((hP' mid).mpr ⟨c0, hcurP0, hmStep⟩) hswR
                  subst hmidEq; subst htsEq
                  dsimp only at hrB
                  obtain ⟨present, s2, hspRun, hrC⟩ := sm_bind_ok hrB
                  have ⟨hb2, _, _⟩ :=
                    S.splits_spec hok hg D stamp hchild e k ps (.nt m args) false none mid (some ex)
                      ⟨(hwf0 _ (List.mem_cons_self ..)), rfl⟩ hstmp (AlphaSpec.candsOf provs before mid) sMid present s2 hbMid hspRun
                  obtain ⟨_, hrD⟩ := sm_ite_throw_jp hrC
                  cases hprL : present with
                  | nil => rw [hprL] at hrD; dsimp only [List.head?] at hrD; rw [sm_run_throw] at hrD; cases hrD
                  | cons hdPr tlPr =>
                    rcases hdPr with ⟨hSplit, mkP⟩
                    rw [hprL] at hrD; dsimp only [List.head?] at hrD
                    obtain ⟨pc, s3, hmkRun, hrE⟩ := sm_bind_ok hrD
                    obtain ⟨hpEq, _⟩ := sm_pure_ok hrE
                    obtain ⟨hhEq, _⟩ := Prod.mk.inj hpEq.symm
                    subst hhEq
                    obtain ⟨cNd, _, hcRun⟩ := splits_kid_rule_run hemM (AlphaSpec.candsOf provs before mid) sMid _ s2 hspRun c0 mkP
                      (hprL ▸ List.mem_cons_self ..) s2 pc s3 hmkRun
                    have hcH := ih m (applyArgs ps args) c0 mid s2 cNd s3 hb2 hcRun tC hdC
                    have hisL : tC.isLeaf = false := by cases hdC; rfl
                    rw [dtreeSynHeightKids, hisL]
                    exact Nat.max_le.mpr ⟨hcH, hts1H⟩
        rcases opt_none_or_some (prodIdOf e mask) with hnone | ⟨pId, hpid⟩
        · rw [hnone, sm_run_throw] at hr4; cases hr4
        · have hmdBuilt : S.ModeDerives true n ps i j (.node n pId e ps i j mask ts_built) :=
            .node e heMem heAllow heGrd hpid hswBuilt
          have hdt0Eq := huniq _ hmdBuilt
          rw [← hdt0Eq, dtreeSynHeight]
          have hkidsH := hrhsH 0 e.alt.rhs (.single i) fw.sets fw.last fw.prov st1 i pieces mask st2
            hb1 (fun it hit => itemWF_of_mem A hok hg heMem hit) hfsv hopv hjMem hrhsRun ts_built hswBuilt
          omega

/-! ## Section 3: Equivalence with `SynDerives` / `SynHit`, `Syntax.insertion`, and `ValidASI` -/

private theorem synTerm_bound (hok : parseTablesOk = true) {cx : Ctx} {cs : Array Nat}
    (hcp : ∀ c ∈ cs.toList, c ≤ 0x10FFFF) {first : Bool} {vs : List (Nat × Bool)}
    (hvs : ∀ pb ∈ vs, pb.1 ≤ cs.size)
    {s : Src} {k : Nat} {x : Terminal} {i j : Nat}
    (h : SynTerm Ecma.Spec.gl cx Engine.Model.codePrims cs.toList first vs s k x i j) :
    i < j ∧ j ≤ 2 * cs.size + 1 := by
  unfold SynTerm at h
  cases x with
  | cp _ => cases h
  | text str _ =>
    by_cases hp : vsPending vs i = true
    · simp only [hp, ↓reduceIte] at h
      obtain ⟨_, _, rfl⟩ := h
      obtain ⟨heven, pb, hmem, hpEq⟩ := (vsPending_iff vs i).mp hp
      have := hvs pb hmem
      omega
    · simp only [hp, Bool.false_eq_true, ↓reduceIte] at h
      obtain ⟨a, b, lt, _, ⟨htr, hab, hbLen, _⟩, _, _, rfl⟩ := h
      have hsk := (trivia_eq_skip hok hcp).mp htr
      have hik := (skip_spec (cx := cx) hok hcp first (i / 2)).1
      rw [hsk] at hik
      have hbSz : b ≤ cs.size := by simpa using hbLen
      omega

private theorem synLeaf_bound (hok : parseTablesOk = true) {cx : Ctx} {cs : Array Nat}
    (hcp : ∀ c ∈ cs.toList, c ≤ 0x10FFFF) {first : Bool} {vs : List (Nat × Bool)}
    {n : NT} {i j : Nat}
    (h : SynLeaf Ecma.Spec.gl cx Engine.Model.codePrims cs.toList first vs n i j) :
    i < j ∧ j ≤ 2 * cs.size := by
  obtain ⟨_, a, b, lt, _, _, ⟨htr, hab, hbLen, _⟩, _, _, rfl⟩ := h
  have hsk := (trivia_eq_skip hok hcp).mp htr
  have hik := (skip_spec (cx := cx) hok hcp first (i / 2)).1
  rw [hsk] at hik
  have hbSz : b ≤ cs.size := by simpa using hbLen
  omega

mutual
private theorem synDerives_bound (hok : parseTablesOk = true) {cx : Ctx} {cs : Array Nat}
    (hcp : ∀ c ∈ cs.toList, c ≤ 0x10FFFF) {first : Bool} {vs : List (Nat × Bool)}
    (hvs : ∀ pb ∈ vs, pb.1 ≤ cs.size)
    {n : NT} {ps : List Param} {i j : Nat}
    (hd : SynDerives Ecma.Spec.gl cx Engine.Model.codePrims cs.toList first vs n ps i j) :
    i ≤ j ∧ (i ≤ 2 * cs.size + 1 → j ≤ 2 * cs.size + 1) :=
  match hd with
  | .node _ _ _ hseq => synSeq_bound hok hcp hvs hseq

private theorem synSeq_bound (hok : parseTablesOk = true) {cx : Ctx} {cs : Array Nat}
    (hcp : ∀ c ∈ cs.toList, c ≤ 0x10FFFF) {first : Bool} {vs : List (Nat × Bool)}
    (hvs : ∀ pb ∈ vs, pb.1 ≤ cs.size)
    {s : Src} {ps : List Param} {k : Nat} {is : List Item} {i j : Nat}
    (hseq : SynSeq Ecma.Spec.gl cx Engine.Model.codePrims cs.toList first vs s ps k is i j) :
    i ≤ j ∧ (i ≤ 2 * cs.size + 1 → j ≤ 2 * cs.size + 1) :=
  match hseq with
  | .nil => ⟨Nat.le_refl _, id⟩
  | .absent hr | .look _ hr | .noLT _ hr | .empty hr | .onlyIf hr => synSeq_bound hok hcp hvs hr
  | .term ht hr | .butNotT ht _ hr =>
    let ⟨h1, h2⟩ := synTerm_bound hok hcp hvs ht
    let ⟨r1, r2⟩ := synSeq_bound hok hcp hvs hr
    ⟨by omega, fun _ => r2 h2⟩
  | .leaf _ hl _ _ hr | .butNotLeaf _ hl _ hr =>
    let ⟨h1, h2⟩ := synLeaf_bound hok hcp hl
    let ⟨r1, r2⟩ := synSeq_bound hok hcp hvs hr
    ⟨by omega, fun _ => r2 (by omega)⟩
  | .nt _ hd _ _ hr | .butNotN _ hd _ hr =>
    let ⟨h1, h2⟩ := synDerives_bound hok hcp hvs hd
    let ⟨r1, r2⟩ := synSeq_bound hok hcp hvs hr
    ⟨by omega, fun hi => r2 (h2 hi)⟩
end

mutual
private theorem synOpen_bound (hok : parseTablesOk = true) {cx : Ctx} {cs : Array Nat}
    (hcp : ∀ c ∈ cs.toList, c ≤ 0x10FFFF) {first : Bool} {vs : List (Nat × Bool)}
    (hvs : ∀ pb ∈ vs, pb.1 ≤ cs.size) {goal : NT} {goalPs : List Param}
    {n : NT} {ps : List Param} {i : Nat}
    (ho : SynOpen Ecma.Spec.gl cx Engine.Model.codePrims cs.toList first vs goal goalPs n ps i) :
    i ≤ 2 * cs.size + 1 :=
  match ho with
  | .root => Nat.zero_le _
  | .nt hp _ => synPrefix_bound hok hcp hvs hp
  | .butNotN hp _ => synPrefix_bound hok hcp hvs hp

private theorem synPrefix_bound (hok : parseTablesOk = true) {cx : Ctx} {cs : Array Nat}
    (hcp : ∀ c ∈ cs.toList, c ≤ 0x10FFFF) {first : Bool} {vs : List (Nat × Bool)}
    (hvs : ∀ pb ∈ vs, pb.1 ≤ cs.size) {goal : NT} {goalPs : List Param}
    {s : Src} {ps : List Param} {k : Nat} {is : List Item} {i : Nat}
    (hp : SynPrefix Ecma.Spec.gl cx Engine.Model.codePrims cs.toList first vs goal goalPs s ps k is i) :
    i ≤ 2 * cs.size + 1 :=
  match hp with
  | .enter _ ho _ _ => synOpen_bound hok hcp hvs ho
  | .absent hp0 | .look hp0 _ | .noLT hp0 _ | .empty hp0 | .onlyIf hp0 => synPrefix_bound hok hcp hvs hp0
  | .term _ ht | .butNotT _ ht _ => (synTerm_bound hok hcp hvs ht).2
  | .leaf _ _ hl _ _ | .butNotLeaf _ _ hl _ => Nat.le_trans (synLeaf_bound hok hcp hl).2 (by omega)
  | .nt hp0 _ hd _ _ | .butNotN hp0 _ hd _ =>
    (synDerives_bound hok hcp hvs hd).2 (synPrefix_bound hok hcp hvs hp0)
end

theorem synHit_bound (hok : parseTablesOk = true) {cx : Ctx} {cs : Array Nat}
    (hcp : ∀ c ∈ cs.toList, c ≤ 0x10FFFF) {first : Bool} {vs : List (Nat × Bool)}
    (hvs : ∀ pb ∈ vs, pb.1 ≤ cs.size) {goal : NT} {goalPs : List Param} {h : Nat}
    (hh : SynHit Ecma.Spec.gl cx Engine.Model.codePrims cs.toList first vs goal goalPs h) :
    h ≤ 2 * cs.size + 1 := by
  cases hh with
  | zero => exact Nat.zero_le _
  | term _ ht | butNotT _ ht _ => exact (synTerm_bound hok hcp hvs ht).2
  | leaf _ _ hl _ _ | butNotLeaf _ _ hl _ => exact Nat.le_trans (synLeaf_bound hok hcp hl).2 (by omega)
  | nt hp _ hd _ _ | butNotN hp _ hd _ =>
    exact (synDerives_bound hok hcp hvs hd).2 (synPrefix_bound hok hcp hvs hp)

theorem validASI_props (hok : parseTablesOk = true) {cx : Ctx} {cs : Array Nat}
    (hcp : ∀ c ∈ cs.toList, c ≤ 0x10FFFF) {first : Bool} {goal : NT} {ps : List Param}
    {vs : List (Nat × Bool)}
    (hv : ValidASI Ecma.Spec.gl cx Engine.Model.codePrims cs.toList first goal ps vs) :
    (∀ pb ∈ vs, pb.1 ≤ cs.size) ∧
    (∀ p b1 b2, (p, b1) ∈ vs → (p, b2) ∈ vs → b1 = b2) := by
  induction hv with
  | nil => exact ⟨(fun _ h => nomatch h), (fun _ _ _ h => nomatch h)⟩
  | @step vs0 p paren _ hnext ih =>
    obtain ⟨hvs0, huniq0⟩ := ih
    obtain ⟨_, f, hhit, _, hfEven, rfl, hnotIn, _⟩ := hnext
    have hfBound := synHit_bound hok hcp hvs0 hhit
    have hpBound : f / 2 ≤ cs.size := by omega
    refine ⟨fun pb hmem => ?_, fun q b1 b2 hm1 hm2 => ?_⟩
    · rcases List.mem_append.mp hmem with hm0 | hsing
      · exact hvs0 pb hm0
      · rw [List.mem_singleton] at hsing; subst hsing; exact hpBound
    · have hnotMem : ∀ b, (f / 2, b) ∉ vs0 := by
        intro b hm
        have := List.all_eq_true.mp hnotIn (f / 2, b) hm
        simp at this
      rcases List.mem_append.mp hm1 with h1 | h1 <;> rcases List.mem_append.mp hm2 with h2 | h2
      · exact huniq0 q b1 b2 h1 h2
      · rw [List.mem_singleton] at h2; obtain ⟨rfl, rfl⟩ := Prod.mk.inj h2; exact absurd h1 (hnotMem b1)
      · rw [List.mem_singleton] at h1; obtain ⟨rfl, rfl⟩ := Prod.mk.inj h1; exact absurd h2 (hnotMem b2)
      · rw [List.mem_singleton] at h1 h2
        exact (Prod.mk.inj h1).2.trans (Prod.mk.inj h2).2.symm

private theorem synExcl_iff (hok : parseTablesOk = true) {cs : Array Nat}
    (hcp : ∀ c ∈ cs.toList, c ≤ 0x10FFFF) {first : Bool} {cx : Ctx} {stamp : Nat}
    {vs : List (Nat × Bool)} (hvs : ∀ pb ∈ vs, pb.1 ≤ cs.size)
    {n : NT} {s : Src} (hs : s ∈ Ecma.Spec.gl.alts cx .syntactic n)
    {k : Nat} (hk : k < s.alt.rhs.length) {base : Sym} {ex : Exclusion}
    (hokIt : synItemOk cx (.butNot base ex) = true) (ps : List Param) (i h : Nat) :
    (synAlphaSpec hok hcp first cx stamp vs hvs).ExclHolds s k ps i h ex ↔
      SynExcluded Ecma.Spec.gl cx Engine.Model.codePrims cs.toList first vs s k i h ex := by
  dsimp only [synItemOk] at hokIt
  simp only [Bool.and_eq_true] at hokIt
  have hsym : ∀ y : Sym,
      (match y with | .t _ => true | .nt m _ => (glData.alts cx .syntactic m).isEmpty) = true →
      ((synAlphaSpec hok hcp first cx stamp vs hvs).SymHolds s k ps i h y ↔
        SynSymEx Ecma.Spec.gl cx Engine.Model.codePrims cs.toList first vs s k i h y) := by
    intro y hyOk
    cases y with
    | t x =>
      dsimp only [AlphaSpec.SymHolds, synAlphaSpec, SynSymEx]
      exact synTermFast_iff_synTerm hok hs hk x i h
    | nt m args =>
      dsimp only [AlphaSpec.SymHolds, synAlphaSpec, Syntax.alpha, SynSymEx]
      have hem : (altsOf cx .syntactic m).isEmpty = true := by rw [altsOf_eq hok, ← glData_eq]; exact hyOk
      have hnil : Ecma.Spec.gl.alts cx .syntactic m = [] := List.isEmpty_iff.mp (glData_eq ▸ hyOk)
      simp [hem, hnil]
  cases ex with
  | sym y => exact hsym y hokIt.2
  | oneOf ys _ =>
    dsimp only [AlphaSpec.ExclHolds, SynExcluded]
    exact ⟨fun ⟨y, hy, hsy⟩ => ⟨y, hy, (hsym y (List.all_eq_true.mp hokIt.2 y hy)).mp hsy⟩,
      fun ⟨y, hy, hsy⟩ => ⟨y, hy, (hsym y (List.all_eq_true.mp hokIt.2 y hy)).mpr hsy⟩⟩

private theorem synLook_iff (hok : parseTablesOk = true) {cs : Array Nat}
    (hcp : ∀ c ∈ cs.toList, c ≤ 0x10FFFF) {first : Bool} {cx : Ctx} {stamp : Nat}
    {vs : List (Nat × Bool)} (hvs : ∀ pb ∈ vs, pb.1 ≤ cs.size)
    {l : Lookahead} (hokIt : synItemOk cx (.lookahead l) = true) (i : Nat) :
    (synAlphaSpec hok hcp first cx stamp vs hvs).LookHolds l i ↔
      SynLookOk Ecma.Spec.gl cx Engine.Model.codePrims cs.toList first vs l i := by
  cases l with
  | eq _ | ne _ | mem _ | notMem _ => rfl
  | notMemNT _ => cases hokIt

private theorem noCondAfter_of_synItems {cx : Ctx} {rest : List Item}
    (h : ∀ it ∈ rest, synItemOk cx it = true) :
    noCondAfter rest = true ∧ condAfter rest = none := by
  cases rest with
  | nil => exact ⟨rfl, rfl⟩
  | cons hd _ =>
    have hhd := h hd (List.mem_cons_self ..)
    cases hd with
    | onlyIf _ => cases hhd
    | _ => exact ⟨rfl, rfl⟩

mutual
theorem plainDerives_to_synDerives (hok : parseTablesOk = true) {cs : Array Nat}
    (hcp : ∀ c ∈ cs.toList, c ≤ 0x10FFFF) {first : Bool} {cx : Ctx} {stamp : Nat}
    {vs : List (Nat × Bool)} (hvs : ∀ pb ∈ vs, pb.1 ≤ cs.size)
    {n : NT} {ps : List Param} {i j : Nat} {dt : DTree}
    (hd : (synAlphaSpec hok hcp first cx stamp vs hvs).PlainDerives n ps i j dt) :
    SynDerives Ecma.Spec.gl cx Engine.Model.codePrims cs.toList first vs n ps i j :=
  match hd with
  | .node s hsMem _ hgrd _ hsw => by
    have hsSpec : s ∈ Ecma.Spec.gl.alts cx .syntactic n := (altsOf_eq hok cx .syntactic n) ▸ hsMem
    exact .node s hsSpec hgrd (seqWith_to_synSeq hok hcp hvs hsSpec (Nat.zero_le _) rfl hsw)
termination_by (sizeOf dt, 0)

theorem seqWith_to_synSeq (hok : parseTablesOk = true) {cs : Array Nat}
    (hcp : ∀ c ∈ cs.toList, c ≤ 0x10FFFF) {first : Bool} {cx : Ctx} {stamp : Nat}
    {vs : List (Nat × Bool)} (hvs : ∀ pb ∈ vs, pb.1 ≤ cs.size)
    {n : NT} {s : Src} (hs : s ∈ Ecma.Spec.gl.alts cx .syntactic n)
    {k : Nat} {is : List Item} {i j : Nat} {m : List Bool} {ts : List DTree}
    (hk : k ≤ s.alt.rhs.length) (his : s.alt.rhs.drop k = is)
    (hsw : (synAlphaSpec hok hcp first cx stamp vs hvs).SeqWith (fun _ _ _ _ => True) s ps k is i j m ts) :
    SynSeq Ecma.Spec.gl cx Engine.Model.codePrims cs.toList first vs s ps k is i j := by
  have hallOk : ∀ it ∈ is, synItemOk cx it = true := fun it hit =>
    synItemOk_of_mem hok hs (List.mem_of_mem_drop (his ▸ hit))
  have hkLt : ∀ it rest, is = it :: rest → k < s.alt.rhs.length ∧ s.alt.rhs.drop (k + 1) = rest := by
    intro it rest heq
    have hdrop : s.alt.rhs.drop k = it :: rest := his.trans heq
    have hlen : 0 < (s.alt.rhs.drop k).length := by rw [hdrop]; simp
    rw [List.length_drop] at hlen
    refine ⟨by omega, ?_⟩
    rw [← List.tail_drop, hdrop]; rfl
  cases hsw with
  | nil => exact .nil
  | absent hr =>
    obtain ⟨hlt, hdr⟩ := hkLt _ _ rfl
    exact .absent (seqWith_to_synSeq hok hcp hvs hs (Nat.succ_le_of_lt hlt) hdr hr)
  | term ht hr =>
    obtain ⟨hlt, hdr⟩ := hkLt _ _ rfl
    exact .term ((synTermFast_iff_synTerm hok hs hlt _ _ _).mp ht)
      (seqWith_to_synSeq hok hcp hvs hs (Nat.succ_le_of_lt hlt) hdr hr)
  | nt hem hd hkKeep _ hr =>
    obtain ⟨hlt, hdr⟩ := hkLt _ _ rfl
    dsimp only [Syntax.alpha] at hem
    rw [altsOf_eq hok] at hem
    have hne : Ecma.Spec.gl.alts cx .syntactic _ ≠ [] := fun hnil => by rw [hnil] at hem; cases hem
    have ⟨hnc, _⟩ := noCondAfter_of_synItems (fun x hx => hallOk x (List.mem_cons_of_mem _ hx))
    exact .nt hne (plainDerives_to_synDerives hok hcp hvs hd) hkKeep hnc
      (seqWith_to_synSeq hok hcp hvs hs (Nat.succ_le_of_lt hlt) hdr hr)
  | leaf hem hl hkKeep _ hr =>
    obtain ⟨hlt, hdr⟩ := hkLt _ _ rfl
    dsimp only [Syntax.alpha] at hem
    rw [altsOf_eq hok, List.isEmpty_iff] at hem
    have ⟨hnc, _⟩ := noCondAfter_of_synItems (fun x hx => hallOk x (List.mem_cons_of_mem _ hx))
    exact .leaf hem hl hkKeep hnc (seqWith_to_synSeq hok hcp hvs hs (Nat.succ_le_of_lt hlt) hdr hr)
  | butNotT ht hex hr =>
    obtain ⟨hlt, hdr⟩ := hkLt _ _ rfl
    have hitOk := hallOk _ (List.mem_cons_self ..)
    exact .butNotT ((synTermFast_iff_synTerm hok hs hlt _ _ _).mp ht)
      (fun hx => hex ((synExcl_iff hok hcp hvs hs hlt hitOk ps i _).mpr hx))
      (seqWith_to_synSeq hok hcp hvs hs (Nat.succ_le_of_lt hlt) hdr hr)
  | butNotN hem hd _ hex hr =>
    obtain ⟨hlt, hdr⟩ := hkLt _ _ rfl
    have hitOk := hallOk _ (List.mem_cons_self ..)
    dsimp only [Syntax.alpha] at hem
    rw [altsOf_eq hok] at hem
    have hne : Ecma.Spec.gl.alts cx .syntactic _ ≠ [] := fun hnil => by rw [hnil] at hem; cases hem
    exact .butNotN hne (plainDerives_to_synDerives hok hcp hvs hd)
      (fun hx => hex ((synExcl_iff hok hcp hvs hs hlt hitOk ps i _).mpr hx))
      (seqWith_to_synSeq hok hcp hvs hs (Nat.succ_le_of_lt hlt) hdr hr)
  | butNotLeaf hem hl _ hex hr =>
    obtain ⟨hlt, hdr⟩ := hkLt _ _ rfl
    have hitOk := hallOk _ (List.mem_cons_self ..)
    dsimp only [Syntax.alpha] at hem
    rw [altsOf_eq hok, List.isEmpty_iff] at hem
    exact .butNotLeaf hem hl
      (fun hx => hex ((synExcl_iff hok hcp hvs hs hlt hitOk ps i _).mpr hx))
      (seqWith_to_synSeq hok hcp hvs hs (Nat.succ_le_of_lt hlt) hdr hr)
  | phrase hp _ => exact nomatch hp
  | look hlk hr =>
    obtain ⟨hlt, hdr⟩ := hkLt _ _ rfl
    have hitOk := hallOk _ (List.mem_cons_self ..)
    exact .look ((synLook_iff hok hcp hvs hitOk i).mp hlk)
      (seqWith_to_synSeq hok hcp hvs hs (Nat.succ_le_of_lt hlt) hdr hr)
  | noLT hnl hr =>
    obtain ⟨hlt, hdr⟩ := hkLt _ _ rfl
    exact .noLT hnl (seqWith_to_synSeq hok hcp hvs hs (Nat.succ_le_of_lt hlt) hdr hr)
  | empty hr =>
    obtain ⟨hlt, hdr⟩ := hkLt _ _ rfl
    exact .empty (seqWith_to_synSeq hok hcp hvs hs (Nat.succ_le_of_lt hlt) hdr hr)
  | onlyIf hr =>
    obtain ⟨hlt, hdr⟩ := hkLt _ _ rfl
    exact .onlyIf (seqWith_to_synSeq hok hcp hvs hs (Nat.succ_le_of_lt hlt) hdr hr)
termination_by (sizeOf ts, is.length)
end

private theorem altsOf_isEmpty_false_of_ne {cx : Ctx} {m : NT} (hok : parseTablesOk = true)
    (hne : Ecma.Spec.gl.alts cx .syntactic m ≠ []) :
    (altsOf cx .syntactic m).isEmpty = false := by
  rw [altsOf_eq hok]
  cases h : Ecma.Spec.gl.alts cx .syntactic m with
  | nil => exact absurd h hne
  | cons _ _ => rfl

private theorem altsOf_isEmpty_true_of_eq {cx : Ctx} {m : NT} (hok : parseTablesOk = true)
    (hnil : Ecma.Spec.gl.alts cx .syntactic m = []) :
    (altsOf cx .syntactic m).isEmpty = true := by
  rw [altsOf_eq hok, hnil]; rfl

mutual
theorem synDerives_to_plainDerives (hok : parseTablesOk = true) {cs : Array Nat}
    (hcp : ∀ c ∈ cs.toList, c ≤ 0x10FFFF) {first : Bool} {cx : Ctx} {stamp : Nat}
    {vs : List (Nat × Bool)} (hvs : ∀ pb ∈ vs, pb.1 ≤ cs.size)
    {n : NT} {ps : List Param} {i j : Nat}
    (hd : SynDerives Ecma.Spec.gl cx Engine.Model.codePrims cs.toList first vs n ps i j) :
    ∃ dt, (synAlphaSpec hok hcp first cx stamp vs hvs).PlainDerives n ps i j dt :=
  match hd with
  | .node s hs hgrd hseq => by
    let S := synAlphaSpec hok hcp first cx stamp vs hvs
    obtain ⟨m, ts, hsw⟩ := synSeq_to_seqWith (stamp := stamp) hok hcp hvs hs (Nat.zero_le _) rfl hseq
    obtain ⟨_, hopts⟩ := alt_lhs_and_opts hok hs
    have hm : m ∈ masks s.alt.opts := hopts ▸ S.seqWith_masks hsw
    obtain ⟨hpeq, id, _, hid, _⟩ := prodIdOf_spec hok hs hm
    have hsMem : s ∈ altsOf cx .syntactic n := (altsOf_eq hok cx .syntactic n).symm ▸ hs
    exact ⟨.node n id s ps i j m ts, .node s hsMem trivial hgrd (hpeq.trans hid) hsw⟩

theorem synSeq_to_seqWith (hok : parseTablesOk = true) {cs : Array Nat}
    (hcp : ∀ c ∈ cs.toList, c ≤ 0x10FFFF) {first : Bool} {cx : Ctx} {stamp : Nat}
    {vs : List (Nat × Bool)} (hvs : ∀ pb ∈ vs, pb.1 ≤ cs.size)
    {n : NT} {s : Src} (hs : s ∈ Ecma.Spec.gl.alts cx .syntactic n)
    {k : Nat} {is : List Item} {ps : List Param} {i j : Nat}
    (hk : k ≤ s.alt.rhs.length) (his : s.alt.rhs.drop k = is)
    (hseq : SynSeq Ecma.Spec.gl cx Engine.Model.codePrims cs.toList first vs s ps k is i j) :
    ∃ m ts, (synAlphaSpec hok hcp first cx stamp vs hvs).SeqWith (fun _ _ _ _ => True) s ps k is i j m ts := by
  let S := synAlphaSpec hok hcp first cx stamp vs hvs
  have hallOk : ∀ it ∈ is, synItemOk cx it = true := fun it hit =>
    synItemOk_of_mem hok hs (List.mem_of_mem_drop (his ▸ hit))
  have hkLt : ∀ it rest, is = it :: rest → k < s.alt.rhs.length ∧ s.alt.rhs.drop (k + 1) = rest := by
    intro it rest heq
    have hdrop : s.alt.rhs.drop k = it :: rest := his.trans heq
    have hlen : 0 < (s.alt.rhs.drop k).length := by rw [hdrop]; simp
    rw [List.length_drop] at hlen
    exact ⟨by omega, by rw [← List.tail_drop, hdrop]; rfl⟩
  match hseq with
  | .nil => exact ⟨[], [], .nil⟩
  | .absent hr =>
    obtain ⟨hlt, hdr⟩ := hkLt _ _ rfl
    obtain ⟨m, ts, hsw⟩ := synSeq_to_seqWith hok hcp hvs hs (Nat.succ_le_of_lt hlt) hdr hr
    exact ⟨false :: m, ts, .absent hsw⟩
  | .term ht hr =>
    obtain ⟨hlt, hdr⟩ := hkLt _ _ rfl
    obtain ⟨m, ts, hsw⟩ := synSeq_to_seqWith hok hcp hvs hs (Nat.succ_le_of_lt hlt) hdr hr
    exact ⟨_, _, .term ((synTermFast_iff_synTerm hok hs hlt _ _ _).mpr ht) hsw⟩
  | .nt (is := is0) (h := h0) hne hd hkKeep _ hr =>
    obtain ⟨hlt, hdr⟩ := hkLt _ _ rfl
    obtain ⟨dt0, hd0⟩ := synDerives_to_plainDerives (stamp := stamp) hok hcp hvs hd
    obtain ⟨m, ts, hsw⟩ := synSeq_to_seqWith hok hcp hvs hs (Nat.succ_le_of_lt hlt) hdr hr
    have hem := altsOf_isEmpty_false_of_ne hok hne
    have ⟨_, hca⟩ := noCondAfter_of_synItems (fun x hx => hallOk x (List.mem_cons_of_mem _ hx))
    have hch : S.CondHolds is0 i h0 := by unfold AlphaSpec.CondHolds; rw [hca]; trivial
    exact ⟨_, _, .nt hem hd0 hkKeep hch hsw⟩
  | .leaf (is := is0) (h := h0) hnil hl hkKeep _ hr =>
    obtain ⟨hlt, hdr⟩ := hkLt _ _ rfl
    obtain ⟨m, ts, hsw⟩ := synSeq_to_seqWith hok hcp hvs hs (Nat.succ_le_of_lt hlt) hdr hr
    have hem := altsOf_isEmpty_true_of_eq hok hnil
    have ⟨_, hca⟩ := noCondAfter_of_synItems (fun x hx => hallOk x (List.mem_cons_of_mem _ hx))
    have hch : S.CondHolds is0 i h0 := by unfold AlphaSpec.CondHolds; rw [hca]; trivial
    exact ⟨_, _, .leaf hem hl hkKeep hch hsw⟩
  | .butNotT ht hex hr =>
    obtain ⟨hlt, hdr⟩ := hkLt _ _ rfl
    have hitOk := hallOk _ (List.mem_cons_self ..)
    obtain ⟨m, ts, hsw⟩ := synSeq_to_seqWith hok hcp hvs hs (Nat.succ_le_of_lt hlt) hdr hr
    exact ⟨m, _, .butNotT ((synTermFast_iff_synTerm hok hs hlt _ _ _).mpr ht)
      (fun hx => hex ((synExcl_iff hok hcp hvs hs hlt hitOk ps i _).mp hx)) hsw⟩
  | .butNotN hne _ _ _ =>
    have hitOk := hallOk _ (List.mem_cons_self ..)
    dsimp only [synItemOk] at hitOk
    simp only [Bool.and_eq_true, List.isEmpty_iff, glData_eq] at hitOk
    exact absurd hitOk.1 hne
  | .butNotLeaf (n := mLeaf) (h := hLeaf) hnil hl hex hr =>
    obtain ⟨hlt, hdr⟩ := hkLt _ _ rfl
    have hitOk := hallOk _ (List.mem_cons_self ..)
    obtain ⟨m, ts, hsw⟩ := synSeq_to_seqWith hok hcp hvs hs (Nat.succ_le_of_lt hlt) hdr hr
    have hem := altsOf_isEmpty_true_of_eq hok hnil
    have hfk : forKeep s.rule.lhs mLeaf hLeaf = true := by
      obtain ⟨_, _, b0, _, _, _, _, _, _, rfl⟩ := hl
      exact forKeep_two_mul _ _ b0
    exact ⟨m, _, .butNotLeaf hem hl hfk
      (fun hx => hex ((synExcl_iff hok hcp hvs hs hlt hitOk ps i _).mp hx)) hsw⟩
  | .look hlk hr =>
    obtain ⟨hlt, hdr⟩ := hkLt _ _ rfl
    have hitOk := hallOk _ (List.mem_cons_self ..)
    obtain ⟨m, ts, hsw⟩ := synSeq_to_seqWith hok hcp hvs hs (Nat.succ_le_of_lt hlt) hdr hr
    exact ⟨m, ts, .look ((synLook_iff hok hcp hvs hitOk i).mpr hlk) hsw⟩
  | .noLT hnl hr =>
    obtain ⟨hlt, hdr⟩ := hkLt _ _ rfl
    obtain ⟨m, ts, hsw⟩ := synSeq_to_seqWith hok hcp hvs hs (Nat.succ_le_of_lt hlt) hdr hr
    exact ⟨m, ts, .noLT hnl hsw⟩
  | .empty hr =>
    obtain ⟨hlt, hdr⟩ := hkLt _ _ rfl
    obtain ⟨m, ts, hsw⟩ := synSeq_to_seqWith hok hcp hvs hs (Nat.succ_le_of_lt hlt) hdr hr
    exact ⟨m, ts, .empty hsw⟩
  | .onlyIf hr =>
    obtain ⟨hlt, hdr⟩ := hkLt _ _ rfl
    obtain ⟨m, ts, hsw⟩ := synSeq_to_seqWith hok hcp hvs hs (Nat.succ_le_of_lt hlt) hdr hr
    exact ⟨m, ts, .onlyIf hsw⟩
end

theorem plainDerives_iff_synDerives (hok : parseTablesOk = true) {cs : Array Nat}
    (hcp : ∀ c ∈ cs.toList, c ≤ 0x10FFFF) {first : Bool} {cx : Ctx} {stamp : Nat}
    {vs : List (Nat × Bool)} (hvs : ∀ pb ∈ vs, pb.1 ≤ cs.size)
    {n : NT} {ps : List Param} {i j : Nat} :
    (∃ dt, (synAlphaSpec hok hcp first cx stamp vs hvs).PlainDerives n ps i j dt) ↔
      SynDerives Ecma.Spec.gl cx Engine.Model.codePrims cs.toList first vs n ps i j :=
  ⟨fun ⟨_, hd⟩ => plainDerives_to_synDerives hok hcp hvs hd,
   synDerives_to_plainDerives hok hcp hvs⟩

private theorem specPrefix_inv (hok : parseTablesOk = true) {cs : Array Nat}
    (hcp : ∀ c ∈ cs.toList, c ≤ 0x10FFFF) {first : Bool} {cx : Ctx} {stamp : Nat}
    {vs : List (Nat × Bool)} (hvs : ∀ pb ∈ vs, pb.1 ≤ cs.size)
    {goal : NT} {goalPs : List Param} {s : Src} {ps : List Param} {k : Nat} {is : List Item} {i : Nat}
    (hp : (synAlphaSpec hok hcp first cx stamp vs hvs).SpecPrefix goal goalPs s ps k is i) :
    ∃ n, s ∈ Ecma.Spec.gl.alts cx .syntactic n ∧ k ≤ s.alt.rhs.length ∧ s.alt.rhs.drop k = is :=
  match hp with
  | .enter (n := n0) s0 _ hs0 _ =>
    ⟨n0, (altsOf_eq hok cx .syntactic n0) ▸ hs0, Nat.zero_le _, rfl⟩
  | .step (s := s0) (k := k0) hp0 _ => by
    obtain ⟨n0, hs0, _, hdr0⟩ := specPrefix_inv hok hcp hvs hp0
    have hlen : 0 < (s0.alt.rhs.drop k0).length := by rw [hdr0]; simp
    rw [List.length_drop] at hlen
    exact ⟨n0, hs0, by omega, by rw [← List.tail_drop, hdr0]; rfl⟩

private theorem synPrefix_inv {cx : Ctx} {cs : Array Nat} {first : Bool} {vs : List (Nat × Bool)}
    {goal : NT} {goalPs : List Param} {s : Src} {ps : List Param} {k : Nat} {is : List Item} {i : Nat}
    (hp : SynPrefix Ecma.Spec.gl cx Engine.Model.codePrims cs.toList first vs goal goalPs s ps k is i) :
    ∃ n, s ∈ Ecma.Spec.gl.alts cx .syntactic n ∧ k ≤ s.alt.rhs.length ∧ s.alt.rhs.drop k = is :=
  match hp with
  | .enter (n := n0) s0 _ hs0 _ => ⟨n0, hs0, Nat.zero_le _, rfl⟩
  | .absent (s := s0) (k := k0) hp0
  | .term (s := s0) (k := k0) hp0 _
  | .nt (s := s0) (k := k0) hp0 _ _ _ _
  | .leaf (s := s0) (k := k0) hp0 _ _ _ _
  | .butNotT (s := s0) (k := k0) hp0 _ _
  | .butNotN (s := s0) (k := k0) hp0 _ _ _
  | .butNotLeaf (s := s0) (k := k0) hp0 _ _ _
  | .look (s := s0) (k := k0) hp0 _
  | .noLT (s := s0) (k := k0) hp0 _
  | .empty (s := s0) (k := k0) hp0
  | .onlyIf (s := s0) (k := k0) hp0 => by
    obtain ⟨n0, hs0, _, hdr0⟩ := synPrefix_inv hp0
    have hlen : 0 < (s0.alt.rhs.drop k0).length := by rw [hdr0]; simp
    rw [List.length_drop] at hlen
    exact ⟨n0, hs0, by omega, by rw [← List.tail_drop, hdr0]; rfl⟩

mutual
private theorem specOpen_to_synOpen (hok : parseTablesOk = true) {cs : Array Nat}
    (hcp : ∀ c ∈ cs.toList, c ≤ 0x10FFFF) {first : Bool} {cx : Ctx} {stamp : Nat}
    {vs : List (Nat × Bool)} (hvs : ∀ pb ∈ vs, pb.1 ≤ cs.size)
    {goal : NT} {goalPs : List Param} {n : NT} {ps : List Param} {i : Nat}
    (ho : (synAlphaSpec hok hcp first cx stamp vs hvs).SpecOpen goal goalPs n ps i) :
    SynOpen Ecma.Spec.gl cx Engine.Model.codePrims cs.toList first vs goal goalPs n ps i :=
  match ho with
  | .root => .root
  | .nt hp hem => by
    dsimp only [Syntax.alpha] at hem
    rw [altsOf_eq hok] at hem
    exact .nt (specPrefix_to_synPrefix hok hcp hvs hp) (fun h => by rw [h] at hem; cases hem)
  | .butNotN hp hem => by
    dsimp only [Syntax.alpha] at hem
    rw [altsOf_eq hok] at hem
    exact .butNotN (specPrefix_to_synPrefix hok hcp hvs hp) (fun h => by rw [h] at hem; cases hem)

private theorem specPrefix_to_synPrefix (hok : parseTablesOk = true) {cs : Array Nat}
    (hcp : ∀ c ∈ cs.toList, c ≤ 0x10FFFF) {first : Bool} {cx : Ctx} {stamp : Nat}
    {vs : List (Nat × Bool)} (hvs : ∀ pb ∈ vs, pb.1 ≤ cs.size)
    {goal : NT} {goalPs : List Param} {s : Src} {ps : List Param} {k : Nat} {is : List Item} {i : Nat}
    (hp : (synAlphaSpec hok hcp first cx stamp vs hvs).SpecPrefix goal goalPs s ps k is i) :
    SynPrefix Ecma.Spec.gl cx Engine.Model.codePrims cs.toList first vs goal goalPs s ps k is i :=
  match hp with
  | .enter s0 ho hs0 hgrd =>
    .enter s0 (specOpen_to_synOpen hok hcp hvs ho) ((altsOf_eq hok cx .syntactic _) ▸ hs0) hgrd
  | .step (s := s0) (ps := ps0) (k := k0) (it := it0) (rest := rest0) (i := i0) (h := h0) hp0 hst => by
    have hpSyn := specPrefix_to_synPrefix hok hcp hvs hp0
    obtain ⟨n0, hs0, _, hdr0⟩ := synPrefix_inv hpSyn
    have hlt0 : k0 < s0.alt.rhs.length := by
      have hlen : 0 < (s0.alt.rhs.drop k0).length := by rw [hdr0]; simp
      rw [List.length_drop] at hlen; omega
    have hallOk : ∀ x ∈ it0 :: rest0, synItemOk cx x = true := fun x hx =>
      synItemOk_of_mem hok hs0 (List.mem_of_mem_drop (hdr0 ▸ hx))
    cases it0 with
    | sym sym0 o =>
      rcases hst with ⟨rfl, rfl⟩ | hm
      · exact .absent hpSyn
      · cases sym0 with
        | t tm => exact .term hpSyn ((synTermFast_iff_synTerm hok hs0 hlt0 _ _ _).mp hm)
        | nt m args =>
          obtain ⟨hkKeep, _, hrM⟩ := hm
          have ⟨hnc, _⟩ := noCondAfter_of_synItems (fun x hx => hallOk x (List.mem_cons_of_mem _ hx))
          cases hem : (altsOf cx .syntactic m).isEmpty with
          | false =>
            simp only [Syntax.alpha, hem, Bool.not_false, ↓reduceIte] at hrM
            obtain ⟨dt0, hd0⟩ := hrM
            rw [altsOf_eq hok] at hem
            exact .nt hpSyn (fun h => by rw [h] at hem; cases hem)
              (plainDerives_to_synDerives hok hcp hvs hd0) hkKeep hnc
          | true =>
            simp only [Syntax.alpha, hem, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hrM
            rw [altsOf_eq hok, List.isEmpty_iff] at hem
            exact .leaf hpSyn hem hrM hkKeep hnc
    | butNot base ex =>
      have hitOk := hallOk _ (List.mem_cons_self ..)
      cases base with
      | t tm =>
        exact .butNotT hpSyn ((synTermFast_iff_synTerm hok hs0 hlt0 _ _ _).mp hst.1)
          (fun hx => hst.2 ((synExcl_iff hok hcp hvs hs0 hlt0 hitOk ps0 i0 h0).mpr hx))
      | nt m args =>
        obtain ⟨_, hex, hrM⟩ := hst
        cases hem : (altsOf cx .syntactic m).isEmpty with
        | false =>
          simp only [Syntax.alpha, hem, Bool.not_false, ↓reduceIte] at hrM
          obtain ⟨dt0, hd0⟩ := hrM
          rw [altsOf_eq hok] at hem
          exact .butNotN hpSyn (fun h => by rw [h] at hem; cases hem)
            (plainDerives_to_synDerives hok hcp hvs hd0)
            (fun hx => hex ((synExcl_iff hok hcp hvs hs0 hlt0 hitOk ps0 i0 h0).mpr hx))
        | true =>
          simp only [Syntax.alpha, hem, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hrM
          rw [altsOf_eq hok, List.isEmpty_iff] at hem
          exact .butNotLeaf hpSyn hem hrM
            (fun hx => hex ((synExcl_iff hok hcp hvs hs0 hlt0 hitOk ps0 i0 h0).mpr hx))
    | phrase _ => exact nomatch hst
    | lookahead l =>
      obtain ⟨rfl, hlk⟩ := hst
      exact .look hpSyn ((synLook_iff hok hcp hvs (hallOk _ (List.mem_cons_self ..)) _).mp hlk)
    | noLT =>
      obtain ⟨rfl, hnl⟩ := hst
      exact .noLT hpSyn hnl
    | empty => subst hst; exact .empty hpSyn
    | onlyIf _ => subst hst; exact .onlyIf hpSyn
end

mutual
private theorem synOpen_to_specOpen (hok : parseTablesOk = true) {cs : Array Nat}
    (hcp : ∀ c ∈ cs.toList, c ≤ 0x10FFFF) {first : Bool} {cx : Ctx} {stamp : Nat}
    {vs : List (Nat × Bool)} (hvs : ∀ pb ∈ vs, pb.1 ≤ cs.size)
    {goal : NT} {goalPs : List Param} {n : NT} {ps : List Param} {i : Nat}
    (ho : SynOpen Ecma.Spec.gl cx Engine.Model.codePrims cs.toList first vs goal goalPs n ps i) :
    (synAlphaSpec hok hcp first cx stamp vs hvs).SpecOpen goal goalPs n ps i :=
  match ho with
  | .root => .root
  | .nt hp hne => .nt (synPrefix_to_specPrefix hok hcp hvs hp) (altsOf_isEmpty_false_of_ne hok hne)
  | .butNotN hp hne => .butNotN (synPrefix_to_specPrefix hok hcp hvs hp) (altsOf_isEmpty_false_of_ne hok hne)

private theorem synPrefix_to_specPrefix (hok : parseTablesOk = true) {cs : Array Nat}
    (hcp : ∀ c ∈ cs.toList, c ≤ 0x10FFFF) {first : Bool} {cx : Ctx} {stamp : Nat}
    {vs : List (Nat × Bool)} (hvs : ∀ pb ∈ vs, pb.1 ≤ cs.size)
    {goal : NT} {goalPs : List Param} {s : Src} {ps : List Param} {k : Nat} {is : List Item} {i : Nat}
    (hp : SynPrefix Ecma.Spec.gl cx Engine.Model.codePrims cs.toList first vs goal goalPs s ps k is i) :
    (synAlphaSpec hok hcp first cx stamp vs hvs).SpecPrefix goal goalPs s ps k is i := by
  let S := synAlphaSpec hok hcp first cx stamp vs hvs
  have hltOf : ∀ {s0 ps0 k0 it0 rest0 i0},
      SynPrefix Ecma.Spec.gl cx Engine.Model.codePrims cs.toList first vs goal goalPs s0 ps0 k0 (it0 :: rest0) i0 →
      (∃ n0, s0 ∈ Ecma.Spec.gl.alts cx .syntactic n0) ∧ k0 < s0.alt.rhs.length ∧
        (∀ x ∈ it0 :: rest0, synItemOk cx x = true) := by
    intro s0 ps0 k0 it0 rest0 i0 hp0
    obtain ⟨n0, hs0, _, hdr0⟩ := synPrefix_inv hp0
    have hlen : 0 < (s0.alt.rhs.drop k0).length := by rw [hdr0]; simp
    rw [List.length_drop] at hlen
    exact ⟨⟨n0, hs0⟩, by omega, fun x hx => synItemOk_of_mem hok hs0 (List.mem_of_mem_drop (hdr0 ▸ hx))⟩
  match hp with
  | .enter s0 ho hs0 hgrd =>
    exact .enter s0 (synOpen_to_specOpen hok hcp hvs ho) ((altsOf_eq hok cx .syntactic _).symm ▸ hs0) hgrd
  | .absent hp0 =>
    exact .step (synPrefix_to_specPrefix hok hcp hvs hp0) (Or.inl ⟨rfl, rfl⟩)
  | .term hp0 ht =>
    obtain ⟨⟨_, hs0⟩, hlt0, _⟩ := hltOf hp0
    exact .step (synPrefix_to_specPrefix hok hcp hvs hp0)
      (Or.inr ((synTermFast_iff_synTerm hok hs0 hlt0 _ _ _).mpr ht))
  | .nt (is := is0) (i := i0) hp0 hne hd hkKeep _ =>
    obtain ⟨_, _, hallOk⟩ := hltOf hp0
    obtain ⟨dt0, hd0⟩ := synDerives_to_plainDerives (stamp := stamp) hok hcp hvs hd
    have hem := altsOf_isEmpty_false_of_ne hok hne
    have ⟨_, hca⟩ := noCondAfter_of_synItems (fun x hx => hallOk x (List.mem_cons_of_mem _ hx))
    have hco : S.CondOpt is0.head? i0 i := by
      refine (S.condOpt_head is0 i0 i).mpr ?_; unfold AlphaSpec.CondHolds; rw [hca]; trivial
    exact .step (synPrefix_to_specPrefix hok hcp hvs hp0)
      (Or.inr ⟨hkKeep, hco, by simp only [Syntax.alpha, hem, Bool.not_false, ↓reduceIte]; exact ⟨dt0, hd0⟩⟩)
  | .leaf (is := is0) (i := i0) hp0 hnil hl hkKeep _ =>
    obtain ⟨_, _, hallOk⟩ := hltOf hp0
    have hem := altsOf_isEmpty_true_of_eq hok hnil
    have ⟨_, hca⟩ := noCondAfter_of_synItems (fun x hx => hallOk x (List.mem_cons_of_mem _ hx))
    have hco : S.CondOpt is0.head? i0 i := by
      refine (S.condOpt_head is0 i0 i).mpr ?_; unfold AlphaSpec.CondHolds; rw [hca]; trivial
    exact .step (synPrefix_to_specPrefix hok hcp hvs hp0)
      (Or.inr ⟨hkKeep, hco, by simp only [Syntax.alpha, hem, Bool.not_true, Bool.false_eq_true, ↓reduceIte]; exact hl⟩)
  | .butNotT hp0 ht hex =>
    obtain ⟨⟨_, hs0⟩, hlt0, hallOk⟩ := hltOf hp0
    have hitOk := hallOk _ (List.mem_cons_self ..)
    exact .step (synPrefix_to_specPrefix hok hcp hvs hp0)
      ⟨(synTermFast_iff_synTerm hok hs0 hlt0 _ _ _).mpr ht,
       fun hx => hex ((synExcl_iff hok hcp hvs hs0 hlt0 hitOk _ _ _).mp hx)⟩
  | .butNotN hp0 hne _ _ =>
    obtain ⟨_, _, hallOk⟩ := hltOf hp0
    have hitOk := hallOk _ (List.mem_cons_self ..)
    dsimp only [synItemOk] at hitOk
    simp only [Bool.and_eq_true, List.isEmpty_iff, glData_eq] at hitOk
    exact absurd hitOk.1 hne
  | .butNotLeaf (n := mL) hp0 hnil hl hex =>
    obtain ⟨⟨_, hs0⟩, hlt0, hallOk⟩ := hltOf hp0
    have hitOk := hallOk _ (List.mem_cons_self ..)
    have hem := altsOf_isEmpty_true_of_eq hok hnil
    have hfk : forKeep s.rule.lhs mL i = true := by
      obtain ⟨_, _, b0, _, _, _, _, _, _, rfl⟩ := hl
      exact forKeep_two_mul _ _ b0
    exact .step (synPrefix_to_specPrefix hok hcp hvs hp0)
      ⟨hfk, fun hx => hex ((synExcl_iff hok hcp hvs hs0 hlt0 hitOk _ _ _).mp hx),
       by simp only [Syntax.alpha, hem, Bool.not_true, Bool.false_eq_true, ↓reduceIte]; exact hl⟩
  | .look hp0 hlk =>
    obtain ⟨_, _, hallOk⟩ := hltOf hp0
    exact .step (synPrefix_to_specPrefix hok hcp hvs hp0)
      ⟨rfl, (synLook_iff hok hcp hvs (hallOk _ (List.mem_cons_self ..)) _).mpr hlk⟩
  | .noLT hp0 hnl =>
    exact .step (synPrefix_to_specPrefix hok hcp hvs hp0) ⟨rfl, hnl⟩
  | .empty hp0 => exact .step (synPrefix_to_specPrefix hok hcp hvs hp0) rfl
  | .onlyIf hp0 => exact .step (synPrefix_to_specPrefix hok hcp hvs hp0) rfl
end

theorem specHit_iff_synHit (hok : parseTablesOk = true) {cs : Array Nat}
    (hcp : ∀ c ∈ cs.toList, c ≤ 0x10FFFF) {first : Bool} {cx : Ctx} {stamp : Nat}
    {vs : List (Nat × Bool)} (hvs : ∀ pb ∈ vs, pb.1 ≤ cs.size)
    {goal : NT} {goalPs : List Param} {h : Nat} :
    (synAlphaSpec hok hcp first cx stamp vs hvs).SpecHit goal goalPs h ↔
      SynHit Ecma.Spec.gl cx Engine.Model.codePrims cs.toList first vs goal goalPs h := by
  let S := synAlphaSpec hok hcp first cx stamp vs hvs
  constructor
  · intro hh
    match hh with
    | .zero => exact .zero
    | .matchAt (s := s0) (ps := ps0) (k := k0) (it := it0) (rest := rest0) (i := i0) hp0 hm0 =>
      have hpSyn := specPrefix_to_synPrefix hok hcp hvs hp0
      obtain ⟨n0, hs0, _, hdr0⟩ := synPrefix_inv hpSyn
      have hlt0 : k0 < s0.alt.rhs.length := by
        have hlen : 0 < (s0.alt.rhs.drop k0).length := by rw [hdr0]; simp
        rw [List.length_drop] at hlen; omega
      have hallOk : ∀ x ∈ it0 :: rest0, synItemOk cx x = true := fun x hx =>
        synItemOk_of_mem hok hs0 (List.mem_of_mem_drop (hdr0 ▸ hx))
      cases it0 with
      | sym sym0 o =>
        cases sym0 with
        | t tm => exact .term hpSyn ((synTermFast_iff_synTerm hok hs0 hlt0 _ _ _).mp hm0)
        | nt m args =>
          obtain ⟨hkKeep, _, hrM⟩ := hm0
          have ⟨hnc, _⟩ := noCondAfter_of_synItems (fun x hx => hallOk x (List.mem_cons_of_mem _ hx))
          cases hem : (altsOf cx .syntactic m).isEmpty with
          | false =>
            simp only [Syntax.alpha, hem, Bool.not_false, ↓reduceIte] at hrM
            obtain ⟨dt0, hd0⟩ := hrM
            rw [altsOf_eq hok] at hem
            exact .nt hpSyn (fun hn => by rw [hn] at hem; cases hem)
              (plainDerives_to_synDerives hok hcp hvs hd0) hkKeep hnc
          | true =>
            simp only [Syntax.alpha, hem, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hrM
            rw [altsOf_eq hok, List.isEmpty_iff] at hem
            exact .leaf hpSyn hem hrM hkKeep hnc
      | butNot base ex =>
        have hitOk := hallOk _ (List.mem_cons_self ..)
        cases base with
        | t tm =>
          exact .butNotT hpSyn ((synTermFast_iff_synTerm hok hs0 hlt0 _ _ _).mp hm0.1)
            (fun hx => hm0.2 ((synExcl_iff hok hcp hvs hs0 hlt0 hitOk ps0 i0 h).mpr hx))
        | nt m args =>
          obtain ⟨_, hex, hrM⟩ := hm0
          cases hem : (altsOf cx .syntactic m).isEmpty with
          | false =>
            simp only [Syntax.alpha, hem, Bool.not_false, ↓reduceIte] at hrM
            obtain ⟨dt0, hd0⟩ := hrM
            rw [altsOf_eq hok] at hem
            exact .butNotN hpSyn (fun hn => by rw [hn] at hem; cases hem)
              (plainDerives_to_synDerives hok hcp hvs hd0)
              (fun hx => hex ((synExcl_iff hok hcp hvs hs0 hlt0 hitOk ps0 i0 h).mpr hx))
          | true =>
            simp only [Syntax.alpha, hem, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hrM
            rw [altsOf_eq hok, List.isEmpty_iff] at hem
            exact .butNotLeaf hpSyn hem hrM
              (fun hx => hex ((synExcl_iff hok hcp hvs hs0 hlt0 hitOk ps0 i0 h).mpr hx))
      | phrase _ => exact nomatch hm0
      | lookahead _ | noLT | empty | onlyIf _ => exact nomatch hm0
  · intro hh
    have hltOf : ∀ {s0 ps0 k0 it0 rest0 i0},
        SynPrefix Ecma.Spec.gl cx Engine.Model.codePrims cs.toList first vs goal goalPs s0 ps0 k0 (it0 :: rest0) i0 →
        (∃ n0, s0 ∈ Ecma.Spec.gl.alts cx .syntactic n0) ∧ k0 < s0.alt.rhs.length ∧
          (∀ x ∈ it0 :: rest0, synItemOk cx x = true) := by
      intro s0 ps0 k0 it0 rest0 i0 hp0
      obtain ⟨n0, hs0, _, hdr0⟩ := synPrefix_inv hp0
      have hlen : 0 < (s0.alt.rhs.drop k0).length := by rw [hdr0]; simp
      rw [List.length_drop] at hlen
      exact ⟨⟨n0, hs0⟩, by omega, fun x hx => synItemOk_of_mem hok hs0 (List.mem_of_mem_drop (hdr0 ▸ hx))⟩
    match hh with
    | .zero => exact .zero
    | .term hp0 ht =>
      obtain ⟨⟨_, hs0⟩, hlt0, _⟩ := hltOf hp0
      exact .matchAt (synPrefix_to_specPrefix hok hcp hvs hp0)
        ((synTermFast_iff_synTerm hok hs0 hlt0 _ _ _).mpr ht)
    | .nt (is := is0) (i := i0) hp0 hne hd hkKeep _ =>
      obtain ⟨_, _, hallOk⟩ := hltOf hp0
      obtain ⟨dt0, hd0⟩ := synDerives_to_plainDerives (stamp := stamp) hok hcp hvs hd
      have hem := altsOf_isEmpty_false_of_ne hok hne
      have ⟨_, hca⟩ := noCondAfter_of_synItems (fun x hx => hallOk x (List.mem_cons_of_mem _ hx))
      have hco : S.CondOpt is0.head? i0 h := by
        refine (S.condOpt_head is0 i0 h).mpr ?_; unfold AlphaSpec.CondHolds; rw [hca]; trivial
      exact .matchAt (synPrefix_to_specPrefix hok hcp hvs hp0)
        ⟨hkKeep, hco, by simp only [Syntax.alpha, hem, Bool.not_false, ↓reduceIte]; exact ⟨dt0, hd0⟩⟩
    | .leaf (is := is0) (i := i0) hp0 hnil hl hkKeep _ =>
      obtain ⟨_, _, hallOk⟩ := hltOf hp0
      have hem := altsOf_isEmpty_true_of_eq hok hnil
      have ⟨_, hca⟩ := noCondAfter_of_synItems (fun x hx => hallOk x (List.mem_cons_of_mem _ hx))
      have hco : S.CondOpt is0.head? i0 h := by
        refine (S.condOpt_head is0 i0 h).mpr ?_; unfold AlphaSpec.CondHolds; rw [hca]; trivial
      exact .matchAt (synPrefix_to_specPrefix hok hcp hvs hp0)
        ⟨hkKeep, hco, by simp only [Syntax.alpha, hem, Bool.not_true, Bool.false_eq_true, ↓reduceIte]; exact hl⟩
    | .butNotT hp0 ht hex =>
      obtain ⟨⟨_, hs0⟩, hlt0, hallOk⟩ := hltOf hp0
      have hitOk := hallOk _ (List.mem_cons_self ..)
      exact .matchAt (synPrefix_to_specPrefix hok hcp hvs hp0)
        ⟨(synTermFast_iff_synTerm hok hs0 hlt0 _ _ _).mpr ht,
         fun hx => hex ((synExcl_iff hok hcp hvs hs0 hlt0 hitOk _ _ _).mp hx)⟩
    | .butNotN hp0 hne _ _ =>
      obtain ⟨_, _, hallOk⟩ := hltOf hp0
      have hitOk := hallOk _ (List.mem_cons_self ..)
      dsimp only [synItemOk] at hitOk
      simp only [Bool.and_eq_true, List.isEmpty_iff, glData_eq] at hitOk
      exact absurd hitOk.1 hne
    | .butNotLeaf (s := sL) (n := mL) hp0 hnil hl hex =>
      obtain ⟨⟨_, hs0⟩, hlt0, hallOk⟩ := hltOf hp0
      have hitOk := hallOk _ (List.mem_cons_self ..)
      have hem := altsOf_isEmpty_true_of_eq hok hnil
      have hfk : forKeep sL.rule.lhs mL h = true := by
        obtain ⟨_, _, b0, _, _, _, _, _, _, rfl⟩ := hl
        exact forKeep_two_mul _ _ b0
      exact .matchAt (synPrefix_to_specPrefix hok hcp hvs hp0)
        ⟨hfk, fun hx => hex ((synExcl_iff hok hcp hvs hs0 hlt0 hitOk _ _ _).mp hx),
         by simp only [Syntax.alpha, hem, Bool.not_true, Bool.false_eq_true, ↓reduceIte]; exact hl⟩

theorem insertion_spec (hok : parseTablesOk = true) {cs : Array Nat}
    (hcp : ∀ c ∈ cs.toList, c ≤ 0x10FFFF) {first : Bool} {cx : Ctx}
    {vs : List (Nat × Bool)} {goal : NT} {ps : List Param} {f : Nat}
    (hnotDone : ¬ SynDone Ecma.Spec.gl cx Engine.Model.codePrims cs.toList first vs goal ps)
    (hhitF : SynHit Ecma.Spec.gl cx Engine.Model.codePrims cs.toList first vs goal ps f)
    (hubF : ∀ h, SynHit Ecma.Spec.gl cx Engine.Model.codePrims cs.toList first vs goal ps h → h ≤ f)
    {st st' : St (Syntax.Memo Engine.builder cs first cx)} {res : Option (Nat × Bool)}
    (hrun : (Syntax.insertion Engine.builder cs first cx vs f).run st = .ok (res, st')) :
    (∀ p paren, res = some (p, paren) ↔
      NextASI Ecma.Spec.gl cx Engine.Model.codePrims cs.toList first vs goal ps p paren) ∧
    (res = none ↔
      ∀ p paren, ¬ NextASI Ecma.Spec.gl cx Engine.Model.codePrims cs.toList first vs goal ps p paren) := by
  have hfUniq : ∀ f',
      SynHit Ecma.Spec.gl cx Engine.Model.codePrims cs.toList first vs goal ps f' →
      (∀ h, SynHit Ecma.Spec.gl cx Engine.Model.codePrims cs.toList first vs goal ps h → h ≤ f') →
      f' = f := fun f' hh' hub' => Nat.le_antisymm (hubF f' hh') (hub' f hhitF)
  unfold Syntax.insertion at hrun
  by_cases hguard : (f % 2 == 1 || !vs.all (fun (q, _) => q != f / 2)) = true
  · simp only [hguard, ↓reduceIte] at hrun
    obtain ⟨rfl, _⟩ := sm_pure_ok hrun
    have hno : ∀ p paren, ¬ NextASI Ecma.Spec.gl cx Engine.Model.codePrims cs.toList first vs goal ps p paren := by
      rintro p paren ⟨_, f', hh', hub', hfEven, hpEq, hall, _⟩
      have hfEq := hfUniq f' hh' hub'; subst f'; subst hpEq
      rw [hfEven, hall] at hguard; cases hguard
    exact ⟨fun p paren => ⟨(fun h => nomatch h), fun hn => absurd hn (hno p paren)⟩,
      ⟨fun _ => hno, fun _ => rfl⟩⟩
  · simp only [hguard, Bool.false_eq_true, ↓reduceIte] at hrun
    simp only [Bool.or_eq_true, beq_iff_eq, Bool.not_eq_true', not_or] at hguard
    have hfEven : f % 2 = 0 := by omega
    have hallVs : vs.all (fun (q, _) => q != f / 2) = true := by
      cases h : vs.all (fun (q, _) => q != f / 2) with
      | true => rfl | false => exact absurd h hguard.2
    obtain ⟨lx, s1, hlxRun, hr1⟩ := sm_bind_ok hrun
    obtain ⟨_, _, _, _, _, _, r0, rfl, hlex0⟩ := lex_spec hlxRun
    have hsp0 := lexAtPure_ok_spec hok hcp (by decide : isSynLexGoal .InputElementDiv = true) hlex0
    cases hlx : Syntax.tokOf r0 with
    | eof lt0 =>
      rw [hlx] at hr1; dsimp only at hr1
      obtain ⟨rfl, _⟩ := sm_pure_ok hr1
      have hr0Eof : r0 = .eof lt0 := tokOf_eq_eof_iff.mp hlx
      subst hr0Eof
      obtain ⟨htrSk, _, hgeSz, hnoScan⟩ := lexAtPureSpec_eof hsp0
      have hnext0 : NextASI Ecma.Spec.gl cx Engine.Model.codePrims cs.toList first vs goal ps (f / 2) false :=
        ⟨hnotDone, f, hhitF, hubF, hfEven, rfl, hallVs,
          Or.inl ⟨_, _, htrSk, by simpa using hgeSz, rfl⟩⟩
      refine ⟨fun p paren => ⟨fun heq => ?_, fun hn => ?_⟩, ⟨(fun h => nomatch h), fun hall => absurd hnext0 (hall _ _)⟩⟩
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj heq).symm; exact hnext0
      · obtain ⟨_, f', hh', hub', _, hpEq, _, hc⟩ := hn
        have hfEq := hfUniq f' hh' hub'; subst f'; subst hpEq
        rcases hc with ⟨_, _, _, _, rfl⟩ | ⟨a, b, lt, tr, hsc, _⟩
        · rfl
        · exact absurd hsc (hnoScan a b lt tr)
    | bad _ | follow _ =>
      rw [hlx] at hr1; dsimp only at hr1
      obtain ⟨rfl, _⟩ := sm_pure_ok hr1
      have hno : ∀ p paren, ¬ NextASI Ecma.Spec.gl cx Engine.Model.codePrims cs.toList first vs goal ps p paren := by
        rintro p paren ⟨_, f', hh', hub', _, hpEq, _, hc⟩
        have hfEq := hfUniq f' hh' hub'; subst f'; subst hpEq
        have hnoScan := lexAtPureSpec_not_tok hsp0 (fun _ ht => by rw [hlx] at ht; cases ht)
        have hkLtSz : (Lex.skip Engine.builder cs first cx (f / 2)).1 < cs.size ∧
            Trivia Ecma.Spec.gl cx Engine.Model.codePrims cs.toList first (f / 2)
              (Lex.skip Engine.builder cs first cx (f / 2)).1
              (Lex.skip Engine.builder cs first cx (f / 2)).2 := by
          cases r0 with
          | eof _ => simp [Syntax.tokOf] at hlx
          | tok _ => simp [Syntax.tokOf] at hlx
          | bad _ => exact ⟨hsp0.2.2.1, hsp0.1⟩
          | follow _ => exact ⟨hsp0.2.2.2.1, hsp0.1⟩
        rcases hc with ⟨k, lt, htr, hge, _⟩ | ⟨a, b, lt, tr, hsc, _⟩
        · obtain ⟨rfl, _⟩ := trivia_unique hok hcp hkLtSz.2 htr
          rw [Array.length_toList] at hge; omega
        · exact hnoScan a b lt tr hsc
      exact ⟨fun p paren => ⟨(fun h => nomatch h), fun hn => absurd hn (hno p paren)⟩,
        ⟨fun _ => hno, fun _ => rfl⟩⟩
    | tok tok =>
      rw [hlx] at hr1; dsimp only at hr1
      have hr0Tok : r0 = .tok tok := tokOf_eq_tok_iff.mp hlx
      subst hr0Tok
      obtain ⟨htrSk, htiEq, hltEq, _, hkLtJ, hjSz, ⟨tr0, hscan0, _⟩, huniq0⟩ := lexAtPureSpec_tok hsp0
      have hnoEof : ∀ k lt, Trivia Ecma.Spec.gl cx Engine.Model.codePrims cs.toList first (f / 2) k lt →
          ¬ (cs.toList.length ≤ k) := by
        intro k lt htr hge
        obtain ⟨rfl, _⟩ := trivia_unique hok hcp htrSk htr
        rw [Array.length_toList] at hge; omega
      by_cases hc1 : (tok.lt || Syntax.textIs cs tok "}") = true
      · simp only [hc1, ↓reduceIte] at hr1
        obtain ⟨rfl, _⟩ := sm_pure_ok hr1
        have hc1' : ((Lex.skip Engine.builder cs first cx (f / 2)).2 ||
            slice cs.toList (Lex.skip Engine.builder cs first cx (f / 2)).1 tok.j == "}".toList.map Char.toNat) = true := by
          have hc1U := hc1
          unfold Syntax.textIs at hc1U
          rwa [extract_toList_eq_slice, htiEq, hltEq] at hc1U
        have hnext0 : NextASI Ecma.Spec.gl cx Engine.Model.codePrims cs.toList first vs goal ps (f / 2) false :=
          ⟨hnotDone, f, hhitF, hubF, hfEven, rfl, hallVs,
            Or.inr ⟨_, tok.j, _, tr0, hscan0, by rw [hc1']; simp⟩⟩
        refine ⟨fun p paren => ⟨fun heq => ?_, fun hn => ?_⟩, ⟨(fun h => nomatch h), fun hall => absurd hnext0 (hall _ _)⟩⟩
        · obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj heq).symm; exact hnext0
        · obtain ⟨_, f', hh', hub', _, hpEq, _, hc⟩ := hn
          have hfEq := hfUniq f' hh' hub'; subst f'; subst hpEq
          rcases hc with ⟨k, lt, htr, hge, _⟩ | ⟨a, b, lt, tr, hsc, hbr⟩
          · exact absurd hge (hnoEof k lt htr)
          · obtain ⟨rfl, rfl, rfl⟩ := huniq0 a b lt tr hsc
            rw [hc1'] at hbr; simp at hbr; subst hbr; rfl
      · simp only [hc1, Bool.false_eq_true, ↓reduceIte] at hr1
        have hc1F : ((Lex.skip Engine.builder cs first cx (f / 2)).2 ||
            slice cs.toList (Lex.skip Engine.builder cs first cx (f / 2)).1 tok.j == "}".toList.map Char.toNat) = false := by
          apply Bool.eq_false_iff.mpr; intro hT
          exact hc1 (by unfold Syntax.textIs; rwa [extract_toList_eq_slice, htiEq, hltEq])
        by_cases hc2 : (decide (0 < f / 2) && (cs[f / 2 - 1]? == some 0x29)) = true
        · simp only [hc2, ↓reduceIte] at hr1
          obtain ⟨rfl, _⟩ := sm_pure_ok hr1
          simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hc2
          have hc2L : cs.toList[f / 2 - 1]? = some 0x29 := by simpa using hc2.2
          have hnext0 : NextASI Ecma.Spec.gl cx Engine.Model.codePrims cs.toList first vs goal ps (f / 2) true :=
            ⟨hnotDone, f, hhitF, hubF, hfEven, rfl, hallVs,
              Or.inr ⟨_, tok.j, _, tr0, hscan0, by rw [hc1F]; exact ⟨hc2.1, hc2L, rfl⟩⟩⟩
          refine ⟨fun p paren => ⟨fun heq => ?_, fun hn => ?_⟩, ⟨(fun h => nomatch h), fun hall => absurd hnext0 (hall _ _)⟩⟩
          · obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj heq).symm; exact hnext0
          · obtain ⟨_, f', hh', hub', _, hpEq, _, hc⟩ := hn
            have hfEq := hfUniq f' hh' hub'; subst f'; subst hpEq
            rcases hc with ⟨k, lt, htr, hge, _⟩ | ⟨a, b, lt, tr, hsc, hbr⟩
            · exact absurd hge (hnoEof k lt htr)
            · obtain ⟨rfl, rfl, rfl⟩ := huniq0 a b lt tr hsc
              rw [hc1F] at hbr; simp only [Bool.false_eq_true, ↓reduceIte] at hbr
              rw [hbr.2.2]
        · simp only [hc2, Bool.false_eq_true, ↓reduceIte] at hr1
          obtain ⟨rfl, _⟩ := sm_pure_ok hr1
          have hno : ∀ p paren, ¬ NextASI Ecma.Spec.gl cx Engine.Model.codePrims cs.toList first vs goal ps p paren := by
            rintro p paren ⟨_, f', hh', hub', _, hpEq, _, hc⟩
            have hfEq := hfUniq f' hh' hub'; subst f'; subst hpEq
            rcases hc with ⟨k, lt, htr, hge, _⟩ | ⟨a, b, lt, tr, hsc, hbr⟩
            · exact hnoEof k lt htr hge
            · obtain ⟨rfl, rfl, rfl⟩ := huniq0 a b lt tr hsc
              rw [hc1F] at hbr; simp only [Bool.false_eq_true, ↓reduceIte] at hbr
              have hc2' : cs[f / 2 - 1]? = some 0x29 := by simpa using hbr.2.1
              exact hc2 (Bool.and_eq_true_iff.mpr ⟨decide_eq_true hbr.1, beq_iff_eq.mpr hc2'⟩)
          exact ⟨fun p paren => ⟨(fun h => nomatch h), fun hn => absurd hn (hno p paren)⟩,
            ⟨fun _ => hno, fun _ => rfl⟩⟩

theorem nextASI_det (hok : parseTablesOk = true) {cx : Ctx} {cs : Array Nat}
    (hcp : ∀ c ∈ cs.toList, c ≤ 0x10FFFF) {first : Bool} {vs : List (Nat × Bool)}
    {goal : NT} {ps : List Param} {p1 p2 : Nat} {b1 b2 : Bool}
    (h1 : NextASI Ecma.Spec.gl cx Engine.Model.codePrims cs.toList first vs goal ps p1 b1)
    (h2 : NextASI Ecma.Spec.gl cx Engine.Model.codePrims cs.toList first vs goal ps p2 b2) :
    p1 = p2 ∧ b1 = b2 := by
  obtain ⟨_, f1, hh1, hub1, _, rfl, _, hc1⟩ := h1
  obtain ⟨_, f2, hh2, hub2, _, rfl, _, hc2⟩ := h2
  have hfEq : f1 = f2 := Nat.le_antisymm (hub2 f1 hh1) (hub1 f2 hh2)
  subst hfEq
  refine ⟨rfl, ?_⟩
  rcases hc1 with ⟨k1, lt1, htr1, hge1, rfl⟩ | ⟨a1, end1, lt1, tr1, hsc1, hbr1⟩ <;>
    rcases hc2 with ⟨k2, lt2, htr2, hge2, rfl⟩ | ⟨a2, end2, lt2, tr2, hsc2, hbr2⟩
  · rfl
  · obtain ⟨rfl, _⟩ := trivia_unique hok hcp htr1 hsc2.1
    have := hsc2.2.1; have := hsc2.2.2.1; omega
  · obtain ⟨rfl, _⟩ := trivia_unique hok hcp htr2 hsc1.1
    have := hsc1.2.1; have := hsc1.2.2.1; omega
  · obtain ⟨rfl, rfl, rfl⟩ := scanTok_span_unique hok hcp hsc1 hsc2
    split at hbr1 <;> rename_i hif
    · simp only [hif, ↓reduceIte] at hbr2; exact hbr1.trans hbr2.symm
    · simp only [hif] at hbr2; exact hbr1.2.2.trans hbr2.2.2.symm

theorem synDone_not_nextASI {cx : Ctx} {P : CodePrims} {src : List Nat} {first : Bool}
    {vs : List (Nat × Bool)} {goal : NT} {ps : List Param}
    (hdone : SynDone Ecma.Spec.gl cx P src first vs goal ps) :
    ∀ p paren, ¬ NextASI Ecma.Spec.gl cx P src first vs goal ps p paren :=
  fun _ _ hn => hn.1 hdone

theorem validASI_prefix_det (hok : parseTablesOk = true) {cx : Ctx} {cs : Array Nat}
    (hcp : ∀ c ∈ cs.toList, c ≤ 0x10FFFF) {first : Bool} {goal : NT} {ps : List Param}
    {vs1 vs2 : List (Nat × Bool)}
    (h1 : ValidASI Ecma.Spec.gl cx Engine.Model.codePrims cs.toList first goal ps vs1)
    (h2 : ValidASI Ecma.Spec.gl cx Engine.Model.codePrims cs.toList first goal ps vs2)
    (hlen : vs1.length ≤ vs2.length) :
    ∃ rem, vs2 = vs1 ++ rem := by
  induction h2 generalizing vs1 with
  | nil =>
    have hnil : vs1 = [] := List.eq_nil_of_length_eq_zero (by simpa using hlen)
    subst hnil; exact ⟨[], rfl⟩
  | @step vs20 p2 b2 h20 hnext2 ih =>
    rw [List.length_append, List.length_singleton] at hlen
    by_cases hle0 : vs1.length ≤ vs20.length
    · obtain ⟨rem0, rfl⟩ := ih h1 hle0
      exact ⟨rem0 ++ [(p2, b2)], by simp [List.append_assoc]⟩
    · cases h1 with
      | nil => simp at hle0
      | @step vs10 p1 b1 h10 hnext1 =>
        rw [List.length_append, List.length_singleton] at hlen hle0
        have heqL : vs10.length = vs20.length := by omega
        obtain ⟨rem0, hEq0⟩ := ih h10 (by omega)
        have hremNil : rem0 = [] := by
          have := congrArg List.length hEq0
          rw [List.length_append] at this
          exact List.eq_nil_of_length_eq_zero (by omega)
        subst hremNil; rw [List.append_nil] at hEq0; subst hEq0
        obtain ⟨rfl, rfl⟩ := nextASI_det hok hcp hnext1 hnext2
        exact ⟨[], by simp⟩

theorem validASI_terminal_max_len (hok : parseTablesOk = true) {cx : Ctx} {cs : Array Nat}
    (hcp : ∀ c ∈ cs.toList, c ≤ 0x10FFFF) {first : Bool} {goal : NT} {ps : List Param}
    {vsA vsB : List (Nat × Bool)}
    (hA : ValidASI Ecma.Spec.gl cx Engine.Model.codePrims cs.toList first goal ps vsA)
    (hterm : ∀ p paren, ¬ NextASI Ecma.Spec.gl cx Engine.Model.codePrims cs.toList first vsA goal ps p paren)
    (hB : ValidASI Ecma.Spec.gl cx Engine.Model.codePrims cs.toList first goal ps vsB) :
    vsB.length ≤ vsA.length := by
  induction hB with
  | nil => exact Nat.zero_le _
  | @step vsB0 pB bB hB0 hnextB ih =>
    rw [List.length_append, List.length_singleton]
    by_cases hlt : vsB0.length < vsA.length
    · omega
    · exfalso
      have heqL : vsB0.length = vsA.length := by omega
      obtain ⟨rem, hEq⟩ := validASI_prefix_det hok hcp hA hB0 (by omega)
      have hremNil : rem = [] := by
        have := congrArg List.length hEq
        rw [List.length_append] at this
        exact List.eq_nil_of_length_eq_zero (by omega)
      subst hremNil; rw [List.append_nil] at hEq; subst hEq
      exact hterm pB bB hnextB

theorem validASI_unique_done (hok : parseTablesOk = true) {cx : Ctx} {cs : Array Nat}
    (hcp : ∀ c ∈ cs.toList, c ≤ 0x10FFFF) {first : Bool} {goal : NT} {ps : List Param}
    {vs1 vs2 : List (Nat × Bool)}
    (h1 : ValidASI Ecma.Spec.gl cx Engine.Model.codePrims cs.toList first goal ps vs1)
    (hd1 : SynDone Ecma.Spec.gl cx Engine.Model.codePrims cs.toList first vs1 goal ps)
    (h2 : ValidASI Ecma.Spec.gl cx Engine.Model.codePrims cs.toList first goal ps vs2)
    (hd2 : SynDone Ecma.Spec.gl cx Engine.Model.codePrims cs.toList first vs2 goal ps) :
    vs1 = vs2 := by
  have hle12 := validASI_terminal_max_len hok hcp h2 (synDone_not_nextASI hd2) h1
  have hle21 := validASI_terminal_max_len hok hcp h1 (synDone_not_nextASI hd1) h2
  obtain ⟨rem, hEq⟩ := validASI_prefix_det hok hcp h1 h2 hle12
  have hremNil : rem = [] := by
    have := congrArg List.length hEq
    rw [List.length_append] at this
    exact List.eq_nil_of_length_eq_zero (by omega)
  subst hremNil; simpa using hEq.symm

theorem validASI_stuck_no_done (hok : parseTablesOk = true) {cx : Ctx} {cs : Array Nat}
    (hcp : ∀ c ∈ cs.toList, c ≤ 0x10FFFF) {first : Bool} {goal : NT} {ps : List Param}
    {vsA vsB : List (Nat × Bool)}
    (hA : ValidASI Ecma.Spec.gl cx Engine.Model.codePrims cs.toList first goal ps vsA)
    (hnotDoneA : ¬ SynDone Ecma.Spec.gl cx Engine.Model.codePrims cs.toList first vsA goal ps)
    (hstuckA : ∀ p paren, ¬ NextASI Ecma.Spec.gl cx Engine.Model.codePrims cs.toList first vsA goal ps p paren)
    (hB : ValidASI Ecma.Spec.gl cx Engine.Model.codePrims cs.toList first goal ps vsB) :
    ¬ SynDone Ecma.Spec.gl cx Engine.Model.codePrims cs.toList first vsB goal ps := by
  intro hdB
  have hleBA := validASI_terminal_max_len hok hcp hA hstuckA hB
  have hleAB := validASI_terminal_max_len hok hcp hB (synDone_not_nextASI hdB) hA
  obtain ⟨rem, hEq⟩ := validASI_prefix_det hok hcp hA hB hleAB
  have hremNil : rem = [] := by
    have := congrArg List.length hEq
    rw [List.length_append] at this
    exact List.eq_nil_of_length_eq_zero (by omega)
  subst hremNil; rw [List.append_nil] at hEq; subst hEq
  exact hnotDoneA hdB


/-! ## Section 4: Token-stream invariant (`TokStreamInv`), `tokBnd` bijection, and `SameSynSkeleton` -/

/-- One real token input element `tokEl` together with its preceding trivia `triv` from `p`. -/
structure TokBlock where
  triv : List Element
  tokEl : Element
  p : Nat
  lt : Bool

def ValidTokBlock (cx : Ctx) (cs : Array Nat) (first : Bool) (blk : TokBlock) : Prop :=
  ChainEls blk.p blk.tokEl.i blk.triv ∧
  (∀ e ∈ blk.triv, ValidTrivEl cx cs first e) ∧
  (blk.triv.any fun e => e.breaks cs.toList) = blk.lt ∧
  Trivia Ecma.Spec.gl cx Engine.Model.codePrims cs.toList first blk.p blk.tokEl.i blk.lt ∧
  blk.tokEl.i < blk.tokEl.j ∧ blk.tokEl.j ≤ cs.size ∧
  blk.tokEl.isToken = true ∧
  ∃ lg, isSynLexGoal lg = true ∧
    blk.tokEl.goal = (if first && blk.tokEl.i == 0 then .InputElementHashbangOrRegExp else lg) ∧
    ScanTok Ecma.Spec.gl cx Engine.Model.codePrims cs.toList first lg blk.p blk.tokEl.i blk.tokEl.j blk.lt blk.tokEl.tree

inductive BlocksChain : Nat → Nat → List TokBlock → Prop where
  | nil (p : Nat) : BlocksChain p p []
  | cons {p m : Nat} (blk : TokBlock) {bs : List TokBlock} :
      blk.p = p → BlocksChain blk.tokEl.j m bs → BlocksChain p m (blk :: bs)

theorem BlocksChain.append {a b c : Nat} {bs1 bs2 : List TokBlock}
    (h1 : BlocksChain a b bs1) (h2 : BlocksChain b c bs2) :
    BlocksChain a c (bs1 ++ bs2) := by
  induction h1 with
  | nil _ => exact h2
  | cons blk hp _ ih => exact .cons blk hp (ih h2)

/-- Unified token-stream invariant shared by soundness and completeness. -/
structure TokStreamInv (cx : Ctx) (cs : Array Nat) (first : Bool) (vs : List (Nat × Bool))
    (els : List Element) (toks : List Token) : Type where
  blocks : List TokBlock
  elsEnd : List Element
  endPos : Nat
  endLt : Bool
  hchain : BlocksChain 0 endPos blocks
  hvalid : ∀ blk ∈ blocks, ValidTokBlock cx cs first blk
  hendChain : ChainEls endPos cs.size elsEnd
  hendValid : ∀ e ∈ elsEnd, ValidTrivEl cx cs first e
  hendTriv : Trivia Ecma.Spec.gl cx Engine.Model.codePrims cs.toList first endPos cs.size endLt
  helsEq : els = (blocks.flatMap fun blk => blk.triv ++ [blk.tokEl]) ++ elsEnd
  htoksFilt : toks.filter (·.virt.isNone) = tokensOf cs.toList els
  htoksAll : toks.all (fun k => k.virt.isNone || !k.lt) = true
  hasi : toksMatchASI els toks vs
  hvsBound : ∀ pb ∈ vs, pb.1 ≤ cs.size
  hvsUniq : ∀ p b1 b2, (p, b1) ∈ vs → (p, b2) ∈ vs → b1 = b2

/-- Exact parser boundary `2 * p + v` corresponding to token index `k` in `(els, toks)`. -/
def tokBnd (els : List Element) (toks : List Token) (k : Nat) : Nat :=
  2 * tokPos els toks k + (if 0 < k && ((toks[k - 1]?).bind Token.virt).isSome then 1 else 0)

private theorem chainEls_le {a b : Nat} {es : List Element}
    (hch : ChainEls a b es) (hpos : ∀ e ∈ es, e.i < e.j) : a ≤ b := by
  induction hch with
  | nil _ => exact Nat.le_refl _
  | cons e hi hj _ ih =>
    have hlt := hpos e (List.mem_cons_self ..)
    have hrest := ih (fun x hx => hpos x (List.mem_cons_of_mem _ hx))
    omega

private theorem chainEls_scans_structure {n : Nat} {els : List Element}
    (hch : ChainEls 0 n els) :
    els.zipIdx.all (fun (e, k) => e.i == (if k == 0 then 0 else (els[k - 1]?.map (·.j)).getD 0)) = true ∧
    (els.getLast?.map (·.j)).getD 0 = n := by
  have hlast : ∀ {a b : Nat} (cur : Element) (rest : List Element),
      cur.j = a → ChainEls a b rest → ((cur :: rest).getLast?.map (·.j)).getD 0 = b := by
    intro a b cur rest hcj hr
    induction hr generalizing cur with
    | nil _ => simpa using hcj
    | cons e1 _ hj1 _ ih =>
      rw [List.getLast?_cons_cons]
      exact ih e1 hj1
  have hzip : ∀ {a b : Nat} {rem : List Element},
      ChainEls a b rem →
      ∀ (pre : List Element),
      (pre ≠ [] → (pre.getLast?.map (·.j)).getD 0 = a) →
      (pre = [] → a = 0) →
      (rem.zipIdx pre.length).all (fun (e, k) =>
        e.i == (if k == 0 then 0 else ((pre ++ rem)[k - 1]?.map (·.j)).getD 0)) = true := by
    intro a b rem hr
    induction hr with
    | nil _ => intro _ _ _; rfl
    | @cons _ m _ e1 r1 hi1 hj1 _ ih =>
      intro pre hpreNe hpreNil
      simp only [List.zipIdx_cons, List.all_cons, Bool.and_eq_true]
      refine ⟨?_, ?_⟩
      · rw [beq_iff_eq]
        cases pre with
        | nil => rw [hi1, hpreNil rfl]; simp
        | cons hd tl0 =>
          simp only [beq_iff_eq, show (hd :: tl0).length ≠ 0 from by simp, ↓reduceIte]
          have hget : ((hd :: tl0) ++ e1 :: r1)[(hd :: tl0).length - 1]? = (hd :: tl0).getLast? := by
            rw [List.getElem?_append_left (by simp)]
            have hl : (hd :: tl0).length - 1 < (hd :: tl0).length := by simp
            rw [List.getElem?_eq_getElem hl, List.getLast?_eq_some_getLast (List.cons_ne_nil _ _),
              List.getLast_eq_getElem]
          rw [hget, hpreNe (List.cons_ne_nil _ _), hi1]
      · have hassoc : (pre ++ [e1]) ++ r1 = pre ++ e1 :: r1 := by simp
        have hlastPre : ((pre ++ [e1]).getLast?.map (·.j)).getD 0 = m := by
          clear hpreNe hpreNil hassoc ih
          induction pre with
          | nil => simpa using hj1
          | cons _ tl0 ihp =>
            rw [List.cons_append]
            cases tl0 with
            | nil => simpa using hj1
            | cons _ _ => rw [List.cons_append, List.getLast?_cons_cons]; exact ihp
        rw [← hassoc, show pre.length + 1 = (pre ++ [e1]).length from by simp]
        exact ih (pre ++ [e1]) (fun _ => hlastPre) (fun h => by cases pre <;> cases h)
  cases hch with
  | nil _ => exact ⟨rfl, rfl⟩
  | @cons _ _ _ e0 tl hi0 hj0 htl =>
    refine ⟨?_, hlast e0 tl hj0 htl⟩
    simpa using hzip (.cons e0 hi0 hj0 htl) [] (fun h => absurd rfl h) (fun _ => rfl)

theorem blocks_chainEls {a b : Nat} {blocks : List TokBlock} {cx : Ctx} {cs : Array Nat} {first : Bool}
    (hch : BlocksChain a b blocks)
    (hv : ∀ blk ∈ blocks, ValidTokBlock cx cs first blk) :
    ChainEls a b (blocks.flatMap fun blk => blk.triv ++ [blk.tokEl]) := by
  induction hch with
  | nil p => exact .nil p
  | cons blk hp hrest ih =>
    subst hp
    have hb := hv blk (List.mem_cons_self ..)
    have h1 : ChainEls blk.p blk.tokEl.j (blk.triv ++ [blk.tokEl]) :=
      hb.1.append (.cons blk.tokEl rfl rfl (.nil _))
    exact h1.append (ih (fun x hx => hv x (List.mem_cons_of_mem _ hx)))

theorem blocks_filter_isToken {blocks : List TokBlock} {elsEnd : List Element}
    {cx : Ctx} {cs : Array Nat} {first : Bool}
    (hv : ∀ blk ∈ blocks, ValidTokBlock cx cs first blk)
    (hend : ∀ e ∈ elsEnd, ValidTrivEl cx cs first e) :
    (((blocks.flatMap fun blk => blk.triv ++ [blk.tokEl]) ++ elsEnd).filter Element.isToken) =
      blocks.map (·.tokEl) := by
  have htrivF : ∀ es : List Element, (∀ e ∈ es, ValidTrivEl cx cs first e) →
      es.filter Element.isToken = [] := by
    intro es hes; rw [List.filter_eq_nil_iff]
    intro e he; rw [(hes e he).2.2.1]; simp
  rw [List.filter_append, htrivF elsEnd hend, List.append_nil]
  induction blocks with
  | nil => rfl
  | cons blk bs ih =>
    have hb := hv blk (List.mem_cons_self ..)
    simp only [List.flatMap_cons, List.filter_append, htrivF blk.triv hb.2.1, List.nil_append,
      List.filter_cons, hb.2.2.2.2.2.2.1, ↓reduceIte, List.filter_nil, List.cons_append, List.map_cons]
    congr 1
    exact ih (fun x hx => hv x (List.mem_cons_of_mem _ hx))

private theorem takeWhile_not_isToken_rev_append (pre triv : List Element) (tok : Element)
    (htok : tok.isToken = true) (htriv : ∀ e ∈ triv, e.isToken = false) :
    ((pre ++ [tok] ++ triv).reverse.takeWhile (fun e => !e.isToken)) = triv.reverse := by
  have hrevEq : (pre ++ [tok] ++ triv).reverse = triv.reverse ++ (tok :: pre.reverse) := by
    simp [List.append_assoc]
  rw [hrevEq]
  have htwAll : ∀ (l : List Element), (∀ x ∈ l, (!x.isToken) = true) →
      ((l ++ tok :: pre.reverse).takeWhile (fun e => !e.isToken)) = l := by
    intro l hl
    induction l with
    | nil => simp [htok]
    | cons x xs ihL =>
      rw [List.cons_append, List.takeWhile_cons, hl x (List.mem_cons_self ..)]
      simp only [↓reduceIte]
      congr 1; exact ihL (fun y hy => hl y (List.mem_cons_of_mem _ hy))
  exact htwAll triv.reverse (fun x hx => by
    rw [htriv x (List.mem_reverse.mp hx)]; rfl)

theorem blocks_tokensOf {blocks : List TokBlock} {elsEnd : List Element}
    {cx : Ctx} {cs : Array Nat} {first : Bool}
    (hv : ∀ blk ∈ blocks, ValidTokBlock cx cs first blk)
    (hend : ∀ e ∈ elsEnd, ValidTrivEl cx cs first e) :
    tokensOf cs.toList ((blocks.flatMap fun blk => blk.triv ++ [blk.tokEl]) ++ elsEnd) =
      blocks.map (fun blk => ⟨slice cs.toList blk.tokEl.i blk.tokEl.j, blk.lt, none⟩) := by
  unfold tokensOf
  have hgen : ∀ (acc : List Element) (rem : List TokBlock),
      (acc = [] ∨ ∃ pre prevTok, acc = pre ++ [prevTok] ∧ prevTok.isToken = true) →
      (∀ blk ∈ rem, ValidTokBlock cx cs first blk) →
      ((((rem.flatMap fun (blk : TokBlock) => blk.triv ++ [blk.tokEl]) ++ elsEnd).zipIdx acc.length).filter (fun p => p.1.isToken)).map (fun (e, k) =>
        let before := ((acc ++ ((rem.flatMap fun (blk : TokBlock) => blk.triv ++ [blk.tokEl]) ++ elsEnd)).take k).reverse.takeWhile (fun (x : Element) => !x.isToken)
        ({ text := slice cs.toList e.i e.j, lt := before.any (fun x => x.breaks cs.toList), virt := none } : Token)) =
      rem.map (fun blk => ⟨slice cs.toList blk.tokEl.i blk.tokEl.j, blk.lt, none⟩) := by
    intro acc rem hacc hrem
    have hzipTriv : ∀ (tr : List Element) (rest : List Element) (off : Nat),
        (∀ e ∈ tr, e.isToken = false) →
        ((tr ++ rest).zipIdx off).filter (fun p => p.1.isToken) =
          (rest.zipIdx (off + tr.length)).filter (fun p => p.1.isToken) := by
      intro tr rest off htr
      induction tr generalizing off with
      | nil => simp
      | cons e ts ihT =>
        simp only [List.cons_append, List.zipIdx_cons, List.filter_cons,
          htr e (List.mem_cons_self ..), Bool.false_eq_true, ↓reduceIte, List.length_cons]
        rw [ihT (off + 1) (fun x hx => htr x (List.mem_cons_of_mem _ hx))]
        ac_rfl
    induction rem generalizing acc with
    | nil =>
      simp only [List.flatMap_nil, List.nil_append, List.map_nil]
      have := hzipTriv elsEnd [] acc.length (fun e he => (hend e he).2.2.1)
      rw [List.append_nil] at this
      rw [this]; rfl
    | cons blk bs ih =>
      have hb := hrem blk (List.mem_cons_self ..)
      have hbs := fun x hx => hrem x (List.mem_cons_of_mem _ hx)
      let restTail := (bs.flatMap fun b => b.triv ++ [b.tokEl]) ++ elsEnd
      have htailEq : ((blk :: bs).flatMap fun b => b.triv ++ [b.tokEl]) ++ elsEnd =
          blk.triv ++ (blk.tokEl :: restTail) := by
        simp [restTail, List.append_assoc]
      rw [htailEq, hzipTriv blk.triv (blk.tokEl :: restTail) acc.length (fun e he => (hb.2.1 e he).2.2.1)]
      simp only [List.zipIdx_cons, List.filter_cons, hb.2.2.2.2.2.2.1, ↓reduceIte, List.map_cons]
      have htakeK : (acc ++ (blk.triv ++ (blk.tokEl :: restTail))).take (acc.length + blk.triv.length) =
          acc ++ blk.triv := by
        rw [show acc ++ (blk.triv ++ (blk.tokEl :: restTail)) = (acc ++ blk.triv) ++ (blk.tokEl :: restTail) from by simp [List.append_assoc]]
        rw [← List.length_append, List.take_left]
      have hbefEq : ((acc ++ (blk.triv ++ (blk.tokEl :: restTail))).take (acc.length + blk.triv.length)).reverse.takeWhile
          (fun x => !x.isToken) = blk.triv.reverse := by
        rw [htakeK]
        rcases hacc with rfl | ⟨pre, prevTok, rfl, hpt⟩
        · rw [List.nil_append]
          have hall : ∀ x ∈ blk.triv.reverse, (!x.isToken) = true := by
            intro x hx; rw [(hb.2.1 x (List.mem_reverse.mp hx)).2.2.1]; rfl
          have htwSelf : ∀ (l : List Element), (∀ x ∈ l, (!x.isToken) = true) →
              l.takeWhile (fun x => !x.isToken) = l := by
            intro l hl; induction l with
            | nil => rfl
            | cons y ys ihy =>
              simp only [List.takeWhile_cons, hl y (List.mem_cons_self ..), ↓reduceIte]
              exact congrArg (y :: ·) (ihy fun z hz => hl z (List.mem_cons_of_mem _ hz))
          exact htwSelf _ hall
        · exact takeWhile_not_isToken_rev_append pre blk.triv prevTok hpt (fun e he => (hb.2.1 e he).2.2.1)
      have hanyEq : (blk.triv.reverse.any fun x => x.breaks cs.toList) = blk.lt := by
        rw [List.any_reverse]; exact hb.2.2.1
      congr 1
      · rw [hbefEq, hanyEq]
      · have hacc' := ih (acc ++ blk.triv ++ [blk.tokEl])
          (Or.inr ⟨acc ++ blk.triv, blk.tokEl, rfl, hb.2.2.2.2.2.2.1⟩) hbs
        have hlenEq : acc.length + blk.triv.length + 1 = (acc ++ blk.triv ++ [blk.tokEl]).length := by
          simp [List.length_append, Nat.add_assoc]
        have hlistEq : acc ++ (blk.triv ++ blk.tokEl :: restTail) =
            (acc ++ blk.triv ++ [blk.tokEl]) ++ restTail := by simp [List.append_assoc]
        simpa only [hlenEq, hlistEq] using hacc'
  simpa using hgen [] blocks (Or.inl rfl) hv

theorem TokStreamInv.scans {cx : Ctx} {cs : Array Nat} {first : Bool} {vs : List (Nat × Bool)}
    {els : List Element} {toks : List Token}
    (hinv : TokStreamInv cx cs first vs els toks) :
    Scans Ecma.Spec.gl cx Engine.Model.codePrims cs.toList els := by
  have hchAll : ChainEls 0 cs.size els :=
    hinv.helsEq ▸ (blocks_chainEls hinv.hchain hinv.hvalid).append hinv.hendChain
  obtain ⟨hzip, hlast⟩ := chainEls_scans_structure hchAll
  unfold Scans
  rw [Array.length_toList]
  refine ⟨hzip, hlast, fun e he => ?_⟩
  have he' : e ∈ (hinv.blocks.flatMap fun blk => blk.triv ++ [blk.tokEl]) ++ hinv.elsEnd :=
    hinv.helsEq ▸ he
  rcases List.mem_append.mp he' with hblk | hend
  · rw [List.mem_flatMap] at hblk
    obtain ⟨blk, hbm, hem⟩ := hblk
    have hb := hinv.hvalid blk hbm
    rw [List.mem_append, List.mem_singleton] at hem
    rcases hem with htr | rfl
    · obtain ⟨hij, hjSz, _, _, hder, hmax, hhasF⟩ := hb.2.1 e htr
      exact ⟨hij, hder, hmax, fun hh => by rw [hhasF] at hh; cases hh⟩
    · obtain ⟨_, _, _, _, hij, _, _, lg, _, hgoalEq, ⟨_, _, _, _, hder, hmax, hfol⟩⟩ := hb
      rw [← hgoalEq] at hder hmax
      exact ⟨hij, hder, hmax, hfol⟩
  · obtain ⟨hij, _, _, _, hder, hmax, hhasF⟩ := hinv.hendValid e hend
    exact ⟨hij, hder, hmax, fun hh => by rw [hhasF] at hh; cases hh⟩

theorem filter_isNone_and_realIdx :
    ∀ (toks : List Token) {k : Nat} {tok : Token},
      toks[k]? = some tok → tok.virt = none →
      let r := (toks.take k).countP (·.virt.isNone)
      (toks.filter (·.virt.isNone))[r]? = some tok ∧ realIdx r toks = k
  | [], _, _, h, _ => by cases h
  | hd :: tl, 0, tok, h, hv => by
    injection h with heq; subst heq
    simp [realIdx, hv]
  | hd :: tl, k + 1, tok, h, hv => by
    simp only [List.getElem?_cons_succ] at h
    have ⟨hf, hr⟩ := filter_isNone_and_realIdx tl h hv
    cases hhd : hd.virt.isNone with
    | true =>
      simp only [List.take_succ_cons, List.countP_cons, hhd, ↓reduceIte, List.filter_cons]
      rw [Nat.add_comm _ 1, show 1 + (tl.take k).countP (·.virt.isNone) = (tl.take k).countP (·.virt.isNone) + 1 from Nat.add_comm _ _]
      simp only [List.getElem?_cons_succ, realIdx, hhd, ↓reduceIte, hr]
      exact ⟨hf, Nat.add_comm 1 k⟩
    | false =>
      simp only [List.take_succ_cons, List.countP_cons, hhd, Bool.false_eq_true, ↓reduceIte, Nat.add_zero, List.filter_cons]
      refine ⟨hf, ?_⟩
      cases hcnt : (tl.take k).countP (·.virt.isNone) with
      | zero =>
        rw [hcnt] at hr
        simp [realIdx, hhd, hr, Nat.add_comm 1 k]
      | succ n =>
        rw [hcnt] at hr
        simp [realIdx, hhd, hr, Nat.add_comm 1 k]

private theorem blocksChain_pos_mono {a b : Nat} {blocks : List TokBlock}
    {cx : Ctx} {cs : Array Nat} {first : Bool}
    (hch : BlocksChain a b blocks)
    (hv : ∀ blk ∈ blocks, ValidTokBlock cx cs first blk) :
    a ≤ b ∧
    (∀ r (hr : r < blocks.length),
      (if r == 0 then a else (blocks[r - 1]'(by omega)).tokEl.j) = (blocks[r]'hr).p ∧
      (blocks[r]'hr).p < (blocks[r]'hr).tokEl.j) ∧
    (∀ (hne : blocks ≠ []), (blocks[blocks.length - 1]'(by cases blocks with | nil => exact absurd rfl hne | cons _ _ => simp)).tokEl.j = b) ∧
    (blocks = [] → a = b) := by
  induction hch with
  | nil p =>
    exact ⟨Nat.le_refl _, (fun _ hr => absurd hr (Nat.not_lt_zero _)), (fun h => absurd rfl h), (fun _ => rfl)⟩
  | @cons p0 m0 blk bs hp hrest ih =>
    have hb := hv blk (List.mem_cons_self ..)
    have hpLeI := chainEls_le hb.1 (fun e he => (hb.2.1 e he).1)
    have hiLtJ := hb.2.2.2.2.1
    have hpLtJ : p0 < blk.tokEl.j := by omega
    have ⟨hjLeM, hidxRest, hlastRest, hnilRest⟩ := ih (fun x hx => hv x (List.mem_cons_of_mem _ hx))
    refine ⟨by omega, fun r hr => ?_, fun _ => ?_, (fun h => nomatch h)⟩
    · cases r with
      | zero => simp only [List.getElem_cons_zero]; exact ⟨hp.symm, hp ▸ hpLtJ⟩
      | succ r' =>
        have hr' : r' < bs.length := by simp at hr; exact hr
        have ⟨hprev, hltR⟩ := hidxRest r' hr'
        refine ⟨?_, hltR⟩
        cases r' with
        | zero => simpa using hprev
        | succ r'' => simpa using hprev
    · cases bs with
      | nil => simp [hnilRest rfl]
      | cons b2 bs2 => exact hlastRest (List.cons_ne_nil _ _)

theorem TokStreamInv.tokensOf_eq {cx : Ctx} {cs : Array Nat} {first : Bool} {vs : List (Nat × Bool)}
    {els : List Element} {toks : List Token} (hinv : TokStreamInv cx cs first vs els toks) :
    tokensOf cs.toList els =
      hinv.blocks.map (fun blk => ⟨slice cs.toList blk.tokEl.i blk.tokEl.j, blk.lt, none⟩) :=
  (congrArg (tokensOf cs.toList) hinv.helsEq).trans (blocks_tokensOf hinv.hvalid hinv.hendValid)

theorem TokStreamInv.filter_isToken_eq {cx : Ctx} {cs : Array Nat} {first : Bool} {vs : List (Nat × Bool)}
    {els : List Element} {toks : List Token} (hinv : TokStreamInv cx cs first vs els toks) :
    els.filter Element.isToken = hinv.blocks.map (·.tokEl) :=
  (congrArg (List.filter Element.isToken) hinv.helsEq).trans (blocks_filter_isToken hinv.hvalid hinv.hendValid)

theorem TokStreamInv.countP_le_blocks {cx : Ctx} {cs : Array Nat} {first : Bool} {vs : List (Nat × Bool)}
    {els : List Element} {toks : List Token} (hinv : TokStreamInv cx cs first vs els toks) (k : Nat) :
    (toks.take k).countP (·.virt.isNone) ≤ hinv.blocks.length := by
  have h1 : (toks.take k).countP (·.virt.isNone) ≤ toks.countP (·.virt.isNone) := by
    have : toks = toks.take k ++ toks.drop k := (List.take_append_drop k toks).symm
    conv => rhs; rw [this, List.countP_append]
    omega
  simp only [List.countP_eq_length_filter, hinv.htoksFilt, hinv.tokensOf_eq, List.length_map] at h1 ⊢
  exact h1

theorem TokStreamInv.tokPos_eq {cx : Ctx} {cs : Array Nat} {first : Bool} {vs : List (Nat × Bool)}
    {els : List Element} {toks : List Token} (hinv : TokStreamInv cx cs first vs els toks) (k : Nat) :
    let r := (toks.take k).countP (·.virt.isNone)
    (∀ hr : r < hinv.blocks.length, tokPos els toks k = (hinv.blocks[r]'hr).p) ∧
    (r = hinv.blocks.length → tokPos els toks k = hinv.endPos) := by
  dsimp only
  have hrLe := hinv.countP_le_blocks k
  have ⟨_, hidx, hlast, hnil⟩ := blocksChain_pos_mono hinv.hchain hinv.hvalid
  unfold tokPos
  rw [hinv.filter_isToken_eq]
  dsimp only
  generalize (toks.take k).countP (·.virt.isNone) = r at hrLe ⊢
  constructor
  · intro hrLt
    obtain ⟨hprev, _⟩ := hidx r hrLt
    cases r with
    | zero => simpa using hprev
    | succ r' =>
      have hrNe : (r' + 1 == 0) = false := rfl
      simp only [hrNe, Bool.false_eq_true, ↓reduceIte, Nat.add_sub_cancel]
      have hr'Lt : r' < hinv.blocks.length := Nat.lt_of_succ_lt hrLt
      simp only [List.getElem?_map, List.getElem?_eq_getElem hr'Lt, Option.map_some, Option.getD_some]
      simpa using hprev
  · intro hrEq
    cases hblks : hinv.blocks with
    | nil =>
      have hr0 : r = 0 := by rw [hblks] at hrEq; exact hrEq
      rw [hr0]; simpa using hnil hblks
    | cons b0 bs =>
      have hposL : 0 < hinv.blocks.length := by rw [hblks]; simp
      have hrNe : (r == 0) = false := beq_eq_false_iff_ne.mpr (by omega)
      simp only [hrNe, Bool.false_eq_true, ↓reduceIte]
      have hrm1 : r - 1 < (b0 :: bs).length := by rw [← hblks]; omega
      simp only [List.getElem?_map, List.getElem?_eq_getElem hrm1, Option.map_some, Option.getD_some]
      have hlastEq := hlast (by rw [hblks]; exact List.cons_ne_nil _ _)
      have hidxEq : r - 1 = hinv.blocks.length - 1 := by omega
      have hgetEq : (b0 :: bs)[r - 1]'hrm1 = hinv.blocks[hinv.blocks.length - 1]'(by omega) := by
        apply Option.some.inj
        rw [← List.getElem?_eq_getElem hrm1, ← List.getElem?_eq_getElem (by omega), ← hblks, hidxEq]
      rw [hgetEq]; exact hlastEq

theorem TokStreamInv.tokPos_inj_countP {cx : Ctx} {cs : Array Nat} {first : Bool} {vs : List (Nat × Bool)}
    {els : List Element} {toks : List Token} (hinv : TokStreamInv cx cs first vs els toks)
    {k1 k2 : Nat} (heq : tokPos els toks k1 = tokPos els toks k2) :
    (toks.take k1).countP (·.virt.isNone) = (toks.take k2).countP (·.virt.isNone) := by
  let len := hinv.blocks.length
  have ⟨_, hidx, hlast, _⟩ := blocksChain_pos_mono hinv.hchain hinv.hvalid
  let posAt (r : Nat) : Nat :=
    if hr : r < len then (hinv.blocks[r]'hr).p else hinv.endPos
  have hstepLt : ∀ r, r < len → posAt r < posAt (r + 1) := by
    intro r hr
    simp only [posAt, hr, ↓reduceDIte]
    by_cases hr1 : r + 1 < len
    · simp only [hr1, ↓reduceDIte]
      have ⟨hprev1, _⟩ := hidx (r + 1) hr1
      have ⟨_, hlt0⟩ := hidx r hr
      simp only [Nat.add_one_sub_one, beq_iff_eq, Nat.succ_ne_zero, ↓reduceIte] at hprev1
      omega
    · simp only [hr1, ↓reduceDIte]
      have hrLast : r = len - 1 := by omega
      have hne : hinv.blocks ≠ [] := by
        intro hn
        have hlen0 : len = 0 := by dsimp only [len]; rw [hn]; rfl
        omega
      have hlEq := hlast hne
      have ⟨_, hlt0⟩ := hidx r hr
      have hjEq : (hinv.blocks[r]'hr).tokEl.j = hinv.endPos := by
        simpa [hrLast] using hlEq
      omega
  have hmonoLt : ∀ a b, a < b → b ≤ len → posAt a < posAt b := by
    intro a b hab hble
    induction b with
    | zero => omega
    | succ b' ih =>
      by_cases hab' : a < b'
      · exact Nat.lt_trans (ih hab' (by omega)) (hstepLt b' (by omega))
      · have habEq : a = b' := by omega
        subst habEq; exact hstepLt a (by omega)
  let r1 := (toks.take k1).countP (·.virt.isNone)
  let r2 := (toks.take k2).countP (·.virt.isNone)
  have hr1Le : r1 ≤ len := hinv.countP_le_blocks k1
  have hr2Le : r2 ≤ len := hinv.countP_le_blocks k2
  have hp1 : tokPos els toks k1 = posAt r1 := by
    by_cases h1 : r1 < len
    · simp only [posAt, h1, ↓reduceDIte]; exact (hinv.tokPos_eq k1).1 h1
    · simp only [posAt, h1, ↓reduceDIte]; exact (hinv.tokPos_eq k1).2 (by omega)
  have hp2 : tokPos els toks k2 = posAt r2 := by
    by_cases h2 : r2 < len
    · simp only [posAt, h2, ↓reduceDIte]; exact (hinv.tokPos_eq k2).1 h2
    · simp only [posAt, h2, ↓reduceDIte]; exact (hinv.tokPos_eq k2).2 (by omega)
  rw [hp1, hp2] at heq
  by_cases hlt : r1 < r2
  · have := hmonoLt r1 r2 hlt hr2Le; omega
  · by_cases hgt : r2 < r1
    · have := hmonoLt r2 r1 hgt hr1Le; omega
    · omega

theorem TokStreamInv.tokBnd_virt {cx : Ctx} {cs : Array Nat} {first : Bool} {vs : List (Nat × Bool)}
    {els : List Element} {toks : List Token} (hinv : TokStreamInv cx cs first vs els toks)
    {k : Nat} {tok : Token} {why : Why}
    (hget : toks[k]? = some tok) (hvirt : tok.virt = some why) :
    let p := tokPos els toks k
    tokBnd els toks k = 2 * p ∧
    vsPending vs (tokBnd els toks k) = true ∧
    tokBnd els toks (k + 1) = 2 * p + 1 ∧
    why = (if vsParen vs p then .paren else if k + 1 == toks.length then .eof else .offending) ∧
    (p, vsParen vs p) ∈ vs := by
  dsimp only
  let p := tokPos els toks k
  have hpDef : p = tokPos els toks k := rfl
  have ⟨hwhyEq, hpMem⟩ := hinv.hasi.2.1 k tok why hget hvirt
  rw [← hpDef] at hwhyEq hpMem
  have hprevNotVirt : (0 < k && ((toks[k - 1]?).bind Token.virt).isSome) = false := by
    by_cases hk0 : 0 < k
    · obtain ⟨km1, rfl⟩ : ∃ km1, k = km1 + 1 := ⟨k - 1, by omega⟩
      have hkm1Lt : km1 < toks.length := Nat.lt_trans (Nat.lt_succ_self km1) (List.getElem?_eq_some_iff.mp hget).1
      have hgetPrev : toks[km1]? = some toks[km1] := List.getElem?_eq_getElem hkm1Lt
      rcases hinv.hasi.1 km1 toks[km1] tok hgetPrev hget with hvNone | hv2None
      · simp [hgetPrev, hvNone]
      · rw [hvirt] at hv2None; cases hv2None
    · simp [hk0]
  have hbndK : tokBnd els toks k = 2 * p := by
    unfold tokBnd; rw [hprevNotVirt, ← hpDef]; simp
  have hpend : vsPending vs (tokBnd els toks k) = true := by
    rw [hbndK]
    exact (vsPending_iff vs (2 * p)).mpr ⟨by omega, (p, vsParen vs p), hpMem, by omega⟩
  have hkLt : k < toks.length := (List.getElem?_eq_some_iff.mp hget).1
  have htakeSucc : toks.take (k + 1) = toks.take k ++ [tok] := by
    rw [List.take_add_one, hget, Option.toList_some]
  have hcntEq : (toks.take (k + 1)).countP (·.virt.isNone) = (toks.take k).countP (·.virt.isNone) := by
    rw [htakeSucc, List.countP_append, List.countP_cons, List.countP_nil, hvirt]; simp
  have hpSucc : tokPos els toks (k + 1) = p := by
    rw [hpDef]; unfold tokPos; dsimp only; rw [hcntEq]
  have hbndSucc : tokBnd els toks (k + 1) = 2 * p + 1 := by
    unfold tokBnd
    rw [hpSucc, Nat.add_sub_cancel, hget]
    simp [hvirt]
  exact ⟨hbndK, hpend, hbndSucc, hwhyEq, hpMem⟩

theorem TokStreamInv.not_pending_nonvirt {cx : Ctx} {cs : Array Nat} {first : Bool} {vs : List (Nat × Bool)}
    {els : List Element} {toks : List Token} (hinv : TokStreamInv cx cs first vs els toks)
    {k : Nat} (hkLe : k ≤ toks.length)
    (hnotVirt : ∀ tok, toks[k]? = some tok → tok.virt = none) :
    vsPending vs (tokBnd els toks k) = false := by
  cases hp : vsPending vs (tokBnd els toks k) with
  | false => rfl
  | true =>
    exfalso
    obtain ⟨heven, pb, hpbMem, hpEq⟩ := (vsPending_iff vs (tokBnd els toks k)).mp hp
    have hprevF : (0 < k && ((toks[k - 1]?).bind Token.virt).isSome) = false := by
      cases hf : (0 < k && ((toks[k - 1]?).bind Token.virt).isSome) with
      | false => rfl
      | true => unfold tokBnd at heven; rw [hf] at heven; simp only [↓reduceIte] at heven; omega
    have hbndDiv : (tokBnd els toks k) / 2 = tokPos els toks k := by
      unfold tokBnd; rw [hprevF]; simp
    rw [hbndDiv] at hpEq
    obtain ⟨k', tok', hk'Get, hk'Virt, hk'Pos⟩ := hinv.hasi.2.2 pb.1 pb.2 hpbMem
    have hrEq := hinv.tokPos_inj_countP (hk'Pos.trans hpEq)
    have hk'Lt : k' < toks.length := (List.getElem?_eq_some_iff.mp hk'Get).1
    by_cases heqK : k' = k
    · subst heqK
      rw [hnotVirt tok' hk'Get] at hk'Virt; cases hk'Virt
    · by_cases hlt : k < k'
      · have hkLt : k < toks.length := Nat.lt_of_lt_of_le hlt (Nat.le_of_lt hk'Lt)
        have hkGet : toks[k]? = some toks[k] := List.getElem?_eq_getElem hkLt
        have hvNone := hnotVirt toks[k] hkGet
        have hsplit : toks.take k' = toks.take k ++ [toks[k]] ++ (toks.drop (k + 1)).take (k' - (k + 1)) := by
          have h1 : toks.take (k + 1) = toks.take k ++ [toks[k]] := by
            rw [List.take_add_one, hkGet, Option.toList_some]
          rw [← h1]
          have h2 : k' = (k + 1) + (k' - (k + 1)) := by omega
          conv => lhs; rw [h2, List.take_add]
        have hcntGe : (toks.take k).countP (·.virt.isNone) + 1 ≤ (toks.take k').countP (·.virt.isNone) := by
          rw [hsplit, List.countP_append, List.countP_append, List.countP_singleton, hvNone]
          simp
        omega
      · have hk'LtK : k' < k := by omega
        by_cases hk'1 : k' + 1 = k
        · subst hk'1
          simp only [Nat.lt_add_one_iff.mpr (Nat.zero_le k'), decide_true, Bool.true_and,
            Nat.add_sub_cancel, hk'Get, Option.bind_some, hk'Virt] at hprevF
          cases hprevF
        · have hk'2Le : k' + 2 ≤ k := by omega
          have hk'1Lt : k' + 1 < toks.length := by omega
          have hk'1Get : toks[k' + 1]? = some toks[k' + 1] := List.getElem?_eq_getElem hk'1Lt
          rcases hinv.hasi.1 k' tok' toks[k' + 1] hk'Get hk'1Get with hv1 | hv2
          · rw [hv1] at hk'Virt; cases hk'Virt
          · have hsplit : toks.take k = toks.take (k' + 1) ++ [toks[k' + 1]] ++ (toks.drop (k' + 2)).take (k - (k' + 2)) := by
              have h1 : toks.take (k' + 2) = toks.take (k' + 1) ++ [toks[k' + 1]] := by
                rw [List.take_add_one, hk'1Get, Option.toList_some]
              rw [← h1]
              have h2 : k = (k' + 2) + (k - (k' + 2)) := by omega
              conv => lhs; rw [h2, List.take_add]
            have htk1 : toks.take (k' + 1) = toks.take k' ++ [tok'] := by
              rw [List.take_add_one, hk'Get, Option.toList_some]
            have hcntGe : (toks.take k').countP (·.virt.isNone) + 1 ≤ (toks.take k).countP (·.virt.isNone) := by
              rw [hsplit, htk1, List.countP_append, List.countP_append, List.countP_append,
                List.countP_singleton, List.countP_singleton, hv2]
              simp only [Option.isNone_none, ↓reduceIte]
              omega
            omega

theorem TokStreamInv.tokBnd_real {cx : Ctx} {cs : Array Nat} {first : Bool} {vs : List (Nat × Bool)}
    {els : List Element} {toks : List Token} (hinv : TokStreamInv cx cs first vs els toks)
    {k : Nat} {tok : Token} (hget : toks[k]? = some tok) (hnone : tok.virt = none) :
    let r := (toks.take k).countP (·.virt.isNone)
    ∃ (hr : r < hinv.blocks.length),
      let blk := hinv.blocks[r]'hr
      (tokBnd els toks k) / 2 = blk.p ∧
      vsPending vs (tokBnd els toks k) = false ∧
      tok = ⟨slice cs.toList blk.tokEl.i blk.tokEl.j, blk.lt, none⟩ ∧
      noCross vs blk.p blk.tokEl.j = true ∧
      tokBnd els toks (k + 1) = 2 * blk.tokEl.j ∧
      realIdx r toks = k := by
  dsimp only
  let r := (toks.take k).countP (·.virt.isNone)
  have hrDef : r = (toks.take k).countP (·.virt.isNone) := rfl
  have hkLt : k < toks.length := (List.getElem?_eq_some_iff.mp hget).1
  obtain ⟨hfiltGet, hrealEq⟩ := filter_isNone_and_realIdx toks hget hnone
  rw [← hrDef, hinv.htoksFilt, hinv.tokensOf_eq, List.getElem?_map] at hfiltGet
  rw [← hrDef] at hrealEq
  have hrLt : r < hinv.blocks.length := by
    cases hg : hinv.blocks[r]? with
    | none => rw [hg] at hfiltGet; cases hfiltGet
    | some _ => exact (List.getElem?_eq_some_iff.mp hg).1
  rw [List.getElem?_eq_getElem hrLt, Option.map_some, Option.some.injEq] at hfiltGet
  refine ⟨hrLt, ?_⟩
  let blk := hinv.blocks[r]'hrLt
  have hpEq : tokPos els toks k = blk.p := (hinv.tokPos_eq k).1 (hrDef ▸ hrLt)
  have hdiv2 : (tokBnd els toks k) / 2 = blk.p := by
    unfold tokBnd; rw [hpEq]; split <;> omega
  have hnp : vsPending vs (tokBnd els toks k) = false :=
    hinv.not_pending_nonvirt (Nat.le_of_lt hkLt) (fun t ht => by rw [hget] at ht; injection ht with e; exact e ▸ hnone)
  have hnc : noCross vs blk.p blk.tokEl.j = true := by
    unfold noCross
    rw [List.all_eq_true]
    rintro ⟨v, b⟩ hvMem
    rw [Bool.not_eq_true', Bool.and_eq_false_iff]
    obtain ⟨kv, _, _, _, hkvPos⟩ := hinv.hasi.2.2 v b hvMem
    let rv := (toks.take kv).countP (·.virt.isNone)
    have hrvDef : rv = (toks.take kv).countP (·.virt.isNone) := rfl
    have hrvLe := hinv.countP_le_blocks kv
    rw [← hrvDef] at hrvLe
    have ⟨_, hidx, hlast, _⟩ := blocksChain_pos_mono hinv.hchain hinv.hvalid
    have hmono : ∀ a0 b0 (ha0 : a0 < hinv.blocks.length) (hb0 : b0 < hinv.blocks.length), a0 ≤ b0 →
        (hinv.blocks[a0]'ha0).p ≤ (hinv.blocks[b0]'hb0).p := by
      intro a0 b0 ha0 hb0 hab0
      induction b0 with
      | zero =>
        have haZ : a0 = 0 := by omega
        subst haZ; exact Nat.le_refl _
      | succ b' ih =>
        by_cases hab' : a0 ≤ b'
        · have hb'Lt : b' < hinv.blocks.length := by omega
          have hle1 := ih hb'Lt hab'
          have ⟨hprev, _⟩ := hidx (b' + 1) hb0
          have ⟨_, hltB'⟩ := hidx b' hb'Lt
          simp only [Nat.add_one_sub_one, beq_iff_eq, Nat.succ_ne_zero, ↓reduceIte] at hprev
          omega
        · have haEq : a0 = b' + 1 := by omega
          subst haEq; exact Nat.le_refl _
    by_cases hrvLeR : rv ≤ r
    · left
      have hrvLt0 : rv < hinv.blocks.length := Nat.lt_of_le_of_lt hrvLeR hrLt
      have hvEq : v = (hinv.blocks[rv]'hrvLt0).p :=
        hkvPos.symm.trans ((hinv.tokPos_eq kv).1 (hrvDef ▸ hrvLt0))
      have hle := hmono rv r hrvLt0 hrLt hrvLeR
      dsimp only [blk]; simp [hvEq]; omega
    · right
      have hrvGe : r + 1 ≤ rv := by omega
      by_cases hrvLt : rv < hinv.blocks.length
      · have hvEq : v = (hinv.blocks[rv]'hrvLt).p :=
          hkvPos.symm.trans ((hinv.tokPos_eq kv).1 (hrvDef ▸ hrvLt))
        have hr1Lt : r + 1 < hinv.blocks.length := by omega
        have ⟨hprevR1, _⟩ := hidx (r + 1) hr1Lt
        simp only [Nat.add_one_sub_one, beq_iff_eq, Nat.succ_ne_zero, ↓reduceIte] at hprevR1
        have hle := hmono (r + 1) rv hr1Lt hrvLt hrvGe
        dsimp only [blk]; simp [hvEq]; omega
      · have hrvEq : rv = hinv.blocks.length := by omega
        have hvEq : v = hinv.endPos := hkvPos.symm.trans ((hinv.tokPos_eq kv).2 (hrvDef ▸ hrvEq))
        have hlastEq := hlast (by intro hn; rw [hn] at hrLt; exact nomatch hrLt)
        have hleEnd : blk.tokEl.j ≤ hinv.endPos := by
          by_cases hrLast : r + 1 = hinv.blocks.length
          · have hidxLast : r = hinv.blocks.length - 1 := by omega
            have : blk.tokEl.j = (hinv.blocks[hinv.blocks.length - 1]'(by omega)).tokEl.j := by
              dsimp only [blk]; simp only [hidxLast]
            omega
          · have hr1Lt : r + 1 < hinv.blocks.length := by omega
            have ⟨hprevR1, _⟩ := hidx (r + 1) hr1Lt
            simp only [Nat.add_one_sub_one, beq_iff_eq, Nat.succ_ne_zero, ↓reduceIte] at hprevR1
            have hleLast := hmono (r + 1) (hinv.blocks.length - 1) hr1Lt (by omega) (by omega)
            have ⟨_, hltLast⟩ := hidx (hinv.blocks.length - 1) (by omega)
            dsimp only [blk]; omega
        simp [hvEq]; omega
  have htkSucc : toks.take (k + 1) = toks.take k ++ [tok] := by
    rw [List.take_add_one, hget, Option.toList_some]
  have hcntSucc : (toks.take (k + 1)).countP (·.virt.isNone) = r + 1 := by
    rw [htkSucc, List.countP_append, List.countP_singleton, hnone, ← hrDef]; rfl
  have hpSucc : tokPos els toks (k + 1) = blk.tokEl.j := by
    have ⟨_, hidx, hlast, _⟩ := blocksChain_pos_mono hinv.hchain hinv.hvalid
    by_cases hr1Lt : r + 1 < hinv.blocks.length
    · have h1 := (hinv.tokPos_eq (k + 1)).1 (hcntSucc ▸ hr1Lt)
      have ⟨hprev, _⟩ := hidx (r + 1) hr1Lt
      simp only [Nat.add_one_sub_one, beq_iff_eq, Nat.succ_ne_zero, ↓reduceIte] at hprev
      exact h1.trans (by simpa [hcntSucc] using hprev.symm)
    · have hr1Eq : r + 1 = hinv.blocks.length := by omega
      have h1 := (hinv.tokPos_eq (k + 1)).2 (hcntSucc.trans hr1Eq)
      have hlastEq := hlast (by intro hn; rw [hn] at hrLt; exact nomatch hrLt)
      have hidxEq : r = hinv.blocks.length - 1 := by omega
      exact h1.trans (by simpa [blk, hidxEq] using hlastEq.symm)
  have hbndSucc : tokBnd els toks (k + 1) = 2 * blk.tokEl.j := by
    unfold tokBnd
    rw [hpSucc, Nat.add_sub_cancel, hget]
    simp [hnone]
  exact ⟨hdiv2, hnp, hfiltGet.symm, hnc, hbndSucc, hrealEq⟩

theorem TokStreamInv.tokBnd_end {cx : Ctx} {cs : Array Nat} {first : Bool} {vs : List (Nat × Bool)}
    {els : List Element} {toks : List Token} (hinv : TokStreamInv cx cs first vs els toks) :
    let e := tokBnd els toks toks.length
    e / 2 = hinv.endPos ∧
    vsPending vs e = false ∧
    vs.all (fun (q, _) => q ≤ e / 2) = true := by
  dsimp only
  let e := tokBnd els toks toks.length
  have heDef : e = tokBnd els toks toks.length := rfl
  have hcntAll : (toks.take toks.length).countP (·.virt.isNone) = hinv.blocks.length := by
    rw [List.take_length, List.countP_eq_length_filter, hinv.htoksFilt, hinv.tokensOf_eq, List.length_map]
  have hpEnd : tokPos els toks toks.length = hinv.endPos := (hinv.tokPos_eq toks.length).2 hcntAll
  have hdiv2 : e / 2 = hinv.endPos := by
    rw [heDef]; unfold tokBnd; rw [hpEnd]; split <;> omega
  have hnp : vsPending vs e = false :=
    heDef ▸ hinv.not_pending_nonvirt (Nat.le_refl _) (fun _ ht => by rw [List.getElem?_eq_none (Nat.le_refl _)] at ht; cases ht)
  have hallVs : vs.all (fun (q, _) => q ≤ e / 2) = true := by
    rw [hdiv2, List.all_eq_true]
    rintro ⟨q, b⟩ hqb
    rw [decide_eq_true_eq]
    obtain ⟨kq, _, _, _, hkqPos⟩ := hinv.hasi.2.2 q b hqb
    rw [← hkqPos]
    let rq := (toks.take kq).countP (·.virt.isNone)
    have hrqDef : rq = (toks.take kq).countP (·.virt.isNone) := rfl
    have hrqLe := hinv.countP_le_blocks kq
    rw [← hrqDef] at hrqLe
    by_cases hrqLt : rq < hinv.blocks.length
    · rw [(hinv.tokPos_eq kq).1 (hrqDef ▸ hrqLt)]
      have hgen : ∀ (bs : List TokBlock) {x y : Nat} (idx : Nat) (hidxLt : idx < bs.length),
          BlocksChain x y bs → BlocksChain (bs[idx]'hidxLt).p y (bs.drop idx) := by
        intro bs
        induction bs with
        | nil => intro _ _ _ h; exact nomatch h
        | cons hd tl ihB =>
          intro x y idx hlt hcB
          cases hcB with
          | cons _ hpB hrestB =>
            cases idx with
            | zero => simpa [hpB] using BlocksChain.cons hd hpB hrestB
            | succ idx' => exact ihB idx' (by simpa using hlt) hrestB
      have hsub := hgen hinv.blocks rq hrqLt hinv.hchain
      exact (blocksChain_pos_mono hsub (fun x hx => hinv.hvalid x (List.mem_of_mem_drop hx))).1
    · rw [(hinv.tokPos_eq kq).2 (hrqDef ▸ (by omega : rq = hinv.blocks.length))]
      exact Nat.le_refl _
  exact ⟨hdiv2, hnp, hallVs⟩

theorem TokStreamInv.tokBnd_step_pos {cx : Ctx} {cs : Array Nat} {first : Bool} {vs : List (Nat × Bool)}
    {els : List Element} {toks : List Token} (hinv : TokStreamInv cx cs first vs els toks)
    {k : Nat} (hk : k < toks.length) :
    tokBnd els toks k < tokBnd els toks (k + 1) := by
  have hget : toks[k]? = some toks[k] := List.getElem?_eq_getElem hk
  cases hv : toks[k].virt with
  | some why =>
    obtain ⟨hb1, _, hb2, _, _⟩ := hinv.tokBnd_virt hget hv
    omega
  | none =>
    obtain ⟨hr, hdiv2, _, _, _, hb2, _⟩ := hinv.tokBnd_real hget hv
    have hbValid := hinv.hvalid (hinv.blocks[_]'hr) (List.getElem_mem hr)
    have hpLeI := chainEls_le hbValid.1 (fun e he => (hbValid.2.1 e he).1)
    have hiLtJ := hbValid.2.2.2.2.1
    omega

theorem TokStreamInv.tokBnd_mono_lt {cx : Ctx} {cs : Array Nat} {first : Bool} {vs : List (Nat × Bool)}
    {els : List Element} {toks : List Token} (hinv : TokStreamInv cx cs first vs els toks)
    {i j : Nat} (hij : i < j) (hj : j ≤ toks.length) :
    tokBnd els toks i < tokBnd els toks j := by
  induction j with
  | zero => omega
  | succ j' ih =>
    by_cases hij' : i < j'
    · exact Nat.lt_trans (ih hij' (by omega)) (hinv.tokBnd_step_pos (by omega))
    · have hiEq : i = j' := by omega
      subst hiEq
      exact hinv.tokBnd_step_pos (by omega)

theorem TokStreamInv.tokBnd_le_iff {cx : Ctx} {cs : Array Nat} {first : Bool} {vs : List (Nat × Bool)}
    {els : List Element} {toks : List Token} (hinv : TokStreamInv cx cs first vs els toks)
    {i j : Nat} (hi : i ≤ toks.length) (hj : j ≤ toks.length) :
    tokBnd els toks i ≤ tokBnd els toks j ↔ i ≤ j := by
  constructor
  · intro hle
    by_cases hij : i ≤ j
    · exact hij
    · have := hinv.tokBnd_mono_lt (show j < i from by omega) hi
      omega
  · intro hij
    by_cases hlt : i < j
    · exact Nat.le_of_lt (hinv.tokBnd_mono_lt hlt hj)
    · have heq : i = j := by omega
      subst heq; exact Nat.le_refl _

theorem TokStreamInv.tokBnd_inj {cx : Ctx} {cs : Array Nat} {first : Bool} {vs : List (Nat × Bool)}
    {els : List Element} {toks : List Token} (hinv : TokStreamInv cx cs first vs els toks)
    {i j : Nat} (hi : i ≤ toks.length) (hj : j ≤ toks.length)
    (heq : tokBnd els toks i = tokBnd els toks j) : i = j :=
  Nat.le_antisymm
    ((hinv.tokBnd_le_iff hi hj).mp (Nat.le_of_eq heq))
    ((hinv.tokBnd_le_iff hj hi).mp (Nat.le_of_eq heq.symm))

theorem TokStreamInv.tokenSpan_eq_synSpanOf (hok : parseTablesOk = true)
    {cx : Ctx} {cs : Array Nat} (hcp : ∀ c ∈ cs.toList, c ≤ 0x10FFFF)
    {first : Bool} {vs : List (Nat × Bool)}
    {els : List Element} {toks : List Token} (hinv : TokStreamInv cx cs first vs els toks)
    {i j : Nat} (hij : i ≤ j) (hj : j ≤ toks.length) :
    Ecma.Grammar.tokenSpan els toks i j = synSpanOf cs first cx (tokBnd els toks i) (tokBnd els toks j) := by
  have hi : i ≤ toks.length := Nat.le_trans hij hj
  unfold Ecma.Grammar.tokenSpan synSpanOf
  dsimp only
  generalize haEq : (toks.take i).countP (·.virt.isNone) = a
  generalize hbEq : (toks.take j).countP (·.virt.isNone) = b
  have haDef : a = (toks.take i).countP (·.virt.isNone) := haEq.symm
  have hbDef : b = (toks.take j).countP (·.virt.isNone) := hbEq.symm
  have haLeB : a ≤ b := by
    have : toks.take j = toks.take i ++ (toks.drop i).take (j - i) := by
      conv => lhs; rw [show j = i + (j - i) from by omega, List.take_add]
    rw [hbDef, this, List.countP_append, ← haDef]
    omega
  have hbLeLen : b ≤ hinv.blocks.length := hbDef ▸ hinv.countP_le_blocks j
  have haLeLen : a ≤ hinv.blocks.length := Nat.le_trans haLeB hbLeLen
  have hbiDiv : (tokBnd els toks i) / 2 = tokPos els toks i := by
    unfold tokBnd; split <;> omega
  have hbjDiv : (tokBnd els toks j) / 2 = tokPos els toks j := by
    unfold tokBnd; split <;> omega
  rw [hinv.filter_isToken_eq, hbiDiv, hbjDiv]
  have ⟨_, hidx, hlast, hnil⟩ := blocksChain_pos_mono hinv.hchain hinv.hvalid
  by_cases hab : a < b
  · have haLt : a < hinv.blocks.length := Nat.lt_of_lt_of_le hab hbLeLen
    have hbm1Lt : b - 1 < hinv.blocks.length := by omega
    have hpi : tokPos els toks i = (hinv.blocks[a]'haLt).p := by
      simpa only [haEq] using (hinv.tokPos_eq i).1 (haDef ▸ haLt)
    have hpj : tokPos els toks j = (hinv.blocks[b - 1]'hbm1Lt).tokEl.j := by
      by_cases hbLt : b < hinv.blocks.length
      · have h1 : tokPos els toks j = (hinv.blocks[b]'hbLt).p := by
          simpa only [hbEq] using (hinv.tokPos_eq j).1 (hbDef ▸ hbLt)
        have ⟨hprev, _⟩ := hidx b hbLt
        have hne0 : b ≠ 0 := by omega
        simp only [beq_iff_eq, hne0, ↓reduceIte] at hprev
        exact h1.trans hprev.symm
      · have hbEqL : b = hinv.blocks.length := by omega
        have h1 := (hinv.tokPos_eq j).2 (hbDef ▸ hbEqL)
        have hlastEq := hlast (by intro hn; rw [hn] at haLt; exact nomatch haLt)
        exact h1.trans (by simpa [hbEqL] using hlastEq.symm)
    have hbA := hinv.hvalid (hinv.blocks[a]'haLt) (List.getElem_mem haLt)
    have hskA := (trivia_eq_skip hok hcp).mp hbA.2.2.2.1
    have hpLtJ : (hinv.blocks[a]'haLt).p < (hinv.blocks[b - 1]'hbm1Lt).tokEl.j := by
      have hmono : ∀ a0 u (ha0 : a0 < hinv.blocks.length) (hu : u < hinv.blocks.length), a0 ≤ u →
          (hinv.blocks[a0]'ha0).p ≤ (hinv.blocks[u]'hu).p := by
        intro a0 u ha0 hu hau
        induction u with
        | zero =>
          have haZ : a0 = 0 := by omega
          subst haZ; exact Nat.le_refl _
        | succ u' ih =>
          by_cases hau' : a0 ≤ u'
          · have hu'Lt : u' < hinv.blocks.length := by omega
            have ⟨hprev, _⟩ := hidx (u' + 1) hu
            have ⟨_, hltU'⟩ := hidx u' hu'Lt
            simp only [Nat.add_one_sub_one, beq_iff_eq, Nat.succ_ne_zero, ↓reduceIte] at hprev
            have := ih hu'Lt hau'
            omega
          · have haEqU : a0 = u' + 1 := by omega
            subst haEqU; exact Nat.le_refl _
      have hle1 := hmono a (b - 1) haLt hbm1Lt (by omega)
      have ⟨_, hltBm1⟩ := hidx (b - 1) hbm1Lt
      omega
    simp only [hab, ↓reduceIte, hpi, hpj, gt_iff_lt, hpLtJ, hskA,
      List.getElem?_map, List.getElem?_eq_getElem haLt, Option.map_some, Option.getD_some,
      List.getElem?_eq_getElem hbm1Lt]
  · have habEq : a = b := by omega
    have hpEq : tokPos els toks i = tokPos els toks j := by
      unfold tokPos; dsimp only; rw [← haDef, ← hbDef, habEq]
    simp only [hab, ↓reduceIte, ← hpEq, gt_iff_lt, Nat.lt_irrefl]
    by_cases haLt : a < hinv.blocks.length
    · have hpi : tokPos els toks i = (hinv.blocks[a]'haLt).p := by
        simpa only [haEq] using (hinv.tokPos_eq i).1 (haDef ▸ haLt)
      have hbA := hinv.hvalid (hinv.blocks[a]'haLt) (List.getElem_mem haLt)
      have hskA := (trivia_eq_skip hok hcp).mp hbA.2.2.2.1
      have hiLtSz : (hinv.blocks[a]'haLt).tokEl.i < cs.size :=
        Nat.lt_of_lt_of_le hbA.2.2.2.2.1 hbA.2.2.2.2.2.1
      simp only [hpi, hskA, hiLtSz, ↓reduceIte,
        List.getElem?_map, List.getElem?_eq_getElem haLt, Option.map_some, Option.getD_some]
    · have haEqLen : a = hinv.blocks.length := by omega
      have hpi : tokPos els toks i = hinv.endPos := (hinv.tokPos_eq i).2 (haDef ▸ haEqLen)
      have hskEnd := (trivia_eq_skip hok hcp).mp hinv.hendTriv
      have hgetNone : (hinv.blocks.map (·.tokEl))[a]? = none :=
        List.getElem?_eq_none (by simp [haEqLen])
      have hlastEnd : (((hinv.blocks.map (·.tokEl)).getLast?.map (·.j)).getD 0) = hinv.endPos := by
        cases hblks : hinv.blocks with
        | nil => simp [(hnil hblks).symm]
        | cons b0 bs =>
          have hne : (b0 :: bs) ≠ [] := List.cons_ne_nil _ _
          have hlastEq := hlast (by rw [hblks]; exact hne)
          simp only [List.getLast?_map, List.getLast?_eq_some_getLast hne, Option.map_some, Option.getD_some,
            List.getLast_eq_getElem]
          have hgetEq : (b0 :: bs)[(b0 :: bs).length - 1] = hinv.blocks[hinv.blocks.length - 1]'(by rw [hblks]; simp) := by
            apply Option.some.inj
            rw [← List.getElem?_eq_getElem (by simp), ← List.getElem?_eq_getElem (by rw [hblks]; simp)]
            simp only [hblks]
          rw [hgetEq]; exact hlastEq
      simp only [hpi, hskEnd, Nat.lt_irrefl, ↓reduceIte, hgetNone, Option.map_none, Option.getD_none, hlastEnd]

theorem TokStreamInv.pastVirt_eq {cx : Ctx} {cs : Array Nat} {first : Bool} {vs : List (Nat × Bool)}
    {els : List Element} {toks : List Token} (hinv : TokStreamInv cx cs first vs els toks)
    {i : Nat} (hi : i ≤ toks.length) :
    pastVirt toks i ≤ toks.length ∧
    (∀ tok, toks[pastVirt toks i]? = some tok → tok.virt = none) ∧
    tokBnd els toks (pastVirt toks i) = SynLook vs (tokBnd els toks i) := by
  unfold pastVirt SynLook
  rcases opt_none_or_some toks[i]? with hnone | ⟨tok, hget⟩
  · have hiEq : i = toks.length := Nat.le_antisymm hi (List.getElem?_eq_none_iff.mp hnone)
    subst hiEq
    have hnp := hinv.tokBnd_end.2.1
    simp [List.drop_length, hnp]
  · have hiLt : i < toks.length := (List.getElem?_eq_some_iff.mp hget).1
    rw [List.drop_eq_getElem_cons hiLt]
    have hval : toks[i] = tok := Option.some.inj ((List.getElem?_eq_getElem hiLt).symm.trans hget)
    rw [hval]
    cases hv : tok.virt with
    | none =>
      obtain ⟨_, _, hnp, _, _, _, _⟩ := hinv.tokBnd_real hget hv
      simp only [List.takeWhile_cons, hv, Option.isSome_none, Bool.false_eq_true, ↓reduceIte,
        List.length_nil, Nat.add_zero, hnp]
      exact ⟨hi, fun t ht => by rw [hget] at ht; injection ht with e; exact e ▸ hv, trivial⟩
    | some why =>
      obtain ⟨hbndI, hpend, hbndSucc, _, _⟩ := hinv.tokBnd_virt hget hv
      have hnextNone : ((toks.drop (i + 1)).takeWhile (·.virt.isSome)) = [] := by
        rcases opt_none_or_some toks[i + 1]? with hn2 | ⟨tok2, hg2⟩
        · rw [List.drop_eq_nil_of_le (List.getElem?_eq_none_iff.mp hn2)]; rfl
        · have hi1Lt : i + 1 < toks.length := (List.getElem?_eq_some_iff.mp hg2).1
          rw [List.drop_eq_getElem_cons hi1Lt]
          have hv2 : toks[i + 1] = tok2 := Option.some.inj ((List.getElem?_eq_getElem hi1Lt).symm.trans hg2)
          rw [hv2]
          rcases hinv.hasi.1 i tok tok2 hget hg2 with hv1 | hv2None
          · rw [hv] at hv1; cases hv1
          · simp [hv2None]
      simp only [List.takeWhile_cons, hv, Option.isSome_some, ↓reduceIte, hnextNone,
        List.length_singleton, hpend]
      refine ⟨by omega, fun t ht => ?_, hbndSucc.trans (congrArg (· + 1) hbndI.symm)⟩
      rcases hinv.hasi.1 i tok t hget ht with hv1 | hv2None
      · rw [hv] at hv1; cases hv1
      · exact hv2None

theorem TokStreamInv.noLT_iff_synNoLT (hok : parseTablesOk = true)
    {cx : Ctx} {cs : Array Nat} (hcp : ∀ c ∈ cs.toList, c ≤ 0x10FFFF)
    {first : Bool} {vs : List (Nat × Bool)}
    {els : List Element} {toks : List Token} (hinv : TokStreamInv cx cs first vs els toks)
    {i : Nat} (hi : i ≤ toks.length) :
    (tokenAlphabet Ecma.Spec.gl cx Engine.Model.codePrims).noLT toks i ↔
      SynNoLT Ecma.Spec.gl cx Engine.Model.codePrims cs.toList first vs (tokBnd els toks i) := by
  dsimp only [tokenAlphabet]
  unfold SynNoLT
  rcases opt_none_or_some toks[i]? with hnone | ⟨tok, hget⟩
  · have hiEq : i = toks.length := Nat.le_antisymm hi (List.getElem?_eq_none_iff.mp hnone)
    subst hiEq
    obtain ⟨hdiv2, hnp, _⟩ := hinv.tokBnd_end
    rw [hnp]
    simp only [hnone, reduceCtorEq, false_implies, implies_true, true_iff, Bool.false_eq_true, false_or]
    exact ⟨cs.size, hinv.endLt, hdiv2 ▸ hinv.hendTriv, Or.inl (by simp)⟩
  · cases hv : tok.virt with
    | some why =>
      obtain ⟨_, hpend, _, _, _⟩ := hinv.tokBnd_virt hget hv
      have hall := List.all_eq_true.mp hinv.htoksAll tok (List.mem_of_getElem? hget)
      simp only [hv, Option.isNone_some, Bool.false_or, Bool.not_eq_true'] at hall
      rw [hpend]
      exact ⟨fun _ => Or.inl rfl, fun _ t ht => by rw [hget] at ht; injection ht with e; exact e ▸ hall⟩
    | none =>
      obtain ⟨hr, hdiv2, hnp, htokEq, _, _, _⟩ := hinv.tokBnd_real hget hv
      let blk := hinv.blocks[(toks.take i).countP (·.virt.isNone)]'hr
      have hb := hinv.hvalid blk (List.getElem_mem hr)
      have hiLtSz : blk.tokEl.i < cs.toList.length := by
        rw [Array.length_toList]; exact Nat.lt_of_lt_of_le hb.2.2.2.2.1 hb.2.2.2.2.2.1
      rw [hnp, hdiv2]
      simp only [Bool.false_eq_true, false_or]
      constructor
      · intro hnl
        have hltF : blk.lt = false := by
          have := hnl tok hget; rw [htokEq] at this; exact this
        exact ⟨blk.tokEl.i, blk.lt, hb.2.2.2.1, Or.inr hltF⟩
      · rintro ⟨k, lt, htr, hcond⟩ t ht
        rw [hget] at ht; injection ht with e; subst e
        obtain ⟨rfl, rfl⟩ := trivia_unique hok hcp hb.2.2.2.1 htr
        rcases hcond with hge | hltF
        · omega
        · rw [htokEq]; exact hltF

theorem TokStreamInv.startsWith_iff_synStarts (hok : parseTablesOk = true)
    {cx : Ctx} {cs : Array Nat} (hcp : ∀ c ∈ cs.toList, c ≤ 0x10FFFF)
    {first : Bool} {vs : List (Nat × Bool)}
    {els : List Element} {toks : List Token} (hinv : TokStreamInv cx cs first vs els toks)
    (s : Src) :
    ∀ (q : List LookItem) {i : Nat},
      lookSeqsOk synLookTermOk [q] = true →
      i ≤ toks.length →
      (StartsWith (tokenAlphabet Ecma.Spec.gl cx Engine.Model.codePrims) toks s q i ↔
        SynStarts Ecma.Spec.gl cx Engine.Model.codePrims cs.toList first vs q (tokBnd els toks i))
  | [], i, _, _ => Iff.rfl
  | .noLT :: rest, i, hokQ, hi => by
    simp only [lookSeqsOk, List.all_cons, List.all_nil, Bool.and_true, Bool.true_and] at hokQ
    dsimp only [StartsWith, tokenAlphabet, SynStarts]
    obtain ⟨hpvLe, _, hpvBnd⟩ := hinv.pastVirt_eq hi
    rw [← hpvBnd, ← hinv.noLT_iff_synNoLT hok hcp hpvLe]
    exact and_congr Iff.rfl (hinv.startsWith_iff_synStarts hok hcp s rest (by simp [lookSeqsOk, hokQ]) hi)
  | .t x :: rest, i, hokQ, hi => by
    simp only [lookSeqsOk, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true] at hokQ
    obtain ⟨hxOk, hrestOk⟩ := hokQ
    cases x with
    | cp _ => cases hxOk
    | text str b0 =>
      dsimp only [synLookTermOk] at hxOk
      cases hchars : str.toList with
      | nil => rw [hchars] at hxOk; cases hxOk
      | cons ch0 chRest =>
        rw [hchars] at hxOk
        simp only [Bool.and_eq_true, bne_iff_ne] at hxOk
        have hchNot2f : ch0.toNat ≠ 0x2F :=
          fun h => hxOk.1 (Char.ext (UInt32.eq_of_toBitVec_eq (BitVec.eq_of_toNat_eq h)))
        have hchNot7d : ch0.toNat ≠ 0x7D :=
          fun h => hxOk.2 (Char.ext (UInt32.eq_of_toBitVec_eq (BitVec.eq_of_toNat_eq h)))
        have hwChars : str.toList.map Char.toNat = ch0.toNat :: chRest.map Char.toNat := by
          rw [hchars]; rfl
        dsimp only [StartsWith, SynStarts]
        obtain ⟨hpvLe, hpvNonVirt, hpvBnd⟩ := hinv.pastVirt_eq hi
        let pv := pastVirt toks i
        have hpvDiv : (SynLook vs (tokBnd els toks i)) / 2 = (tokBnd els toks pv) / 2 := by
          rw [← hpvBnd]
        rw [hpvDiv]
        rcases opt_none_or_some toks[pv]? with hnone | ⟨tok, hget⟩
        · -- `pv = toks.length`: no real token left!
          have hpvEq : pv = toks.length := Nat.le_antisymm hpvLe (List.getElem?_eq_none_iff.mp hnone)
          have hdivEnd : (tokBnd els toks pv) / 2 = hinv.endPos := hpvEq ▸ hinv.tokBnd_end.1
          rw [hdivEnd]
          constructor
          · rintro ⟨h, hlt, hle, _⟩
            dsimp only [tokenAlphabet] at hlt
            change pv < h at hlt
            omega
          · rintro ⟨a, b, lt, _, ⟨htr, hab, hbLen, _⟩, _⟩
            obtain ⟨rfl, _⟩ := trivia_unique hok hcp hinv.hendTriv htr
            rw [Array.length_toList] at hbLen; omega
        · have hvNone : tok.virt = none := hpvNonVirt tok hget
          have hpvLt : pv < toks.length := (List.getElem?_eq_some_iff.mp hget).1
          obtain ⟨hr, hdivP, _, htokEq, hnc, hbndNext, _⟩ := hinv.tokBnd_real hget hvNone
          let blk := hinv.blocks[(toks.take pv).countP (·.virt.isNone)]'hr
          obtain ⟨_, _, _, htrBlk, habBlk, hbSzBlk, _, lg, hlgSyn, _, hscanBlk⟩ :=
            hinv.hvalid blk (List.getElem_mem hr)
          rw [hdivP]
          -- Helper characterizing singleton `tokenAlphabet.term` at `pv`:
          have htermIff : ∀ h, pv < h → h ≤ toks.length →
              ((tokenAlphabet Ecma.Spec.gl cx Engine.Model.codePrims).term s 0 (.text str b0) (slice toks pv h) ↔
                h = pv + 1 ∧ slice cs.toList blk.tokEl.i blk.tokEl.j = str.toList.map Char.toNat) := by
            intro h hlt hle
            dsimp only [tokenAlphabet]
            by_cases hh1 : h = pv + 1
            · subst hh1
              have hsc1 : slice toks pv (pv + 1) = [tok] := by
                unfold slice
                rw [Nat.add_sub_cancel_left, List.drop_eq_getElem_cons hpvLt, List.take_succ_cons, List.take_zero]
                rw [Option.some.inj ((List.getElem?_eq_getElem hpvLt).symm.trans hget)]
              rw [hsc1, htokEq]
              simp only [and_true, true_and]
              exact Iff.rfl
            · have h2 : pv + 2 ≤ h := by omega
              have hpv1Lt : pv + 1 < toks.length := by omega
              have hsc2 : ∃ t1 t2 tl, slice toks pv h = t1 :: t2 :: tl := by
                unfold slice
                obtain ⟨d, hd⟩ : ∃ d, h - pv = d + 2 := ⟨h - pv - 2, by omega⟩
                rw [hd, List.drop_eq_getElem_cons hpvLt, List.take_succ_cons,
                  List.drop_eq_getElem_cons hpv1Lt, List.take_succ_cons]
                exact ⟨_, _, _, rfl⟩
              obtain ⟨t1, t2, tl, hscEq⟩ := hsc2
              rw [hscEq]; simp [hh1]
          constructor
          · rintro ⟨h, hlt, hle, htm, hswRest⟩
            obtain ⟨rfl, htxtEq⟩ := (htermIff h hlt hle).mp htm
            have hca : cs[blk.tokEl.i]? = some ch0.toNat :=
              slice_head_getElem? habBlk hbSzBlk (htxtEq.trans hwChars)
            have hnotSB : cs[blk.tokEl.i]? ≠ some 0x2F ∧ cs[blk.tokEl.i]? ≠ some 0x7D :=
              ⟨fun h => hchNot2f (Option.some.inj (hca.symm.trans h)),
               fun h => hchNot7d (Option.some.inj (hca.symm.trans h))⟩
            obtain ⟨trDiv, hscanDiv⟩ :=
              scanTok_agree_not_slash_brace (g2 := .InputElementDiv) hok hcp hlgSyn (by decide) hnotSB hscanBlk
            have hrestSyn := (hinv.startsWith_iff_synStarts hok hcp s rest (by simp [lookSeqsOk, hrestOk]) (Nat.succ_le_of_lt hpvLt)).mp hswRest
            rw [hbndNext] at hrestSyn
            exact ⟨blk.tokEl.i, blk.tokEl.j, blk.lt, trDiv, hscanDiv, hnc, htxtEq, hrestSyn⟩
          · rintro ⟨a, b, lt, trDiv, hscanDiv, _, htxtEq, hsynRest⟩
            obtain ⟨rfl, rfl⟩ := trivia_unique hok hcp htrBlk hscanDiv.1
            have hbSz : b ≤ cs.size := by simpa using hscanDiv.2.2.1
            have hca : cs[blk.tokEl.i]? = some ch0.toNat :=
              slice_head_getElem? hscanDiv.2.1 hbSz (htxtEq.trans hwChars)
            have hnotSB : cs[blk.tokEl.i]? ≠ some 0x2F ∧ cs[blk.tokEl.i]? ≠ some 0x7D :=
              ⟨fun h => hchNot2f (Option.some.inj (hca.symm.trans h)),
               fun h => hchNot7d (Option.some.inj (hca.symm.trans h))⟩
            obtain ⟨trLg, hscanLg⟩ :=
              scanTok_agree_not_slash_brace (g1 := .InputElementDiv) hok hcp (by decide) hlgSyn hnotSB hscanDiv
            obtain ⟨_, rfl, _⟩ := scanTok_span_unique hok hcp hscanBlk hscanLg
            rw [← hbndNext] at hsynRest
            have hswRest := (hinv.startsWith_iff_synStarts hok hcp s rest (by simp [lookSeqsOk, hrestOk]) (Nat.succ_le_of_lt hpvLt)).mpr hsynRest
            exact ⟨pv + 1, Nat.lt_succ_self pv, Nat.succ_le_of_lt hpvLt,
              (htermIff (pv + 1) (Nat.lt_succ_self pv) (Nat.succ_le_of_lt hpvLt)).mpr ⟨rfl, htxtEq⟩, hswRest⟩

/-! ### Syntactic skeleton equivalence (`SameSynSkeleton`) for `NonStrictOk` -/

inductive ListRel {α β : Type} (R : α → β → Prop) : List α → List β → Prop where
  | nil : ListRel R [] []
  | cons {a : α} {b : β} {as : List α} {bs : List β} : R a b → ListRel R as bs → ListRel R (a :: as) (b :: bs)

mutual
inductive SameSynSkeleton : Tree → Tree → Prop where
  | leaf (i j : Nat) : SameSynSkeleton (.leaf i j) (.leaf i j)
  | lex (k : Nat) {t1 t2 : Tree} : t1.nt? = t2.nt? → SameSynSkeleton (.lex k t1) (.lex k t2)
  | node (n : NT) (id : Nat) (ps : List Param) (i j : Nat) {ks1 ks2 : List Tree} :
      SameSynSkeletonList ks1 ks2 →
      SameSynSkeleton (.node n id ps i j ks1) (.node n id ps i j ks2)

inductive SameSynSkeletonList : List Tree → List Tree → Prop where
  | nil : SameSynSkeletonList [] []
  | cons {t1 t2 : Tree} {ks1 ks2 : List Tree} :
      SameSynSkeleton t1 t2 → SameSynSkeletonList ks1 ks2 → SameSynSkeletonList (t1 :: ks1) (t2 :: ks2)
end

theorem SameSynSkeletonList.to_listRel {ks1 ks2 : List Tree} (h : SameSynSkeletonList ks1 ks2) :
    ListRel SameSynSkeleton ks1 ks2 :=
  match ks1, ks2, h with
  | [], [], .nil => .nil
  | _ :: _, _ :: _, .cons hd tl => .cons hd tl.to_listRel

theorem SameSynSkeleton.isLeaf_eq {t1 t2 : Tree} (h : SameSynSkeleton t1 t2) :
    t1.isLeaf = t2.isLeaf := by cases h <;> rfl

theorem SameSynSkeleton.nt?_eq {t1 t2 : Tree} (h : SameSynSkeleton t1 t2) :
    t1.nt? = t2.nt? := by
  cases h with
  | leaf _ _ => rfl
  | lex _ hnt => exact hnt
  | node _ _ _ _ _ _ => rfl

theorem SameSynSkeleton.span_eq {t1 t2 : Tree} (h : SameSynSkeleton t1 t2) :
    t1.span = t2.span := by cases h <;> rfl

mutual
theorem SameSynSkeleton.synHeight_eq {t1 t2 : Tree} (h : SameSynSkeleton t1 t2) :
    Strict.synHeight t1 = Strict.synHeight t2 :=
  match t1, t2, h with
  | .leaf _ _, .leaf _ _, .leaf _ _ => rfl
  | .lex _ _, .lex _ _, .lex _ _ => rfl
  | .node _ _ _ _ _ ks1, .node _ _ _ _ _ ks2, .node _ _ _ _ _ hks => by
    rw [Strict.synHeight, Strict.synHeight, hks.synHeightKids_eq]

theorem SameSynSkeletonList.synHeightKids_eq {ks1 ks2 : List Tree} (h : SameSynSkeletonList ks1 ks2) :
    Strict.synHeightKids ks1 = Strict.synHeightKids ks2 :=
  match ks1, ks2, h with
  | [], [], .nil => rfl
  | _ :: _, _ :: _, .cons hhd htl => by
    rw [Strict.synHeightKids, Strict.synHeightKids, hhd.isLeaf_eq, hhd.synHeight_eq, htl.synHeightKids_eq]
end

theorem SameSynSkeleton.kids_forall₂ (text : Nat → Nat → List Nat) {t1 t2 : Tree}
    (h : SameSynSkeleton t1 t2) :
    ListRel SameSynSkeleton ((Tree.view text).kids t1) ((Tree.view text).kids t2) := by
  cases h with
  | leaf _ _ => exact .nil
  | lex _ _ => exact .nil
  | node _ _ _ _ _ hks =>
    dsimp only [Tree.view]
    have hlr := hks.to_listRel
    clear hks
    induction hlr with
    | nil => exact .nil
    | cons hhd _ ihr =>
      simp only [List.filter_cons, hhd.isLeaf_eq]
      split
      · exact .cons hhd ihr
      · exact ihr

private theorem forall₂_any_eq {α : Type} {R : α → α → Prop} {xs ys : List α}
    (h : ListRel R xs ys) {f g : α → Bool}
    (hfg : ∀ x y, R x y → f x = g y) :
    xs.any f = ys.any g := by
  induction h with
  | nil => rfl
  | cons hr _ ih => simp [hfg _ _ hr, ih]

private theorem forall₂_findSome_eq {α β : Type} {R : α → α → Prop} {xs ys : List α}
    (h : ListRel R xs ys) {f g : α → Option β}
    (hfg : ∀ x y, R x y → f x = g y) :
    xs.findSome? f = ys.findSome? g := by
  induction h with
  | nil => rfl
  | cons hr _ ih =>
    simp only [List.findSome?_cons, hfg _ _ hr]
    cases g _ with
    | none => exact ih
    | some _ => rfl

private theorem listRel_append {α : Type} {R : α → α → Prop} {xs1 ys1 xs2 ys2 : List α}
    (h1 : ListRel R xs1 ys1) (h2 : ListRel R xs2 ys2) :
    ListRel R (xs1 ++ xs2) (ys1 ++ ys2) := by
  induction h1 with
  | nil => exact h2
  | cons hd _ ih => exact .cons hd ih

private theorem listRel_reverse {α : Type} {R : α → α → Prop} {xs ys : List α}
    (h : ListRel R xs ys) : ListRel R xs.reverse ys.reverse := by
  induction h with
  | nil => exact .nil
  | cons hd _ ih =>
    simp only [List.reverse_cons]
    exact listRel_append ih (.cons hd .nil)

private theorem listRel_takeWhile {α : Type} {R : α → α → Prop} {xs ys : List α}
    (h : ListRel R xs ys) {p q : α → Bool} (hpq : ∀ x y, R x y → p x = q y) :
    ListRel R (xs.takeWhile p) (ys.takeWhile q) := by
  induction h with
  | nil => exact .nil
  | @cons x y _ _ hr _ ih =>
    simp only [List.takeWhile_cons, hpq x y hr]
    cases q y with
    | false => exact .nil
    | true => exact .cons hr ih

private theorem sameSynSkeleton_oneNode (text : Nat → Nat → List Nat) (m : NT) (sp : Nat × Nat) :
    ∀ (f : Nat) {t1 t2 : Tree}, SameSynSkeleton t1 t2 →
      oneNode (Tree.view text) m sp f t1 = oneNode (Tree.view text) m sp f t2
  | 0, _, _, _ => rfl
  | f + 1, t1, t2, h => by
    unfold oneNode
    have hisA : (Tree.view text).isA t1 m = (Tree.view text).isA t2 m := by
      dsimp only [Tree.view]; rw [h.nt?_eq]
    have hsp : (Tree.view text).span t1 = (Tree.view text).span t2 := h.span_eq
    rw [hisA, hsp]
    congr 1; congr 1
    exact forall₂_any_eq (h.kids_forall₂ text) (fun _ _ hk => sameSynSkeleton_oneNode text m sp f hk)

private theorem sameSynSkeleton_directive (text : Nat → Nat → List Nat) (f : Nat) {t1 t2 : Tree}
    (h : SameSynSkeleton t1 t2) :
    directive (Tree.view text) f t1 = directive (Tree.view text) f t2 := by
  unfold directive
  have hk1 := h.kids_forall₂ text
  generalize (Tree.view text).kids t1 = ks1 at hk1 ⊢
  generalize (Tree.view text).kids t2 = ks2 at hk1 ⊢
  cases hk1 with
  | nil => rfl
  | @cons s1 s2 _ _ hs hrest1 =>
    cases hrest1 with
    | cons _ _ => rfl
    | nil =>
      dsimp only
      have hisSt : (Tree.view text).isA s1 .Statement = (Tree.view text).isA s2 .Statement := by
        dsimp only [Tree.view]; rw [hs.nt?_eq]
      rw [hisSt]
      split
      · rfl
      · have hk2 := hs.kids_forall₂ text
        generalize (Tree.view text).kids s1 = ksS1 at hk2 ⊢
        generalize (Tree.view text).kids s2 = ksS2 at hk2 ⊢
        cases hk2 with
        | nil => rfl
        | @cons es1 es2 _ _ hes hrest2 =>
          cases hrest2 with
          | cons _ _ => rfl
          | nil =>
            dsimp only
            have hisEs : (Tree.view text).isA es1 .ExpressionStatement = (Tree.view text).isA es2 .ExpressionStatement := by
              dsimp only [Tree.view]; rw [hes.nt?_eq]
            rw [hisEs]
            split
            · rfl
            · have hk3 := hes.kids_forall₂ text
              generalize (Tree.view text).kids es1 = ksE1 at hk3 ⊢
              generalize (Tree.view text).kids es2 = ksE2 at hk3 ⊢
              cases hk3 with
              | nil => rfl
              | @cons e1 e2 _ _ he hrest3 =>
                cases hrest3 with
                | cons _ _ => rfl
                | nil =>
                  dsimp only
                  have hisE : (Tree.view text).isA e1 .Expression = (Tree.view text).isA e2 .Expression := by
                    dsimp only [Tree.view]; rw [he.nt?_eq]
                  have hsp : (Tree.view text).span e1 = (Tree.view text).span e2 := he.span_eq
                  have htxt : (Tree.view text).textIs e1 = (Tree.view text).textIs e2 := by
                    funext s0; dsimp only [Tree.view]; rw [he.span_eq]
                  rw [hisE, hsp, sameSynSkeleton_oneNode text .StringLiteral _ f he, htxt]

private theorem sameSynSkeleton_prologueScan (text : Nat → Nat → List Nat) :
    ∀ (f : Nat) {t1 t2 : Tree}, SameSynSkeleton t1 t2 →
      prologueScan (Tree.view text) f t1 = prologueScan (Tree.view text) f t2
  | 0, _, _, _ => rfl
  | f + 1, t1, t2, h => by
    unfold prologueScan
    have hisA : (Tree.view text).isA t1 .StatementListItem = (Tree.view text).isA t2 .StatementListItem := by
      dsimp only [Tree.view]; rw [h.nt?_eq]
    rw [hisA]
    split
    · rw [sameSynSkeleton_directive text f h]
    · exact forall₂_findSome_eq (h.kids_forall₂ text) (fun _ _ hk => sameSynSkeleton_prologueScan text f hk)

private theorem sameSynSkeleton_bodyOf (text : Nat → Nat → List Nat) :
    ∀ (f : Nat) {t1 t2 : Tree}, SameSynSkeleton t1 t2 →
      match bodyOf (Tree.view text) f t1, bodyOf (Tree.view text) f t2 with
      | none, none => True
      | some b1, some b2 => SameSynSkeleton b1 b2
      | _, _ => False
  | 0, _, _, _ => trivial
  | f + 1, t1, t2, h => by
    unfold bodyOf
    have hisA : (Tree.view text).isA t1 .FunctionBody = (Tree.view text).isA t2 .FunctionBody := by
      dsimp only [Tree.view]; rw [h.nt?_eq]
    rw [hisA]
    cases (Tree.view text).isA t2 .FunctionBody with
    | true =>
      simp only [↓reduceIte]
      exact h
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      have hloop : ∀ {ks1 ks2 : List Tree}, ListRel SameSynSkeleton ks1 ks2 →
          match ks1.findSome? (fun k => if (Tree.view text).isIn bodyPath k then bodyOf (Tree.view text) f k else none),
                ks2.findSome? (fun k => if (Tree.view text).isIn bodyPath k then bodyOf (Tree.view text) f k else none) with
          | none, none => True
          | some b1, some b2 => SameSynSkeleton b1 b2
          | _, _ => False := by
        intro ks1 ks2 hks
        induction hks with
        | nil => trivial
        | @cons c1 c2 _ _ hc _ ih =>
          have hisIn : (Tree.view text).isIn bodyPath c1 = (Tree.view text).isIn bodyPath c2 := by
            unfold NodeView.isIn; dsimp only [Tree.view]; rw [hc.nt?_eq]
          simp only [List.findSome?_cons, hisIn]
          cases (Tree.view text).isIn bodyPath c2 with
          | false => exact ih
          | true =>
            simp only [↓reduceIte]
            have hb := sameSynSkeleton_bodyOf text f hc
            cases h1 : bodyOf (Tree.view text) f c1 with
            | none =>
              cases h2 : bodyOf (Tree.view text) f c2 with
              | none => exact ih
              | some _ => rw [h1, h2] at hb; exact nomatch hb
            | some b1 =>
              cases h2 : bodyOf (Tree.view text) f c2 with
              | none => rw [h1, h2] at hb; exact nomatch hb
              | some b2 => rw [h1, h2] at hb; exact hb
      exact hloop (h.kids_forall₂ text)

private theorem sameSynSkeleton_strictCode (text : Nat → Nat → List Nat) {up1 up2 : List Tree}
    (hup : ListRel SameSynSkeleton up1 up2) {t1 t2 : Tree} (ht : SameSynSkeleton t1 t2) :
    StrictCode text up1 t1 ↔ StrictCode text up2 t2 := by
  unfold StrictCode Ecma.Grammar.strictCode
  let V := Tree.view text
  have hisA_eq : ∀ {x1 x2 : Tree} (m : NT), SameSynSkeleton x1 x2 → V.isA x1 m = V.isA x2 m := by
    intro x1 x2 m hx; dsimp only [V, Tree.view]; rw [hx.nt?_eq]
  have hisIn_eq : ∀ {x1 x2 : Tree} (ns : List NT), SameSynSkeleton x1 x2 → V.isIn ns x1 = V.isIn ns x2 := by
    intro x1 x2 ns hx; unfold NodeView.isIn; dsimp only [V, Tree.view]; rw [hx.nt?_eq]
  have hprol : ∀ {x1 x2 : Tree}, SameSynSkeleton x1 x2 →
      prologueStrict V x1 = prologueStrict V x2 := by
    intro x1 x2 hx
    unfold prologueStrict
    have hst1 : prologueScan V (V.height x1) x1 = prologueScan V (Strict.synHeight x1) x1 :=
      Strict.prologueScan_tree_stab text x1 (Strict.synHeight_le_height x1) (Nat.le_refl _)
    have hst2 : prologueScan V (V.height x2) x2 = prologueScan V (Strict.synHeight x2) x2 :=
      Strict.prologueScan_tree_stab text x2 (Strict.synHeight_le_height x2) (Nat.le_refl _)
    rw [hst1, hst2, hx.synHeight_eq, sameSynSkeleton_prologueScan text _ hx]
  have hbody : ∀ {x1 x2 : Tree}, SameSynSkeleton x1 x2 →
      bodyStrict V x1 = bodyStrict V x2 := by
    intro x1 x2 hx
    unfold bodyStrict
    have hst1 : bodyOf V (V.height x1) x1 = bodyOf V (Strict.synHeight x1) x1 :=
      (Strict.bodyOf_tree_stab_and_le text x1 (Strict.synHeight_le_height x1) (Nat.le_refl _)).1
    have hst2 : bodyOf V (V.height x2) x2 = bodyOf V (Strict.synHeight x2) x2 :=
      (Strict.bodyOf_tree_stab_and_le text x2 (Strict.synHeight_le_height x2) (Nat.le_refl _)).1
    rw [hst1, hst2, hx.synHeight_eq]
    dsimp only [V]
    have hb := sameSynSkeleton_bodyOf text (Strict.synHeight x2) hx
    cases hb1 : bodyOf (Tree.view text) (Strict.synHeight x2) x1 with
    | none =>
      cases hb2 : bodyOf (Tree.view text) (Strict.synHeight x2) x2 with
      | none => rfl
      | some _ => rw [hb1, hb2] at hb; exact nomatch hb
    | some b1 =>
      cases hb2 : bodyOf (Tree.view text) (Strict.synHeight x2) x2 with
      | none => rw [hb1, hb2] at hb; exact nomatch hb
      | some b2 => rw [hb1, hb2] at hb; dsimp only [Option.any]; exact hprol hb
  have hdown : ∀ {l1 l2 : List Tree}, ListRel SameSynSkeleton l1 l2 → ∀ (s : Bool),
      strictDown V s l1 = strictDown V s l2 := by
    intro l1 l2 hl
    induction hl with
    | nil => intro _; rfl
    | @cons f1 f2 rs1 rs2 hf hrs ih =>
      intro s
      cases hrs with
      | nil =>
        dsimp only [strictDown]
        rw [hisIn_eq classForms hf]
      | @cons r1 r2 tl1 tl2 hr1 htl =>
        dsimp only [strictDown]
        have htw := listRel_takeWhile (.cons hr1 htl)
          (p := fun x => !V.isIn (functionForms ++ classForms) x)
          (q := fun x => !V.isIn (functionForms ++ classForms) x)
          (fun x y hxy => by rw [hisIn_eq _ hxy])
        have hany := forall₂_any_eq htw (f := fun x => V.isA x .ClassElementName)
          (g := fun x => V.isA x .ClassElementName) (fun x y hxy => hisA_eq _ hxy)
        rw [hisIn_eq classForms hf, hisIn_eq functionForms hf, hisA_eq .MethodDefinition hf,
            hany, hbody hf, ih s, ih (s || bodyStrict V f2)]
  have hpath := listRel_append (listRel_reverse hup) (.cons ht .nil)
  generalize hp1 : up1.reverse ++ [t1] = l1 at hpath
  generalize hp2 : up2.reverse ++ [t2] = l2 at hpath
  cases hpath with
  | nil => rfl
  | @cons rt1 rt2 p1 p2 hrt hp =>
    dsimp only
    have htop : (if V.isA rt1 .Module then true else if V.isA rt1 .Script then prologueStrict V rt1 else V.isIn bodyGoals rt1 && bodyStrict V rt1) =
        (if V.isA rt2 .Module then true else if V.isA rt2 .Script then prologueStrict V rt2 else V.isIn bodyGoals rt2 && bodyStrict V rt2) := by
      rw [hisA_eq .Module hrt, hisA_eq .Script hrt, hprol hrt, hisIn_eq bodyGoals hrt, hbody hrt]
    rw [htop, hdown (.cons hrt hp)]

mutual
theorem sameSynSkeleton_nonStrictOk (G : Ecma.GrammarCtx) {src : List Nat}
    {els1 els2 : List Element} {toks1 toks2 : List Token}
    (htxt : Ecma.Grammar.tokenText src els1 toks1 = Ecma.Grammar.tokenText src els2 toks2)
    {up1 up2 : List Tree} {t1 t2 : Tree}
    (hup : ListRel SameSynSkeleton up1 up2)
    (ht : SameSynSkeleton t1 t2) :
    NonStrictOk Ecma.Spec.gl (G.StrictIn src els1 toks1) up1 t1 ↔
      NonStrictOk Ecma.Spec.gl (G.StrictIn src els2 toks2) up2 t2 :=
  match t1, t2, ht with
  | .leaf _ _, .leaf _ _, .leaf _ _ => Iff.rfl
  | .lex _ _, .lex _ _, .lex _ _ => Iff.rfl
  | .node n id ps i j ks1, .node _ _ _ _ _ ks2, .node _ _ _ _ _ hks => by
    unfold NonStrictOk
    have hstrIff : G.StrictIn src els1 toks1 up1 (.node n id ps i j ks1) ↔
        G.StrictIn src els2 toks2 up2 (.node n id ps i j ks2) := by
      unfold Ecma.GrammarCtx.StrictIn
      rw [htxt]
      exact or_congr Iff.rfl (sameSynSkeleton_strictCode _ hup (.node n id ps i j hks))
    exact and_congr (imp_congr_right fun _ => not_congr hstrIff)
      (sameSynSkeleton_nonStrictOkAll G htxt (.cons (.node n id ps i j hks) hup) hks)

theorem sameSynSkeleton_nonStrictOkAll (G : Ecma.GrammarCtx) {src : List Nat}
    {els1 els2 : List Element} {toks1 toks2 : List Token}
    (htxt : Ecma.Grammar.tokenText src els1 toks1 = Ecma.Grammar.tokenText src els2 toks2)
    {up1 up2 : List Tree} {ks1 ks2 : List Tree}
    (hup : ListRel SameSynSkeleton up1 up2)
    (hks : SameSynSkeletonList ks1 ks2) :
    NonStrictOk.all Ecma.Spec.gl (G.StrictIn src els1 toks1) up1 ks1 ↔
      NonStrictOk.all Ecma.Spec.gl (G.StrictIn src els2 toks2) up2 ks2 :=
  match ks1, ks2, hks with
  | [], [], .nil => Iff.rfl
  | _ :: _, _ :: _, .cons hd tl => by
    dsimp only [NonStrictOk.all]
    exact and_congr
      (sameSynSkeleton_nonStrictOk G htxt hup hd)
      (sameSynSkeleton_nonStrictOkAll G htxt hup tl)
end

/-! ## Section 5: Bidirectional tree bridge and `syntax_run_some_spec` / `syntax_run_none_spec` -/

/-- One matched token step along a `DTree`: either a virtual `;` at `p`, or a real token scanned from `p`. -/
inductive RawStep where
  | virt (p : Nat)
  | real (p a b : Nat) (lt : Bool) (lg : NT) (tr : Tree)

def RawStep.nextBnd : RawStep → Nat
  | .virt p => 2 * p + 1
  | .real _ _ b _ _ _ => 2 * b

def rawBndAt (start : Nat) : List RawStep → Nat → Nat
  | _, 0 => start
  | [], _ + 1 => start
  | st :: rs, u + 1 => rawBndAt st.nextBnd rs u

inductive RawChain (cx : Ctx) (cs : Array Nat) (first : Bool) (vs : List (Nat × Bool)) :
    Nat → Nat → List RawStep → Prop where
  | nil (i : Nat) : RawChain cx cs first vs i i []
  | virt {p j : Nat} {rs : List RawStep} :
      (p, vsParen vs p) ∈ vs →
      RawChain cx cs first vs (2 * p + 1) j rs →
      RawChain cx cs first vs (2 * p) j (.virt p :: rs)
  | real {i p a b j : Nat} {lt : Bool} {lg : NT} {tr : Tree} {rs : List RawStep} :
      p = i / 2 →
      vsPending vs i = false →
      noCross vs p b = true →
      isSynLexGoal lg = true →
      ScanTok Ecma.Spec.gl cx Engine.Model.codePrims cs.toList first lg p a b lt tr →
      RawChain cx cs first vs (2 * b) j rs →
      RawChain cx cs first vs i j (.real p a b lt lg tr :: rs)

theorem RawChain.append {cx : Ctx} {cs : Array Nat} {first : Bool} {vs : List (Nat × Bool)}
    {a b c : Nat} {r1 r2 : List RawStep}
    (h1 : RawChain cx cs first vs a b r1) (h2 : RawChain cx cs first vs b c r2) :
    RawChain cx cs first vs a c (r1 ++ r2) := by
  induction h1 with
  | nil _ => exact h2
  | virt hm _ ih => exact .virt hm (ih h2)
  | real hp hnp hnc hlg hsc _ ih => exact .real hp hnp hnc hlg hsc (ih h2)

theorem RawChain.rawBndAt_end {cx : Ctx} {cs : Array Nat} {first : Bool} {vs : List (Nat × Bool)}
    {i j : Nat} {rs : List RawStep} (h : RawChain cx cs first vs i j rs) :
    rawBndAt i rs rs.length = j := by
  induction h with
  | nil _ => rfl
  | virt _ _ ih => exact ih
  | real _ _ _ _ _ _ ih => exact ih

theorem rawBndAt_append (start : Nat) (r1 r2 : List RawStep) (u : Nat) :
    rawBndAt start (r1 ++ r2) u =
      if u ≤ r1.length then rawBndAt start r1 u
      else rawBndAt (rawBndAt start r1 r1.length) r2 (u - r1.length) := by
  induction r1 generalizing start u with
  | nil => cases u <;> simp [rawBndAt]
  | cons st rs ih =>
    cases u with
    | zero => simp [rawBndAt]
    | succ u' =>
      simp only [List.cons_append, rawBndAt, List.length_cons]
      rw [ih st.nextBnd u']
      by_cases hle : u' ≤ rs.length
      · simp [hle, Nat.succ_le_succ hle]
      · have hnle : ¬ (u' + 1 ≤ rs.length + 1) := by omega
        simp [hle, hnle, show u' + 1 - (rs.length + 1) = u' - rs.length from by omega]

theorem RawChain.bound (hok : parseTablesOk = true) {cx : Ctx} {cs : Array Nat}
    (hcp : ∀ c ∈ cs.toList, c ≤ 0x10FFFF) {first : Bool} {vs : List (Nat × Bool)}
    (hvs : ∀ pb ∈ vs, pb.1 ≤ cs.size) {i j : Nat} {rs : List RawStep}
    (h : RawChain cx cs first vs i j rs) :
    i ≤ j ∧ (rs ≠ [] → i < j ∧ j ≤ 2 * cs.size + 1) := by
  induction h with
  | nil _ => exact ⟨Nat.le_refl _, fun hne => absurd rfl hne⟩
  | @virt p j rs0 hm hr ih =>
    have hpLe := hvs (p, vsParen vs p) hm
    rcases rs0 with _ | ⟨hd, tl⟩
    · generalize hs0 : 2 * p + 1 = s0 at hr
      cases hr
      exact ⟨by omega, fun _ => ⟨by omega, by omega⟩⟩
    · have hltR := (ih.2 (List.cons_ne_nil _ _)).1
      have hleR := (ih.2 (List.cons_ne_nil _ _)).2
      exact ⟨by omega, fun _ => ⟨by omega, hleR⟩⟩
  | @real i0 p a b j lt lg tr rs0 hp _ _ _ hsc hr ih =>
    subst hp
    have hsk := (trivia_eq_skip hok hcp).mp hsc.1
    have hik := (skip_spec (cx := cx) hok hcp first (i0 / 2)).1
    rw [hsk] at hik
    have hab := hsc.2.1
    have hbSz : b ≤ cs.size := by simpa using hsc.2.2.1
    have hilt2b : i0 < 2 * b := by omega
    rcases rs0 with _ | ⟨hd, tl⟩
    · generalize hs0 : 2 * b = s0 at hr
      cases hr
      exact ⟨by omega, fun _ => ⟨by omega, by omega⟩⟩
    · have hltR := (ih.2 (List.cons_ne_nil _ _)).1
      have hleR := (ih.2 (List.cons_ne_nil _ _)).2
      exact ⟨by omega, fun _ => ⟨by omega, hleR⟩⟩

/-- How a single `RawStep` matches `toks[idx]`. -/
def StepMatchesTok (cs : Array Nat) (toks : List Token) (idx : Nat) : RawStep → Prop
  | .virt _ => ∃ tok why, toks[idx]? = some tok ∧ tok.text = ";".toList.map Char.toNat ∧
      tok.lt = false ∧ tok.virt = some why
  | .real _ a b lt _ _ => toks[idx]? = some ⟨slice cs.toList a b, lt, none⟩

/-- Every `LexicalDeclaration` derivation consumes at least one token (`i < j`). -/
private theorem lexicalDeclaration_pos (hok : parseTablesOk = true) {cs : Array Nat}
    (hcp : ∀ c ∈ cs.toList, c ≤ 0x10FFFF) {first : Bool} {cx : Ctx} {stamp : Nat}
    {vs : List (Nat × Bool)} (hvs : ∀ pb ∈ vs, pb.1 ≤ cs.size)
    {ps : List Param} {i j : Nat} {dt : DTree}
    (hd : (synAlphaSpec hok hcp first cx stamp vs hvs).PlainDerives .LexicalDeclaration ps i j dt) :
    i < j := by
  let isTermFirstNt : NT → Bool := fun x =>
    x == .LetOrConst || x == .UsingDeclaration || x == .CoverAwaitExpressionAndAwaitUsingDeclarationHead
  let isTrackedNt : NT → Bool := fun x =>
    x == .LexicalDeclaration || x == .AwaitUsingDeclaration || isTermFirstNt x
  have hcertLD :
      (((glData.rulesOf .syntactic).all fun r =>
          !(r.lhs == .LexicalDeclaration) ||
          (writtenAlts r).all fun a => match a.rhs with
            | .sym (.nt m _) false :: _ => m == .LetOrConst || m == .UsingDeclaration || m == .AwaitUsingDeclaration
            | _ => false) &&
        ((glData.rulesOf .syntactic).all fun r =>
          !(r.lhs == .AwaitUsingDeclaration) ||
          (writtenAlts r).all fun a => match a.rhs with
            | .sym (.nt .CoverAwaitExpressionAndAwaitUsingDeclarationHead _) false :: _ => true
            | _ => false) &&
        ((glData.rulesOf .syntactic).all fun r =>
          !(isTermFirstNt r.lhs) ||
          (writtenAlts r).all fun a => match a.rhs with
            | .sym (.t _) false :: _ => true
            | _ => false) &&
        (glData.blocks.all fun b => match b.kind with
          | .overlay sec _ _ => !(overlayGrammar sec == .syntactic) || b.rules.all (fun r => !(isTrackedNt r.lhs))
          | _ => true)) = true := by decide
  have hc1 := (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp hcertLD).1).1).1
  have hc2 := (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp hcertLD).1).1).2
  have hc3 := (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp hcertLD).1).2
  have hc4 := (Bool.and_eq_true_iff.mp hcertLD).2
  have hmemZip1 : ∀ {α : Type} {x : α} {idx : Nat} {xs : List α} {k : Nat},
      (x, idx) ∈ xs.zipIdx k → x ∈ xs := by
    intro α x idx xs; induction xs with
    | nil => intro _ h; cases h
    | cons y tl ih =>
      intro k h; rcases List.mem_cons.mp h with heq | htl
      · exact (Prod.mk.inj heq).1 ▸ List.mem_cons_self ..
      · exact List.mem_cons_of_mem _ (ih htl)
  have haltsProp : ∀ (target : NT) (pred : Alt → Bool),
      isTrackedNt target = true →
      ((glData.rulesOf .syntactic).all fun r => !(r.lhs == target) || (writtenAlts r).all pred) = true →
      ∀ s ∈ Ecma.Spec.gl.alts cx .syntactic target, pred s.alt = true := by
    intro target pred htr hpR s hs
    rw [← glData_eq] at hs
    unfold GL.alts at hs
    have hnoOv : ∀ (bs : List (Block × OverlayMode)) (acc : List Src),
        (∀ pm ∈ bs, pm.1 ∈ glData.blocks ∧ ∃ sec md cd, pm.1.kind = .overlay sec md cd ∧ overlayGrammar sec == .syntactic) →
        bs.foldl (fun acc (b, m) =>
          match b.rules.find? (·.lhs == target), m with
          | none, _ => acc
          | some r, .extend => acc ++ (srcsOf .annexB r).filter fun s => !acc.any (·.alt == s.alt)
          | some r, .replace => srcsOf .annexB r) acc = acc := by
      intro bs; induction bs with
      | nil => intro acc _; rfl
      | cons hd tl ih =>
        intro acc hbs
        obtain ⟨hbMem, sec, md, cd, hbk, hog⟩ := hbs hd (List.mem_cons_self ..)
        have hbOk := List.all_eq_true.mp hc4 hd.1 hbMem
        rw [hbk] at hbOk; simp only [hog, Bool.not_true, Bool.false_or] at hbOk
        have hfn : hd.1.rules.find? (·.lhs == target) = none := by
          rw [List.find?_eq_none]; intro r hr heq
          have hrOk := List.all_eq_true.mp hbOk r hr
          have heq' : r.lhs = target := beq_iff_eq.mp heq
          rw [heq', htr] at hrOk; cases hrOk
        simp only [List.foldl_cons, hfn]
        exact ih acc (fun pm hpm => hbs pm (List.mem_cons_of_mem _ hpm))
    have hovEq := hnoOv (glData.overlays cx .syntactic) (glData.pinned .syntactic target) (by
      intro pm hpm; unfold GL.overlays at hpm; split at hpm
      · cases hpm
      · obtain ⟨b, hb, hfb⟩ := List.mem_filterMap.mp hpm
        cases hbk : b.kind with
        | main | supplemental _ => rw [hbk] at hfb; cases hfb
        | overlay sec md cd =>
          rw [hbk] at hfb; dsimp only at hfb
          split at hfb
          · rename_i hcond; cases hfb; exact ⟨hb, sec, md, cd, hbk, (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp hcond).1).1⟩
          · cases hfb)
    have hsPin : s ∈ glData.pinned .syntactic target := Eq.mp (congrArg (s ∈ ·) hovEq) hs
    unfold GL.pinned at hsPin
    rcases opt_none_or_some ((glData.rulesOf .syntactic).find? (·.lhs == target)) with hn | ⟨r, hr⟩
    · rw [hn] at hsPin; simp [baseGrammar] at hsPin
    · rw [hr] at hsPin
      have hrMem := List.mem_of_find?_eq_some hr
      have hrEq : (r.lhs == target) = true := @List.find?_some _ (fun (x : Rule) => x.lhs == target) _ _ hr
      have hrAll := List.all_eq_true.mp hpR r hrMem
      simp only [hrEq, Bool.not_true, Bool.false_or] at hrAll
      simp only [srcsOf, List.mem_map] at hsPin
      obtain ⟨⟨a0, _⟩, hz, rfl⟩ := hsPin
      exact List.all_eq_true.mp hrAll a0 (hmemZip1 hz)
  let S := synAlphaSpec hok hcp first cx stamp vs hvs
  have htermFirstPos : ∀ {m : NT} {ps0 : List Param} {a b : Nat} {dt0 : DTree},
      isTermFirstNt m = true → S.PlainDerives m ps0 a b dt0 → a < b := by
    intro m ps0 a b dt0 hmTF hd0
    cases hd0 with
    | node s2 hs2Mem _ _ _ hsw2 =>
      have hs2Spec : s2 ∈ Ecma.Spec.gl.alts cx .syntactic m := (altsOf_eq hok cx .syntactic m) ▸ hs2Mem
      have htrM : isTrackedNt m = true := by simp [isTrackedNt, hmTF]
      have hpM : ((glData.rulesOf .syntactic).all fun r => !(r.lhs == m) || (writtenAlts r).all fun a =>
          match a.rhs with | .sym (.t _) false :: _ => true | _ => false) = true := by
        rw [List.all_eq_true]
        intro r hr
        by_cases heq : (r.lhs == m) = true
        · have hmEq : r.lhs = m := beq_iff_eq.mp heq
          have hr3 := List.all_eq_true.mp hc3 r hr
          rw [hmEq, hmTF] at hr3; simpa [heq] using hr3
        · simp [heq]
      have hsh := haltsProp m _ htrM hpM s2 hs2Spec
      generalize hrhs2 : s2.alt.rhs = rhs2 at hsh hsw2
      cases rhs2 with
      | nil => cases hsh
      | cons it2 rest2 =>
        cases it2 with
        | sym sym2 o2 =>
          cases sym2 with
          | nt _ _ => cases o2 <;> cases hsh
          | t x2 =>
            cases o2 with
            | true => cases hsh
            | false =>
              cases hsw2 with
              | term ht2 hr2 =>
                have hlt1 := (S.term_bound _ _ _ _ _ ht2).1
                have hlenGe : 0 + 1 ≤ s2.alt.rhs.length := by rw [hrhs2]; simp
                have hleMid := (synSeq_bound hok hcp hvs (seqWith_to_synSeq hok hcp hvs hs2Spec
                  hlenGe (by rw [hrhs2]; rfl) hr2)).1
                omega
        | _ => cases hsh
  have hawaitPos : ∀ {ps0 : List Param} {a b : Nat} {dt0 : DTree},
      S.PlainDerives .AwaitUsingDeclaration ps0 a b dt0 → a < b := by
    intro ps0 a b dt0 hdA
    cases hdA with
    | node sA hsAMem _ _ _ hswA =>
      have hsASpec : sA ∈ Ecma.Spec.gl.alts cx .syntactic .AwaitUsingDeclaration := (altsOf_eq hok cx .syntactic _) ▸ hsAMem
      have hshA := haltsProp .AwaitUsingDeclaration _ (by decide) hc2 sA hsASpec
      generalize hrhsA : sA.alt.rhs = rhsA at hshA hswA
      cases rhsA with
      | nil => cases hshA
      | cons itA restA =>
        cases itA with
        | sym symA oA =>
          cases symA with
          | t _ => cases oA <;> cases hshA
          | nt mA argsA =>
            cases oA with
            | true => cases mA <;> cases hshA
            | false =>
              have hmAEq : mA = .CoverAwaitExpressionAndAwaitUsingDeclarationHead := by
                by_cases h : mA = .CoverAwaitExpressionAndAwaitUsingDeclarationHead
                · exact h
                · simp [h] at hshA
              subst hmAEq
              have hlenGe : 0 + 1 ≤ sA.alt.rhs.length := by rw [hrhsA]; simp
              cases hswA with
              | leaf _ hlA _ _ hrA =>
                have hlt1 := (S.leaf_bound _ _ _ hlA).1
                have hle2 := (synSeq_bound hok hcp hvs (seqWith_to_synSeq hok hcp hvs hsASpec hlenGe (by rw [hrhsA]; rfl) hrA)).1
                omega
              | nt _ hdC _ _ hrA =>
                have hlt1 := htermFirstPos (by decide) hdC
                have hle2 := (synSeq_bound hok hcp hvs (seqWith_to_synSeq hok hcp hvs hsASpec hlenGe (by rw [hrhsA]; rfl) hrA)).1
                omega
        | _ => cases hshA
  cases hd with
  | node s hsMem _ _ _ hsw =>
    have hsSpec : s ∈ Ecma.Spec.gl.alts cx .syntactic .LexicalDeclaration := (altsOf_eq hok cx .syntactic _) ▸ hsMem
    have hshapeLD := haltsProp .LexicalDeclaration _ (by decide) hc1 s hsSpec
    generalize hrhs : s.alt.rhs = rhs0 at hshapeLD hsw
    cases rhs0 with
    | nil => cases hshapeLD
    | cons it rest =>
      cases it with
      | sym sym0 o =>
        cases sym0 with
        | t _ => cases o <;> cases hshapeLD
        | nt m args =>
          cases o with
          | true => cases hshapeLD
          | false =>
            dsimp only at hshapeLD
            have hlenGe : 0 + 1 ≤ s.alt.rhs.length := by rw [hrhs]; simp
            cases hsw with
            | leaf _ hl _ _ hr =>
              have hlt1 := (S.leaf_bound _ _ _ hl).1
              have hle2 := (synSeq_bound hok hcp hvs (seqWith_to_synSeq hok hcp hvs hsSpec hlenGe (by rw [hrhs]; rfl) hr)).1
              omega
            | nt _ hdChild _ _ hr =>
              have hle2 := (synSeq_bound hok hcp hvs (seqWith_to_synSeq hok hcp hvs hsSpec hlenGe (by rw [hrhs]; rfl) hr)).1
              have hlt1 :=
                if hmA : m = .AwaitUsingDeclaration then
                  hawaitPos (hmA ▸ hdChild)
                else
                  htermFirstPos (by
                    simp only [Bool.or_eq_true, beq_iff_eq] at hshapeLD
                    rcases hshapeLD with (rfl | rfl) | rfl
                    · decide
                    · decide
                    · exact absurd rfl hmA) hdChild
              omega
      | _ => cases hshapeLD

theorem RawChain.even_end_last_not_virt {cx : Ctx} {cs : Array Nat} {first : Bool} {vs : List (Nat × Bool)}
    {i j : Nat} {rs : List RawStep}
    (h : RawChain cx cs first vs i j rs) (hne : rs ≠ []) (heven : j % 2 = 0) :
    ∃ p a b lt lg tr, rs[rs.length - 1]? = some (.real p a b lt lg tr) := by
  induction h with
  | nil _ => exact absurd rfl hne
  | @virt p j rs0 _ hr ih =>
    cases rs0 with
    | nil =>
      generalize hs0 : 2 * p + 1 = s0 at hr
      cases hr
      omega
    | cons r1 rs1 =>
      simpa using ih (List.cons_ne_nil _ _) heven
  | @real _ p a b j lt lg tr rs0 _ _ _ _ _ hr ih =>
    cases rs0 with
    | nil => exact ⟨p, a, b, lt, lg, tr, rfl⟩
    | cons r1 rs1 =>
      simpa using ih (List.cons_ne_nil _ _) heven


/-! ### `SameDTreeSkeleton` and `DTreeBndsMatch` -/

mutual
inductive SameDTreeSkeleton : DTree → Nat → Tree → Prop where
  | leaf {b1 b2 : Nat} (off : Nat) :
      SameDTreeSkeleton (.leaf b1 b2) off (.leaf off (off + 1))
  | lex {m : NT} {b1 b2 : Nat} (off : Nat) {tLex : Tree} :
      tLex.nt? = some m →
      SameDTreeSkeleton (.lex m b1 b2) off (.lex off tLex)
  | node {n : NT} {id : Nat} {s : Src} {ps : List Param} {b1 b2 : Nat}
      {mask : List Bool} {dks : List DTree} {off endOff : Nat} {tks : List Tree} :
      SameDTreeSkeletonList dks off endOff tks →
      SameDTreeSkeleton (.node n id s ps b1 b2 mask dks) off (.node n id ps off endOff tks)

inductive SameDTreeSkeletonList : List DTree → Nat → Nat → List Tree → Prop where
  | nil (off : Nat) : SameDTreeSkeletonList [] off off []
  | cons {dk : DTree} {dks : List DTree} {off mid endOff : Nat} {tk : Tree} {tks : List Tree} :
      tk.span = (off, mid) →
      SameDTreeSkeleton dk off tk →
      SameDTreeSkeletonList dks mid endOff tks →
      SameDTreeSkeletonList (dk :: dks) off endOff (tk :: tks)
end

mutual
theorem SameDTreeSkeleton.span_le {dt : DTree} {off : Nat} {t : Tree}
    (h : SameDTreeSkeleton dt off t) : off ≤ t.span.2 ∧ t.span.1 = off :=
  match dt, t, h with
  | .leaf _ _, _, .leaf _ => ⟨by dsimp [Tree.span]; omega, rfl⟩
  | .lex _ _ _, _, .lex _ _ => ⟨by dsimp [Tree.span]; omega, rfl⟩
  | .node _ _ _ _ _ _ _ _, _, .node hls => ⟨SameDTreeSkeletonList.span_le hls, rfl⟩

theorem SameDTreeSkeletonList.span_le {dks : List DTree} {off endOff : Nat} {tks : List Tree}
    (h : SameDTreeSkeletonList dks off endOff tks) : off ≤ endOff :=
  match dks, tks, h with
  | [], [], .nil _ => Nat.le_refl _
  | _ :: _, _ :: _, .cons hsp hdk htl => by
    have h1 := hdk.span_le.1
    rw [hsp] at h1
    exact Nat.le_trans h1 htl.span_le
end

mutual
theorem sameDTreeSkeleton_unique_and_syn {dt : DTree} {off : Nat} {t1 t2 : Tree}
    (h1 : SameDTreeSkeleton dt off t1) (h2 : SameDTreeSkeleton dt off t2) :
    t1.span = t2.span ∧ SameSynSkeleton t1 t2 :=
  match dt, t1, t2, h1, h2 with
  | .leaf _ _, _, _, .leaf _, .leaf _ => ⟨rfl, .leaf _ _⟩
  | .lex _ _ _, _, _, .lex _ hnt1, .lex _ hnt2 => ⟨rfl, .lex _ (hnt1.trans hnt2.symm)⟩
  | .node _ _ _ _ _ _ _ _, _, _, .node hl1, .node hl2 => by
    obtain ⟨rfl, hks⟩ := sameDTreeSkeletonList_unique_and_syn hl1 hl2
    exact ⟨rfl, .node _ _ _ _ _ hks⟩

theorem sameDTreeSkeletonList_unique_and_syn {dks : List DTree} {off e1 e2 : Nat} {tks1 tks2 : List Tree}
    (h1 : SameDTreeSkeletonList dks off e1 tks1) (h2 : SameDTreeSkeletonList dks off e2 tks2) :
    e1 = e2 ∧ SameSynSkeletonList tks1 tks2 :=
  match dks, tks1, tks2, h1, h2 with
  | [], [], [], .nil _, .nil _ => ⟨rfl, .nil⟩
  | _ :: _, _ :: _, _ :: _, .cons hsp1 hd1 htl1, .cons hsp2 hd2 htl2 => by
    obtain ⟨hspEq, hsynD⟩ := sameDTreeSkeleton_unique_and_syn hd1 hd2
    have hmidEq : _ = _ := (Prod.mk.inj (hsp1.symm.trans (hspEq.trans hsp2))).2
    subst hmidEq
    obtain ⟨rfl, hsynTl⟩ := sameDTreeSkeletonList_unique_and_syn htl1 htl2
    exact ⟨rfl, .cons hsynD hsynTl⟩
end

mutual
theorem sameDTreeSkeleton_synHeight {dt : DTree} {off : Nat} {t : Tree}
    (h : SameDTreeSkeleton dt off t) :
    Strict.synHeight t = dtreeSynHeight dt :=
  match dt, t, h with
  | .leaf _ _, _, .leaf _ => rfl
  | .lex _ _ _, _, .lex _ _ => rfl
  | .node _ _ _ _ _ _ _ _, _, .node hl => by
    rw [Strict.synHeight, dtreeSynHeight, sameDTreeSkeletonList_synHeight hl]

theorem sameDTreeSkeletonList_synHeight {dks : List DTree} {off endOff : Nat} {tks : List Tree}
    (h : SameDTreeSkeletonList dks off endOff tks) :
    Strict.synHeightKids tks = dtreeSynHeightKids dks :=
  match dks, tks, h with
  | [], [], .nil _ => rfl
  | dk :: _, tk :: _, .cons _ hd htl => by
    rw [Strict.synHeightKids, dtreeSynHeightKids, sameDTreeSkeletonList_synHeight htl]
    have hisL : tk.isLeaf = dk.isLeaf := by cases hd <;> rfl
    rw [hisL, sameDTreeSkeleton_synHeight hd]
end

mutual
def DTreeBndsMatch (bnds : Nat → Nat) : DTree → Nat → Nat → Prop
  | .leaf b1 b2, off, endOff => endOff = off + 1 ∧ b1 = bnds off ∧ b2 = bnds (off + 1)
  | .lex _ b1 b2, off, endOff => endOff = off + 1 ∧ b1 = bnds off ∧ b2 = bnds (off + 1)
  | .node _ _ _ _ b1 b2 _ dks, off, endOff =>
      b1 = bnds off ∧ b2 = bnds endOff ∧ DTreeBndsMatchList bnds dks off endOff

def DTreeBndsMatchList (bnds : Nat → Nat) : List DTree → Nat → Nat → Prop
  | [], off, endOff => endOff = off
  | dk :: dks, off, endOff => ∃ mid, off ≤ mid ∧ mid ≤ endOff ∧
      DTreeBndsMatch bnds dk off mid ∧ DTreeBndsMatchList bnds dks mid endOff
end

mutual
theorem dtreeBndsMatch_eq {bnds1 bnds2 : Nat → Nat} {dt : DTree} {off endOff1 endOff2 : Nat}
    (h1 : DTreeBndsMatch bnds1 dt off endOff1) (h2 : DTreeBndsMatch bnds2 dt off endOff2) :
    endOff1 = endOff2 ∧ ∀ u, off ≤ u → u ≤ endOff1 → bnds1 u = bnds2 u :=
  match dt with
  | .leaf _ _ => by
    obtain ⟨rfl, hb11, hb12⟩ := h1
    obtain ⟨he2, hb21, hb22⟩ := h2
    refine ⟨he2.symm, fun u hu1 hu2 => ?_⟩
    by_cases hu : u = off
    · subst hu; exact hb11.symm.trans hb21
    · have hu' : u = off + 1 := by omega
      subst hu'; exact hb12.symm.trans hb22
  | .lex _ _ _ => by
    obtain ⟨rfl, hb11, hb12⟩ := h1
    obtain ⟨he2, hb21, hb22⟩ := h2
    refine ⟨he2.symm, fun u hu1 hu2 => ?_⟩
    by_cases hu : u = off
    · subst hu; exact hb11.symm.trans hb21
    · have hu' : u = off + 1 := by omega
      subst hu'; exact hb12.symm.trans hb22
  | .node _ _ _ _ _ _ _ dks => by
    obtain ⟨hb11, _, hl1⟩ := h1
    obtain ⟨hb21, _, hl2⟩ := h2
    exact dtreeBndsMatchList_eq (hb11.symm.trans hb21) hl1 hl2

theorem dtreeBndsMatchList_eq {bnds1 bnds2 : Nat → Nat} {dks : List DTree} {off e1 e2 : Nat}
    (hoff : bnds1 off = bnds2 off)
    (h1 : DTreeBndsMatchList bnds1 dks off e1) (h2 : DTreeBndsMatchList bnds2 dks off e2) :
    e1 = e2 ∧ ∀ u, off ≤ u → u ≤ e1 → bnds1 u = bnds2 u :=
  match dks with
  | [] => by
    dsimp only [DTreeBndsMatchList] at h1 h2
    subst e1; subst e2
    exact ⟨rfl, fun u hu1 hu2 => by
      have hEq : u = off := by omega
      exact hEq ▸ hoff⟩
  | dk :: rest => by
    obtain ⟨m1, hm1Lo, hm1Hi, hd1, htl1⟩ := h1
    obtain ⟨m2, _, _, hd2, htl2⟩ := h2
    obtain ⟨rfl, heq1⟩ := dtreeBndsMatch_eq hd1 hd2
    obtain ⟨rfl, heq2⟩ := dtreeBndsMatchList_eq (heq1 m1 hm1Lo (Nat.le_refl _)) htl1 htl2
    refine ⟨rfl, fun u hu1 hu2 => ?_⟩
    by_cases hum : u ≤ m1
    · exact heq1 u hu1 hum
    · exact heq2 u (by omega) hu2
end

theorem tokenSpan_congr_of_tokBnd_eq (hok : parseTablesOk = true)
    {cx : Ctx} {cs : Array Nat} (hcp : ∀ c ∈ cs.toList, c ≤ 0x10FFFF)
    {first : Bool} {vs : List (Nat × Bool)}
    {els1 els2 : List Element} {toks1 toks2 : List Token}
    (hinv1 : TokStreamInv cx cs first vs els1 toks1)
    (hinv2 : TokStreamInv cx cs first vs els2 toks2)
    (hlen : toks1.length = toks2.length)
    (hbnd : ∀ u, u ≤ toks1.length → tokBnd els1 toks1 u = tokBnd els2 toks2 u) :
    Ecma.Grammar.tokenSpan els1 toks1 = Ecma.Grammar.tokenSpan els2 toks2 := by
  have hclamp : ∀ (els : List Element) (toks : List Token) (i j : Nat),
      Ecma.Grammar.tokenSpan els toks i j =
        Ecma.Grammar.tokenSpan els toks (min i toks.length) (min j toks.length) := by
    intro els toks i j
    have htk : ∀ m, toks.take (min m toks.length) = toks.take m := fun m => by
      by_cases hm : m ≤ toks.length
      · rw [Nat.min_eq_left hm]
      · rw [Nat.min_eq_right (by omega), List.take_length, List.take_of_length_le (by omega)]
    unfold Ecma.Grammar.tokenSpan
    rw [htk i, htk j]
  have hba : ∀ (els : List Element) (toks : List Token) (i' j' : Nat),
      j' < i' → Ecma.Grammar.tokenSpan els toks i' j' = Ecma.Grammar.tokenSpan els toks i' i' := by
    intro els toks i' j' hlt
    have hle : (toks.take j').countP (·.virt.isNone) ≤ (toks.take i').countP (·.virt.isNone) := by
      have : toks.take i' = toks.take j' ++ (toks.drop j').take (i' - j') := by
        conv => lhs; rw [show i' = j' + (i' - j') from by omega, List.take_add]
      rw [this, List.countP_append]; omega
    unfold Ecma.Grammar.tokenSpan
    have hnot : ¬ ((toks.take i').countP (·.virt.isNone) < (toks.take j').countP (·.virt.isNone)) := by omega
    simp [hnot]
  funext i j
  rw [hclamp els1 toks1 i j, hclamp els2 toks2 i j, ← hlen]
  let i' := min i toks1.length
  let j' := min j toks1.length
  have hi' : i' ≤ toks1.length := Nat.min_le_right _ _
  have hj' : j' ≤ toks1.length := Nat.min_le_right _ _
  by_cases hij : i' ≤ j'
  · rw [hinv1.tokenSpan_eq_synSpanOf hok hcp hij hj',
        hinv2.tokenSpan_eq_synSpanOf hok hcp hij (hlen ▸ hj'),
        hbnd i' hi', hbnd j' hj']
  · rw [hba els1 toks1 i' j' (by omega), hba els2 toks2 i' j' (by omega),
        hinv1.tokenSpan_eq_synSpanOf hok hcp (Nat.le_refl _) hi',
        hinv2.tokenSpan_eq_synSpanOf hok hcp (Nat.le_refl _) (hlen ▸ hi'),
        hbnd i' hi']

/-! ### Part 5A: Soundness extraction (`DTree` → `RawStep`s → `(els, toks, t)`) -/

def RawStep.goal : RawStep → NT
  | .virt _ => .InputElementDiv
  | .real _ _ _ _ lg _ => lg

/-- When `(els, toks)` embeds `rs` starting at token index `off` from boundary `start`. -/
def EmbedsAt (cx : Ctx) (cs : Array Nat) (first : Bool) (vs : List (Nat × Bool))
    (els : List Element) (toks : List Token) (start off : Nat) (rs : List RawStep) : Prop :=
  Nonempty (TokStreamInv cx cs first vs els toks) ∧
  off + rs.length ≤ toks.length ∧
  (∀ u, u ≤ rs.length → tokBnd els toks (off + u) = rawBndAt start rs u) ∧
  (∀ (u : Nat) (hu : u < rs.length), StepMatchesTok cs toks (off + u) (rs[u]'hu))

theorem EmbedsAt.split_append {cx : Ctx} {cs : Array Nat} {first : Bool} {vs : List (Nat × Bool)}
    {els : List Element} {toks : List Token} {start mid off : Nat} {r1 r2 : List RawStep}
    (hc1 : RawChain cx cs first vs start mid r1)
    (he : EmbedsAt cx cs first vs els toks start off (r1 ++ r2)) :
    EmbedsAt cx cs first vs els toks start off r1 ∧
    EmbedsAt cx cs first vs els toks mid (off + r1.length) r2 := by
  obtain ⟨hinv, hlen, hbnd, hst⟩ := he
  rw [List.length_append] at hlen
  refine ⟨⟨hinv, by omega, fun u hu => ?_, fun u hu => ?_⟩,
          ⟨hinv, by omega, fun u hu => ?_, fun u hu => ?_⟩⟩
  · have := hbnd u (by rw [List.length_append]; omega)
    simpa only [rawBndAt_append, hu, ↓reduceIte] using this
  · have := hst u (by rw [List.length_append]; omega)
    rwa [List.getElem_append_left hu] at this
  · have := hbnd (r1.length + u) (by rw [List.length_append]; omega)
    rw [rawBndAt_append] at this
    by_cases hu0 : u = 0
    · subst hu0
      simp only [Nat.add_zero, Nat.le_refl, ↓reduceIte, hc1.rawBndAt_end] at this
      simpa [rawBndAt] using this
    · have hnle : ¬ (r1.length + u ≤ r1.length) := by omega
      simp only [hnle, ↓reduceIte, hc1.rawBndAt_end, Nat.add_sub_cancel_left] at this
      simpa [Nat.add_assoc] using this
  · have := hst (r1.length + u) (by rw [List.length_append]; omega)
    rw [List.getElem_append_right (Nat.le_add_right _ _)] at this
    simpa [Nat.add_sub_cancel_left, Nat.add_assoc] using this

private theorem embedsAt_term_tokenAlphabet (hok : parseTablesOk = true)
    {cx : Ctx} {cs : Array Nat} {first : Bool} {vs : List (Nat × Bool)}
    {n : NT} {s : Src} (hs : s ∈ Ecma.Spec.gl.alts cx .syntactic n)
    {k : Nat} (hk : k < s.alt.rhs.length) {x : Terminal} {i h : Nat}
    (htm : SynTermFast cx cs first vs s k x i h)
    (hvsUniq : ∀ p b1 b2, (p, b1) ∈ vs → (p, b2) ∈ vs → b1 = b2) :
    ∃ (st : RawStep),
      st.goal = .InputElementDiv ∧
      RawChain cx cs first vs i h [st] ∧
      ∀ els toks off, EmbedsAt cx cs first vs els toks i off [st] →
        (tokenAlphabet Ecma.Spec.gl cx Engine.Model.codePrims).term s k x (slice toks off (off + 1)) := by
  have hsynT := (synTermFast_iff_synTerm hok hs hk x i h).mp htm
  unfold SynTerm at hsynT
  cases x with
  | cp _ => cases hsynT
  | text str b0 =>
    by_cases hp : vsPending vs i = true
    · simp only [hp, ↓reduceIte] at hsynT
      obtain ⟨rfl, hsemi, rfl⟩ := hsynT
      obtain ⟨heven, hpMem⟩ := mem_vs_of_vsPending hvsUniq hp
      have hi2 : i = 2 * (i / 2) := by omega
      have hrc : RawChain cx cs first vs i (i + 1) [.virt (i / 2)] := by
        have h0 : RawChain cx cs first vs (2 * (i / 2)) (2 * (i / 2) + 1) [.virt (i / 2)] := .virt hpMem (.nil _)
        rwa [← hi2] at h0
      have hhEq : 2 * (i / 2) + 1 = i + 1 := by omega
      refine ⟨.virt (i / 2), rfl, hhEq.symm ▸ hrc, fun els toks off hemb => ?_⟩
      obtain ⟨⟨hinv⟩, hlen, hbnd, hst⟩ := hemb
      obtain ⟨tok, why, hget, htxt, _, hvirt⟩ := hst 0 (by simp)
      simp only [Nat.add_zero] at hget
      have hoffLt : off < toks.length := (List.getElem?_eq_some_iff.mp hget).1
      have hsc1 : slice toks off (off + 1) = [tok] := by
        unfold slice
        rw [Nat.add_sub_cancel_left, List.drop_eq_getElem_cons hoffLt, List.take_succ_cons, List.take_zero]
        rw [Option.some.inj ((List.getElem?_eq_getElem hoffLt).symm.trans hget)]
      rw [hsc1]
      dsimp only [tokenAlphabet]
      refine ⟨htxt, ?_⟩
      rw [hvirt]
      obtain ⟨hbndOff, _, _, hwhyEq, _⟩ := hinv.tokBnd_virt hget hvirt
      have hb0Eq := hbnd 0 (Nat.zero_le _)
      simp only [Nat.add_zero, rawBndAt] at hb0Eq
      have hpOffEq : tokPos els toks off = i / 2 := by omega
      obtain ⟨c, cls, hc, hmemS, hclsOk⟩ := hsemi
      refine ⟨c, hc, cls, hmemS, ?_⟩
      cases cls with
      | doWhile => trivial
      | emptyStatement | forHeader => exact hclsOk
      | insertable | forHeaderIfDeclaration =>
        rw [hpOffEq] at hwhyEq
        rw [hclsOk] at hwhyEq
        simp only [Bool.false_eq_true, ↓reduceIte] at hwhyEq
        rw [hwhyEq]
        cases (off + 1 == toks.length) <;> decide
    · simp only [hp, Bool.false_eq_true, ↓reduceIte] at hsynT
      obtain ⟨a, b, lt, tr, hscan, hnc, htxt, rfl⟩ := hsynT
      refine ⟨.real (i / 2) a b lt .InputElementDiv tr, rfl,
        .real rfl (Bool.eq_false_iff.mpr hp) hnc (by decide) hscan (.nil _),
        fun els toks off hemb => ?_⟩
      obtain ⟨_, _, _, hst⟩ := hemb
      have hget : toks[off]? = some ⟨slice cs.toList a b, lt, none⟩ := by
        have h0 := hst 0 (by simp)
        dsimp only [Nat.add_zero, List.getElem_cons_zero, StepMatchesTok] at h0
        exact h0
      have hoffLt : off < toks.length := (List.getElem?_eq_some_iff.mp hget).1
      have hsc1 : slice toks off (off + 1) = [⟨slice cs.toList a b, lt, none⟩] := by
        rw [show slice toks off (off + 1) = (toks.drop off).take (off + 1 - off) from rfl,
            Nat.add_sub_cancel_left, List.drop_eq_getElem_cons hoffLt, List.take_succ_cons, List.take_zero]
        rw [Option.some.inj ((List.getElem?_eq_getElem hoffLt).symm.trans hget)]
      rw [hsc1]
      exact ⟨htxt, trivial⟩

/-! ### Syntactic `Src` certificates for `butNot` lexical goals and `semis` -/

private def itemButNotDivOk : Item → Bool
  | .butNot base ex =>
    (match base with
     | .t _ => true
     | .nt bm _ => lexicalGoalOf bm == .InputElementDiv) &&
    (match ex with
     | .sym y => match y with | .t _ => true | .nt m _ => lexicalGoalOf m == .InputElementDiv
     | .oneOf ys _ => ys.all fun | .t _ => true | .nt m _ => lexicalGoalOf m == .InputElementDiv)
  | _ => true

private def semiCtorEntries : List (GrammarId × NT × Nat × Nat) :=
  glData.grammars.flatMap fun (g, rules) =>
    let ws := rules.flatMap fun r => r.written.zipIdx.map fun (k, i) => (r, i, k)
    ws.zipIdx.filterMap fun ((r, i, _), c) =>
      if glData.semis.any (fun (c', _, _) => c == c') then some (g, r.lhs, i, c) else none

private def srcSemisOk (entries : List (GrammarId × NT × Nat × Nat)) (s : Src) : Bool :=
  entries.all fun (g, lhs, idx, c) =>
    !(g == s.grammar && lhs == s.rule.lhs && idx == s.idx) ||
    (List.range s.alt.rhs.length).all fun k =>
      !(glData.semis.any fun (c', k', _) => c == c' && k' == k) ||
      match s.alt.rhs[k]? with
      | some (.sym (.t (.text ";" _)) _) => true
      | _ => false

private def synSrcPred (entries : List (GrammarId × NT × Nat × Nat)) (s : Src) : Bool :=
  s.alt.rhs.all itemButNotDivOk && srcSemisOk entries s

set_option maxRecDepth 400000 in
private theorem synSrcPred_cert :
    (let entries := semiCtorEntries
     (glData.rulesOf .syntactic).all (fun r => (srcsOf .syntactic r).all (synSrcPred entries)) &&
     glData.blocks.all (fun b => match b.kind with
       | .overlay sec _ _ => !(overlayGrammar sec == .syntactic) || b.rules.all (fun r => (srcsOf .annexB r).all (synSrcPred entries))
       | _ => true)) = true := by decide

private theorem synSrcPred_of_alts {cx : Ctx} {n : NT} {s : Src}
    (hs : s ∈ Ecma.Spec.gl.alts cx .syntactic n) :
    synSrcPred semiCtorEntries s = true := by
  obtain ⟨hpPin, hpOv⟩ := Bool.and_eq_true_iff.mp synSrcPred_cert
  rw [← glData_eq] at hs
  unfold GL.alts at hs
  have hovPres : ∀ (bs : List (Block × OverlayMode)) (acc : List Src),
      (∀ x ∈ acc, synSrcPred semiCtorEntries x = true) →
      (∀ pm ∈ bs, pm.1 ∈ glData.blocks ∧ ∃ sec md cd, pm.1.kind = .overlay sec md cd ∧ overlayGrammar sec == .syntactic) →
      ∀ x ∈ bs.foldl (fun a (b, md) =>
        match b.rules.find? (·.lhs == n), md with
        | none, _ => a
        | some rB, .extend => a ++ (srcsOf .annexB rB).filter fun (s' : Src) => !a.any (·.alt == s'.alt)
        | some rB, .replace => srcsOf .annexB rB) acc,
        synSrcPred semiCtorEntries x = true := by
    intro bs
    induction bs with
    | nil => intro acc hacc _; exact hacc
    | cons hd tl ih =>
      intro acc hacc hbs
      obtain ⟨hbMem, sec, md, cd, hbk, hog⟩ := hbs hd (List.mem_cons_self ..)
      have hbOk := List.all_eq_true.mp hpOv hd.1 hbMem
      rw [hbk] at hbOk; simp only [hog, Bool.not_true, Bool.false_or] at hbOk
      dsimp only [List.foldl_cons]
      have hacc' : ∀ x ∈ (match hd.1.rules.find? (·.lhs == n), hd.2 with
          | none, _ => acc
          | some rB, .extend => acc ++ (srcsOf .annexB rB).filter fun (s' : Src) => !acc.any (·.alt == s'.alt)
          | some rB, .replace => srcsOf .annexB rB), synSrcPred semiCtorEntries x = true := by
        rcases opt_none_or_some (hd.1.rules.find? (·.lhs == n)) with hfn | ⟨rB, hfn⟩
        · rw [hfn]; exact hacc
        · rw [hfn]
          have hrAll := List.all_eq_true.mp hbOk rB (List.mem_of_find?_eq_some hfn)
          cases hd.2 with
          | extend =>
            intro x hx
            rcases List.mem_append.mp hx with h1 | h2
            · exact hacc x h1
            · exact List.all_eq_true.mp hrAll x (List.mem_filter.mp h2).1
          | replace =>
            intro x hx; exact List.all_eq_true.mp hrAll x hx
      exact ih _ hacc' (fun pm hpm => hbs pm (List.mem_cons_of_mem _ hpm))
  refine hovPres _ _ ?_ ?_ s hs
  · unfold GL.pinned
    rcases opt_none_or_some ((glData.rulesOf .syntactic).find? (·.lhs == n)) with hfn | ⟨r, hfn⟩
    · rw [hfn]; simp [baseGrammar]
    · rw [hfn]
      exact fun x hx => List.all_eq_true.mp (List.all_eq_true.mp hpPin r (List.mem_of_find?_eq_some hfn)) x hx
  · intro pm hpm; unfold GL.overlays at hpm; split at hpm
    · cases hpm
    · obtain ⟨b, hb, hfb⟩ := List.mem_filterMap.mp hpm
      cases hbk : b.kind with
      | main | supplemental _ => rw [hbk] at hfb; cases hfb
      | overlay sec md cd =>
        rw [hbk] at hfb; dsimp only at hfb
        split at hfb
        · rename_i hcond; cases hfb
          exact ⟨hb, sec, md, cd, hbk, (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp hcond).1).1⟩
        · cases hfb

private theorem synSrc_semis_imp (_hok : parseTablesOk = true) {cx : Ctx} {n : NT} {s : Src}
    (hs : s ∈ Ecma.Spec.gl.alts cx .syntactic n) {k : Nat} (hk : k < s.alt.rhs.length)
    {c : Nat} {cls : Semi}
    (hctor : Ecma.Spec.gl.ctorOf s = some c) (hsem : (c, k, cls) ∈ Ecma.Spec.gl.semis) :
    ∃ b o, s.alt.rhs[k]? = some (.sym (.t (.text ";" b)) o) := by
  have hpred := (Bool.and_eq_true_iff.mp (synSrcPred_of_alts hs)).2
  rw [← glData_eq] at hctor hsem
  unfold GL.ctorOf at hctor
  obtain ⟨p, hfind, rfl⟩ := Option.map_eq_some_iff.mp hctor
  have hpMem := List.mem_of_find?_eq_some hfind
  have hpHit := List.find?_some hfind
  simp only [Bool.and_eq_true, beq_iff_eq] at hpHit
  obtain ⟨⟨hgEq, hlhsEq⟩, haltEq⟩ := hpHit
  unfold prodsOf at hpMem
  obtain ⟨⟨g, rules⟩, hgrMem, hpInG⟩ := List.mem_flatMap.mp hpMem
  obtain ⟨⟨⟨r, i, mCnt⟩, c0⟩, hwsMem, hpInM⟩ := List.mem_flatMap.mp hpInG
  obtain ⟨m, _, rfl⟩ := List.mem_map.mp hpInM
  dsimp only at hgEq hlhsEq haltEq hsem ⊢
  have hanyC : (glData.semis.any fun (c', _, _) => c0 == c') = true :=
    List.any_eq_true.mpr ⟨(c0, k, cls), hsem, by simp⟩
  have hmemEnt : (s.grammar, s.rule.lhs, s.idx, c0) ∈ semiCtorEntries := by
    unfold semiCtorEntries
    exact List.mem_flatMap.mpr ⟨(g, rules), hgrMem,
      List.mem_filterMap.mpr ⟨((r, i, mCnt), c0), hwsMem, by simp [hanyC, hgEq, hlhsEq, haltEq]⟩⟩
  unfold srcSemisOk at hpred
  have hent := List.all_eq_true.mp hpred (s.grammar, s.rule.lhs, s.idx, c0) hmemEnt
  simp only [beq_self_eq_true, Bool.and_self, Bool.not_true, Bool.false_or] at hent
  have hkOk := List.all_eq_true.mp hent k (List.mem_range.mpr hk)
  have hany : (glData.semis.any fun (c', k', _) => c0 == c' && k' == k) = true :=
    List.any_eq_true.mpr ⟨(c0, k, cls), hsem, by simp⟩
  rw [hany] at hkOk
  simp only [Bool.not_true, Bool.false_or] at hkOk
  cases hg : s.alt.rhs[k]? with
  | none => rw [hg] at hkOk; cases hkOk
  | some it =>
    rw [hg] at hkOk
    cases it with
    | sym sym0 o =>
      cases sym0 with
      | nt _ _ => cases hkOk
      | t x =>
        cases x with
        | cp _ => cases hkOk
        | text str b =>
          by_cases hstr : str = ";"
          · subst hstr; exact ⟨b, o, rfl⟩
          · simp [hstr] at hkOk
    | _ => cases hkOk

private theorem synSrc_butNot_divOk {cx : Ctx} {n : NT} {s : Src}
    (hs : s ∈ Ecma.Spec.gl.alts cx .syntactic n) {it : Item} (hit : it ∈ s.alt.rhs) :
    itemButNotDivOk it = true :=
  List.all_eq_true.mp (Bool.and_eq_true_iff.mp (synSrcPred_of_alts hs)).1 it hit

private theorem excl_token_iff_synExcluded (hok : parseTablesOk = true)
    {cx : Ctx} {cs : Array Nat} (hcp : ∀ c ∈ cs.toList, c ≤ 0x10FFFF)
    {first : Bool} {vs : List (Nat × Bool)} {els : List Element} {toks : List Token}
    (hinv : TokStreamInv cx cs first vs els toks)
    {n : NT} {s : Src} (hs : s ∈ Ecma.Spec.gl.alts cx .syntactic n)
    {k : Nat} (_hk : k < s.alt.rhs.length) {base : Sym} {ex : Exclusion}
    (hrhsK : s.alt.rhs[k]? = some (.butNot base ex))
    {off : Nat} (hoff : off < toks.length)
    (hvNone : toks[off].virt = none)
    (hscanDiv : ∃ a b lt tr,
      ScanTok Ecma.Spec.gl cx Engine.Model.codePrims cs.toList first .InputElementDiv
        (tokBnd els toks off / 2) a b lt tr ∧
      tokBnd els toks (off + 1) = 2 * b ∧
      toks[off] = ⟨slice cs.toList a b, lt, none⟩)
    (k0 : Nat) (ps : List Param) :
    Excluded (tokenAlphabet Ecma.Spec.gl cx Engine.Model.codePrims)
        (fun m ps' a b => ∃ t', DerivesAt Ecma.Spec.gl cx .syntactic
          (tokenAlphabet Ecma.Spec.gl cx Engine.Model.codePrims) toks (k0 + 1) m ps' a b t')
        toks s k ps off (off + 1) ex ↔
      SynExcluded Ecma.Spec.gl cx Engine.Model.codePrims cs.toList first vs s k
        (tokBnd els toks off) (tokBnd els toks (off + 1)) ex := by
  have hitMem : Item.butNot base ex ∈ s.alt.rhs := List.mem_of_getElem? hrhsK
  have hokIt : synItemOk cx (.butNot base ex) = true := synItemOk_of_mem hok hs hitMem
  have hdivIt : itemButNotDivOk (.butNot base ex) = true := synSrc_butNot_divOk hs hitMem
  dsimp only [synItemOk] at hokIt
  dsimp only [itemButNotDivOk] at hdivIt
  have hget : toks[off]? = some toks[off] := List.getElem?_eq_getElem hoff
  obtain ⟨hr, hdiv2, hnp, _, hnc, hbndBlk, _⟩ := hinv.tokBnd_real hget hvNone
  obtain ⟨a0, b0, lt0, tr0, hsc0, hbndNext0, htokEq0⟩ := hscanDiv
  have hnc0 : noCross vs (tokBnd els toks off / 2) b0 = true := by
    have hbEq : b0 = (hinv.blocks[(toks.take off).countP (·.virt.isNone)]'hr).tokEl.j := by omega
    rwa [hdiv2, hbEq]
  have hsc1 : slice toks off (off + 1) = [toks[off]] := by
    unfold slice
    rw [Nat.add_sub_cancel_left, List.drop_eq_getElem_cons hoff, List.take_succ_cons, List.take_zero]
  have hsymIff : ∀ y : Sym,
      (match y with | .t _ => true | .nt m _ => (glData.alts cx .syntactic m).isEmpty) = true →
      (match y with | .t _ => true | .nt m _ => lexicalGoalOf m == .InputElementDiv) = true →
      ((match y with
        | .t x => (tokenAlphabet Ecma.Spec.gl cx Engine.Model.codePrims).term s k x (slice toks off (off + 1))
        | .nt m args => ∃ t', DerivesAt Ecma.Spec.gl cx .syntactic
            (tokenAlphabet Ecma.Spec.gl cx Engine.Model.codePrims) toks (k0 + 1) m (applyArgs ps args) off (off + 1) t') ↔
       SynSymEx Ecma.Spec.gl cx Engine.Model.codePrims cs.toList first vs s k
         (tokBnd els toks off) (tokBnd els toks (off + 1)) y) := by
    intro y hyNil hyDiv
    cases y with
    | t x =>
      dsimp only [SynSymEx, SynTerm]
      cases x with
      | cp _ => rw [hsc1]; exact ⟨(fun h => nomatch h), (fun h => nomatch h)⟩
      | text str b =>
        rw [hsc1, hnp]
        simp only [Bool.false_eq_true, ↓reduceIte, tokenAlphabet, hvNone]
        constructor
        · rintro ⟨htxt, _⟩
          rw [htokEq0] at htxt
          exact ⟨a0, b0, lt0, tr0, hsc0, hnc0, htxt, hbndNext0⟩
        · rintro ⟨a', b', lt', tr', hsc', _, htxt', hbEq'⟩
          obtain ⟨rfl, rfl, rfl⟩ := scanTok_span_unique hok hcp hsc0 hsc'
          rw [htokEq0]
          exact ⟨htxt', trivial⟩
    | nt m args =>
      have hnil : Ecma.Spec.gl.alts cx .syntactic m = [] := List.isEmpty_iff.mp (glData_eq ▸ hyNil)
      have hlgM : lexicalGoalOf m = .InputElementDiv := beq_iff_eq.mp hyDiv
      dsimp only [SynSymEx, SynLeaf, DerivesAt]
      have hlenSl : (slice cs.toList a0 b0).length = b0 - a0 := by
        unfold slice; rw [List.length_take, List.length_drop]; have := hsc0.2.1; have := hsc0.2.2.1; omega
      constructor
      · rintro ⟨t', hst⟩
        cases hst with
        | node s' hs' _ _ _ => rw [hnil] at hs'; cases hs'
        | @lex _ _ _ tl tok _ hget' hleaf =>
          have htokId : tok = toks[off] := Option.some.inj (hget'.symm.trans hget)
          subst htokId
          obtain ⟨_, hderL⟩ := hleaf
          rw [htokEq0] at hderL; dsimp only at hderL
          rw [hlenSl] at hderL
          exact ⟨hnil, hnp, a0, b0, lt0, tr0, tl, hlgM.symm ▸ hsc0, hnc0, hderL, hbndNext0⟩
      · rintro ⟨_, _, a', b', lt', tr', tl, hsc', _, hderL, _⟩
        rw [hlgM] at hsc'
        obtain ⟨rfl, rfl, rfl⟩ := scanTok_span_unique hok hcp hsc0 hsc'
        refine ⟨.lex off tl, .lex hnil hget ⟨hvNone, ?_⟩⟩
        rw [htokEq0]; dsimp only
        rwa [hlenSl]
  obtain ⟨hokBase, hokEx⟩ := Bool.and_eq_true_iff.mp hokIt
  obtain ⟨hdivBase, hdivEx⟩ := Bool.and_eq_true_iff.mp hdivIt
  cases ex with
  | sym y => exact hsymIff y hokEx hdivEx
  | oneOf ys _ =>
    dsimp only [Excluded, SynExcluded]
    exact ⟨fun ⟨y, hy, hsy⟩ =>
        ⟨y, hy, (hsymIff y (List.all_eq_true.mp hokEx y hy) (List.all_eq_true.mp hdivEx y hy)).mp hsy⟩,
      fun ⟨y, hy, hsy⟩ =>
        ⟨y, hy, (hsymIff y (List.all_eq_true.mp hokEx y hy) (List.all_eq_true.mp hdivEx y hy)).mpr hsy⟩⟩

/-! ### Soundness extraction: `PlainDerives` + `DNodeRel` → `RawChain` + parameterized `Tree` -/

private theorem trivia_chainEls (hok : parseTablesOk = true) {cx : Ctx} {cs : Array Nat}
    (hcp : ∀ c ∈ cs.toList, c ≤ 0x10FFFF) {first : Bool} {p k : Nat} {lt : Bool}
    (htr : Trivia Ecma.Spec.gl cx Engine.Model.codePrims cs.toList first p k lt) :
    ∃ es : List Element,
      ChainEls p k es ∧
      (∀ e ∈ es, ValidTrivEl cx cs first e) ∧
      (es.any fun e => e.breaks cs.toList) = lt := by
  have hsk := (trivia_eq_skip hok hcp).mp htr
  obtain ⟨_, _, _, _, es, hch, hv, hbr⟩ := skip_spec (cx := cx) hok hcp first p
  rw [hsk] at hch hbr
  exact ⟨es, hch, hv, hbr⟩

private theorem inKids_prepend {r1 r2 : List RawStep} {hd : Tree} {tl : List Tree} {off : Nat}
    (hhdIn : ∀ (u : Nat) (hu : u < r1.length), hd.goalAt (off + u) = some (r1[u]'hu).goal)
    (hhdOut : ∀ idx, (idx < off ∨ off + r1.length ≤ idx) → hd.goalAt idx = none)
    (htlIn : ∀ (u : Nat) (hu : u < r2.length), Tree.goalAt.inKids (off + r1.length + u) tl = some (r2[u]'hu).goal)
    (htlOut : ∀ idx, (idx < off + r1.length ∨ off + r1.length + r2.length ≤ idx) → Tree.goalAt.inKids idx tl = none) :
    (∀ (u : Nat) (hu : u < (r1 ++ r2).length), Tree.goalAt.inKids (off + u) (hd :: tl) = some ((r1 ++ r2)[u]'hu).goal) ∧
    (∀ idx, (idx < off ∨ off + (r1 ++ r2).length ≤ idx) → Tree.goalAt.inKids idx (hd :: tl) = none) := by
  refine ⟨fun u hu => ?_, fun idx hout => ?_⟩
  · dsimp only [Tree.goalAt.inKids]
    have huLen : u < r1.length + r2.length := List.length_append ▸ hu
    by_cases hu1 : u < r1.length
    · rw [hhdIn u hu1, List.getElem_append_left hu1]
    · rw [hhdOut (off + u) (Or.inr (by omega)), List.getElem_append_right (by omega),
          show off + u = off + r1.length + (u - r1.length) from by omega]
      exact htlIn (u - r1.length) (by omega)
  · rw [List.length_append] at hout
    dsimp only [Tree.goalAt.inKids]
    rw [hhdOut idx (by omega)]
    exact htlOut idx (by omega)

private theorem dtreeBndsMatchList_prepend {cx : Ctx} {cs : Array Nat} {first : Bool} {vs : List (Nat × Bool)}
    {i0 h0 : Nat} {r1 r2 : List RawStep} {dk1 : DTree} {dks2 : List DTree}
    {bnds : Nat → Nat} {off : Nat}
    (hc1 : RawChain cx cs first vs i0 h0 r1)
    (hbAll : ∀ u, u ≤ (r1 ++ r2).length → bnds (off + u) = rawBndAt i0 (r1 ++ r2) u)
    (hb1 : (∀ u, u ≤ r1.length → bnds (off + u) = rawBndAt i0 r1 u) →
      DTreeBndsMatch bnds dk1 off (off + r1.length))
    (hb2 : (∀ u, u ≤ r2.length → bnds (off + r1.length + u) = rawBndAt h0 r2 u) →
      DTreeBndsMatchList bnds dks2 (off + r1.length) (off + r1.length + r2.length)) :
    DTreeBndsMatchList bnds (dk1 :: dks2) off (off + (r1 ++ r2).length) := by
  rw [List.length_append, ← Nat.add_assoc]
  refine ⟨off + r1.length, by omega, by omega, hb1 fun u hu => ?_, hb2 fun u hu => ?_⟩
  · have := hbAll u (by rw [List.length_append]; omega)
    simpa only [rawBndAt_append, hu, ↓reduceIte] using this
  · have := hbAll (r1.length + u) (by rw [List.length_append]; omega)
    rw [rawBndAt_append] at this
    by_cases hu0 : u = 0
    · subst hu0; simpa [rawBndAt, hc1.rawBndAt_end] using this
    · have hnle : ¬ (r1.length + u ≤ r1.length) := by omega
      simp only [hnle, ↓reduceIte, hc1.rawBndAt_end, Nat.add_sub_cancel_left] at this
      simpa [Nat.add_assoc] using this

private theorem leaf_goalAt_one (off : Nat) :
    (∀ (u : Nat) (_hu : u < 1), (Tree.leaf off (off + 1)).goalAt (off + u) = some .InputElementDiv) ∧
    (∀ idx, (idx < off ∨ off + 1 ≤ idx) → (Tree.leaf off (off + 1)).goalAt idx = none) := by
  refine ⟨fun u hu => ?_, fun idx hout => ?_⟩
  · have hu0 : u = 0 := by omega
    subst hu0; simp [Tree.goalAt]
  · unfold Tree.goalAt
    rcases hout with h1 | h2
    · simp [show ¬ (off ≤ idx) from by omega]
    · simp [show ¬ (idx < off + 1) from by omega]

private theorem lex_goalAt_one (off : Nat) {m : NT} {tLex : Tree} (hnt : tLex.nt? = some m) :
    (∀ (u : Nat) (_hu : u < 1), (Tree.lex off tLex).goalAt (off + u) = some (lexicalGoalOf m)) ∧
    (∀ idx, (idx < off ∨ off + 1 ≤ idx) → (Tree.lex off tLex).goalAt idx = none) := by
  refine ⟨fun u hu => ?_, fun idx hout => ?_⟩
  · have hu0 : u = 0 := by omega
    subst hu0; simp [Tree.goalAt, hnt]
  · unfold Tree.goalAt
    have hne : off ≠ idx := by omega
    simp [hne]

private theorem sound_extract (hok : parseTablesOk = true) {cs : Array Nat}
    (hcp : ∀ c ∈ cs.toList, c ≤ 0x10FFFF) {first : Bool} {cx : Ctx} {stamp : Nat}
    {vs : List (Nat × Bool)} (hvs : ∀ pb ∈ vs, pb.1 ≤ cs.size)
    (hvsUniq : ∀ p b1 b2, (p, b1) ∈ vs → (p, b2) ∈ vs → b1 = b2) :
    let S := synAlphaSpec hok hcp first cx stamp vs hvs
    ∀ {n : NT} {ps : List Param} {i j : Nat} {dt : DTree} {nd : Engine.Model.Node},
      S.PlainDerives n ps i j dt →
      S.DNodeRel stamp nd dt →
      ∃ (rs : List RawStep) (mkTree : Nat → Tree),
        RawChain cx cs first vs i j rs ∧
        (∀ off, SameDTreeSkeleton dt off (mkTree off)) ∧
        (∀ (bnds : Nat → Nat) (off : Nat),
          (∀ u, u ≤ rs.length → bnds (off + u) = rawBndAt i rs u) →
          DTreeBndsMatch bnds dt off (off + rs.length)) ∧
        (∀ off, (mkTree off).span = (off, off + rs.length) ∧
          (mkTree off).nt? = some n ∧ (mkTree off).isLeaf = false) ∧
        (∀ off,
          (∀ (u : Nat) (hu : u < rs.length), (mkTree off).goalAt (off + u) = some (rs[u]'hu).goal) ∧
          (∀ idx, (idx < off ∨ off + rs.length ≤ idx) → (mkTree off).goalAt idx = none)) ∧
        (∀ els toks off, EmbedsAt cx cs first vs els toks i off rs →
          ForHeadersExplicit toks (mkTree off) ∧
          Ecma.Model.NodeRel Engine.Impl stamp cs.toList (Ecma.Grammar.tokenSpan els toks) nd (mkTree off) ∧
          ∀ k0, DerivesAt Ecma.Spec.gl cx .syntactic
            (tokenAlphabet Ecma.Spec.gl cx Engine.Model.codePrims) toks (k0 + 2) n ps off (off + rs.length) (mkTree off)) := by
  intro S
  have hmain : ∀ (sz : Nat) {n : NT} {ps : List Param} {i j : Nat} {dt : DTree} {nd : Engine.Model.Node},
      sizeOf dt ≤ sz →
      S.PlainDerives n ps i j dt →
      S.DNodeRel stamp nd dt →
      ∃ (rs : List RawStep) (mkTree : Nat → Tree),
        RawChain cx cs first vs i j rs ∧
        (∀ off, SameDTreeSkeleton dt off (mkTree off)) ∧
        (∀ (bnds : Nat → Nat) (off : Nat),
          (∀ u, u ≤ rs.length → bnds (off + u) = rawBndAt i rs u) →
          DTreeBndsMatch bnds dt off (off + rs.length)) ∧
        (∀ off, (mkTree off).span = (off, off + rs.length) ∧
          (mkTree off).nt? = some n ∧ (mkTree off).isLeaf = false) ∧
        (∀ off,
          (∀ (u : Nat) (hu : u < rs.length), (mkTree off).goalAt (off + u) = some (rs[u]'hu).goal) ∧
          (∀ idx, (idx < off ∨ off + rs.length ≤ idx) → (mkTree off).goalAt idx = none)) ∧
        (∀ els toks off, EmbedsAt cx cs first vs els toks i off rs →
          ForHeadersExplicit toks (mkTree off) ∧
          Ecma.Model.NodeRel Engine.Impl stamp cs.toList (Ecma.Grammar.tokenSpan els toks) nd (mkTree off) ∧
          ∀ k0, DerivesAt Ecma.Spec.gl cx .syntactic
            (tokenAlphabet Ecma.Spec.gl cx Engine.Model.codePrims) toks (k0 + 2) n ps off (off + rs.length) (mkTree off)) := by
    intro sz
    induction sz using Nat.strongRecOn with
    | ind sz ihOuter =>
      intro n ps i j dt nd hsz hpl hdrel
      match dt, hpl with
      | .node _ pId s _ _ _ mask dks, .node _ hsMem _ hgrd hpid hsw =>
        cases hdrel with
        | node hnt hprod hargs hstNd hspNd htxtNd hkl =>
          have hsSpec : s ∈ Ecma.Spec.gl.alts cx .syntactic n := (altsOf_eq hok cx .syntactic n) ▸ hsMem
          obtain ⟨hlhsS, hoptsS⟩ := alt_lhs_and_opts hok hsSpec
          have hmMask : mask ∈ masks s.alt.opts := hoptsS ▸ S.seqWith_masks hsw
          obtain ⟨hpeq, _, _, _, _⟩ := prodIdOf_spec hok hsSpec hmMask
          have hpidSpec : Ecma.Spec.gl.prodId s mask = some pId := hpeq.symm.trans hpid
          have hszDks : sizeOf dks < sz := by
            simp +arith only [DTree.node.sizeOf_spec] at hsz; omega
          have hseq : ∀ (is : List Item) (k i0 : Nat) (m0 : List Bool) (dks0 : List DTree)
              (nds0 : List Engine.Model.Node),
              sizeOf dks0 ≤ sizeOf dks →
              k ≤ s.alt.rhs.length →
              s.alt.rhs.drop k = is →
              S.SeqWith (fun _ _ _ _ => True) s ps k is i0 j m0 dks0 →
              S.DNodeRelList stamp nds0 (dks0.filter fun d => !d.isLeaf) →
              ∃ (rs : List RawStep) (mkKids : Nat → List Tree),
                RawChain cx cs first vs i0 j rs ∧
                (∀ off, SameDTreeSkeletonList dks0 off (off + rs.length) (mkKids off)) ∧
                (∀ (bnds : Nat → Nat) (off : Nat),
                  (∀ u, u ≤ rs.length → bnds (off + u) = rawBndAt i0 rs u) →
                  DTreeBndsMatchList bnds dks0 off (off + rs.length)) ∧
                (∀ off,
                  (∀ (u : Nat) (hu : u < rs.length), Tree.goalAt.inKids (off + u) (mkKids off) = some (rs[u]'hu).goal) ∧
                  (∀ idx, (idx < off ∨ off + rs.length ≤ idx) → Tree.goalAt.inKids idx (mkKids off) = none)) ∧
                (∀ els toks off, EmbedsAt cx cs first vs els toks i0 off rs →
                  ForHeadersExplicit.all toks (mkKids off) ∧
                  (n == .ForStatement → ∀ d ∈ mkKids off, d.nt? = some .LexicalDeclaration →
                    ∀ tok, toks[d.span.2 - 1]? = some tok → tok.virt = none) ∧
                  nds0.length = ((mkKids off).filter fun t => !t.isLeaf).length ∧
                  (∀ (idx : Nat) tk ck, ((mkKids off).filter fun t => !t.isLeaf)[idx]? = some tk →
                    nds0[idx]? = some ck →
                    Ecma.Model.NodeRel Engine.Impl stamp cs.toList (Ecma.Grammar.tokenSpan els toks) ck tk) ∧
                  ∀ k0, Ecma.Grammar.Seq (tokenAlphabet Ecma.Spec.gl cx Engine.Model.codePrims)
                    (fun m ps' a b => ∃ t', DerivesAt Ecma.Spec.gl cx .syntactic
                      (tokenAlphabet Ecma.Spec.gl cx Engine.Model.codePrims) toks (k0 + 1) m ps' a b t')
                    toks Ecma.Spec.gl cx .syntactic s ps k is off (off + rs.length) m0 (mkKids off)) := by
            intro is
            induction is with
            | nil =>
              intro k i0 m0 dks0 nds0 _ _ _ hsw0 hkl0
              cases hsw0; cases hkl0
              exact ⟨[], fun _ => [], .nil _, fun off => by simpa using SameDTreeSkeletonList.nil off,
                fun _ _ _ => by simp [DTreeBndsMatchList],
                fun _ => ⟨(fun _ hu => nomatch hu), fun _ _ => rfl⟩,
                fun _ _ _ _ => ⟨trivial, (fun _ _ hd => nomatch hd), rfl,
                  fun _ _ _ htk _ => by simp at htk, fun _ => by simpa using Seq.nil⟩⟩
            | cons it rest ihIs =>
              intro k i0 m0 dks0 nds0 hsz0 hk0 hdr0 hsw0 hkl0
              have hallOk : ∀ x ∈ it :: rest, synItemOk cx x = true := fun x hx =>
                synItemOk_of_mem hok hsSpec (List.mem_of_mem_drop (hdr0 ▸ hx))
              have hkLt : k < s.alt.rhs.length := by
                have hlen : 0 < (s.alt.rhs.drop k).length := by rw [hdr0]; simp
                rw [List.length_drop] at hlen; omega
              have hdrRest : s.alt.rhs.drop (k + 1) = rest := by
                rw [← List.tail_drop, hdr0]; rfl
              have hrhsK : s.alt.rhs[k]? = some it := by
                have h1 : (s.alt.rhs.drop k).head? = some it := by rw [hdr0]; rfl
                rw [List.head?_drop] at h1; exact h1
              cases hsw0 with
              | absent hr =>
                obtain ⟨rs2, mkTl, hc2, hsk2, hbnd2, hgl2, hemb2⟩ :=
                  ihIs (k + 1) i0 _ dks0 nds0 hsz0 (Nat.succ_le_of_lt hkLt) hdrRest hr hkl0
                exact ⟨rs2, mkTl, hc2, hsk2, hbnd2, hgl2, fun els toks off he =>
                  let ⟨hfhe, hfor, hlen, hrel, hsq⟩ := hemb2 els toks off he
                  ⟨hfhe, hfor, hlen, hrel, fun k0 => .absent (hsq k0)⟩⟩
              | @look _ _ _ l _ _ _ _ _ hlk hr =>
                obtain ⟨rs2, mkTl, hc2, hsk2, hbnd2, hgl2, hemb2⟩ :=
                  ihIs (k + 1) i0 m0 dks0 nds0 hsz0 (Nat.succ_le_of_lt hkLt) hdrRest hr hkl0
                refine ⟨rs2, mkTl, hc2, hsk2, hbnd2, hgl2, fun els toks off he => ?_⟩
                obtain ⟨hfhe, hfor, hlen, hrel, hsq⟩ := hemb2 els toks off he
                have hhitOk := hallOk _ (List.mem_cons_self ..)
                have hsynLk := (synLook_iff hok hcp hvs hhitOk i0).mp hlk
                have hb0Eq : tokBnd els toks off = i0 := by simpa [rawBndAt] using he.2.2.1 0 (Nat.zero_le _)
                have hoffLe : off ≤ toks.length := by have := he.2.1; omega
                let ⟨hinv⟩ := he.1
                refine ⟨hfhe, hfor, hlen, hrel, fun k0 => .look ?_ (hsq k0)⟩
                dsimp only [synItemOk] at hhitOk
                cases l with
                | eq q =>
                  exact (hinv.startsWith_iff_synStarts hok hcp s q (by simpa [lookSeqsOk] using hhitOk) hoffLe).mpr (hb0Eq.symm ▸ hsynLk)
                | ne q =>
                  exact fun hsw => hsynLk (hb0Eq ▸ (hinv.startsWith_iff_synStarts hok hcp s q (by simpa [lookSeqsOk] using hhitOk) hoffLe).mp hsw)
                | mem qs =>
                  obtain ⟨q, hq, hsqQ⟩ := hsynLk
                  have hqOk : lookSeqsOk synLookTermOk [q] = true := by
                    simp only [lookSeqsOk, List.all_cons, List.all_nil, Bool.and_true]
                    exact List.all_eq_true.mp hhitOk q hq
                  exact ⟨q, hq, (hinv.startsWith_iff_synStarts hok hcp s q hqOk hoffLe).mpr (hb0Eq.symm ▸ hsqQ)⟩
                | notMem qs =>
                  intro q hq hsw
                  have hqOk : lookSeqsOk synLookTermOk [q] = true := by
                    simp only [lookSeqsOk, List.all_cons, List.all_nil, Bool.and_true]
                    exact List.all_eq_true.mp hhitOk q hq
                  exact hsynLk q hq (hb0Eq ▸ (hinv.startsWith_iff_synStarts hok hcp s q hqOk hoffLe).mp hsw)
                | notMemNT _ => cases hhitOk
              | noLT hnl hr =>
                obtain ⟨rs2, mkTl, hc2, hsk2, hbnd2, hgl2, hemb2⟩ :=
                  ihIs (k + 1) i0 m0 dks0 nds0 hsz0 (Nat.succ_le_of_lt hkLt) hdrRest hr hkl0
                refine ⟨rs2, mkTl, hc2, hsk2, hbnd2, hgl2, fun els toks off he => ?_⟩
                obtain ⟨hfhe, hfor, hlen, hrel, hsq⟩ := hemb2 els toks off he
                have hb0Eq : tokBnd els toks off = i0 := by simpa [rawBndAt] using he.2.2.1 0 (Nat.zero_le _)
                have hoffLe : off ≤ toks.length := by have := he.2.1; omega
                let ⟨hinv⟩ := he.1
                exact ⟨hfhe, hfor, hlen, hrel, fun k0 =>
                  .noLT ((hinv.noLT_iff_synNoLT hok hcp hoffLe).mpr (hb0Eq.symm ▸ hnl)) (hsq k0)⟩
              | empty hr =>
                obtain ⟨rs2, mkTl, hc2, hsk2, hbnd2, hgl2, hemb2⟩ :=
                  ihIs (k + 1) i0 m0 dks0 nds0 hsz0 (Nat.succ_le_of_lt hkLt) hdrRest hr hkl0
                exact ⟨rs2, mkTl, hc2, hsk2, hbnd2, hgl2, fun els toks off he =>
                  let ⟨hfhe, hfor, hlen, hrel, hsq⟩ := hemb2 els toks off he
                  ⟨hfhe, hfor, hlen, hrel, fun k0 => .empty (hsq k0)⟩⟩
              | onlyIf hr =>
                obtain ⟨rs2, mkTl, hc2, hsk2, hbnd2, hgl2, hemb2⟩ :=
                  ihIs (k + 1) i0 m0 dks0 nds0 hsz0 (Nat.succ_le_of_lt hkLt) hdrRest hr hkl0
                exact ⟨rs2, mkTl, hc2, hsk2, hbnd2, hgl2, fun els toks off he =>
                  let ⟨hfhe, hfor, hlen, hrel, hsq⟩ := hemb2 els toks off he
                  ⟨hfhe, hfor, hlen, hrel, fun k0 => .onlyIf (hsq k0)⟩⟩
              | phrase hp _ => exact nomatch hp
              | @term _ _ _ x o _ _ h0 _ mr dksr htm hr =>
                have hszR : sizeOf dksr ≤ sizeOf dks := by
                  simp +arith only [List.cons.sizeOf_spec] at hsz0; omega
                obtain ⟨st1, hsg1, hc1, htm1⟩ := embedsAt_term_tokenAlphabet hok hsSpec hkLt htm hvsUniq
                obtain ⟨rs2, mkTl, hc2, hsk2, hbnd2, hgl2, hemb2⟩ :=
                  ihIs (k + 1) h0 mr dksr nds0 hszR (Nat.succ_le_of_lt hkLt) hdrRest hr hkl0
                refine ⟨[st1] ++ rs2, fun off => .leaf off (off + 1) :: mkTl (off + 1),
                  hc1.append hc2,
                  fun off => ?_,
                  fun bnds off hb => dtreeBndsMatchList_prepend hc1 hb
                    (fun hb1 => ⟨rfl, (hb1 0 (Nat.zero_le _)).symm, hc1.rawBndAt_end.symm.trans (hb1 1 (Nat.le_refl _)).symm⟩)
                    (hbnd2 bnds (off + 1)),
                  fun off => inKids_prepend (r1 := [st1])
                    (fun u hu => by simp only [List.length_singleton] at hu; obtain rfl : u = 0 := (by omega); simp [Tree.goalAt, hsg1])
                    (leaf_goalAt_one off).2 (hgl2 (off + 1)).1 (hgl2 (off + 1)).2,
                  fun els toks off he => ?_⟩
                · rw [List.length_append, List.length_singleton, ← Nat.add_assoc]
                  exact .cons rfl (.leaf off) (hsk2 (off + 1))
                · obtain ⟨he1, he2⟩ := he.split_append hc1
                  obtain ⟨hfhe2, hfor2, hlen2, hrel2, hsq2⟩ := hemb2 els toks (off + 1) he2
                  refine ⟨⟨trivial, hfhe2⟩, ?_, by simpa [Tree.isLeaf] using hlen2,
                    by simpa [Tree.isLeaf] using hrel2, fun k0 => ?_⟩
                  · intro hn d hd hntD
                    rcases List.mem_cons.mp hd with rfl | hmem
                    · cases hntD
                    · exact hfor2 hn d hmem hntD
                  · rw [List.length_append, List.length_singleton, ← Nat.add_assoc]
                    exact .term (htm1 els toks off he1) (hsq2 k0)
              | @butNotT _ _ _ x ex _ _ h0 _ _ dksr htm hex hr =>
                have hszR : sizeOf dksr ≤ sizeOf dks := by
                  simp +arith only [List.cons.sizeOf_spec] at hsz0; omega
                have hitOk := hallOk _ (List.mem_cons_self ..)
                have hsynEx : ¬ SynExcluded Ecma.Spec.gl cx Engine.Model.codePrims cs.toList first vs s k i0 h0 ex :=
                  fun hx => hex ((synExcl_iff hok hcp hvs hsSpec hkLt hitOk ps i0 h0).mpr hx)
                have hsynT := (synTermFast_iff_synTerm hok hsSpec hkLt x i0 h0).mp htm
                have hpF : vsPending vs i0 = false := by
                  cases hp : vsPending vs i0 with
                  | false => rfl
                  | true =>
                    unfold SynTerm at hsynT
                    cases x with
                    | cp _ => cases hsynT
                    | text _ _ =>
                      simp only [hp, ↓reduceIte] at hsynT
                      obtain ⟨c, cls, hctor, hsem, _⟩ := hsynT.2.1
                      obtain ⟨_, _, hcontra⟩ := synSrc_semis_imp hok hsSpec hkLt hctor hsem
                      rw [hrhsK] at hcontra; cases hcontra
                obtain ⟨st1, hsg1, hc1, htm1⟩ := embedsAt_term_tokenAlphabet hok hsSpec hkLt htm hvsUniq
                obtain ⟨a0, b0, lt0, tr0, hsc0, hnc0, htxt0, hh0Eq⟩ :
                    ∃ a b lt tr, ScanTok Ecma.Spec.gl cx Engine.Model.codePrims cs.toList first .InputElementDiv (i0 / 2) a b lt tr ∧
                      noCross vs (i0 / 2) b = true ∧ (∃ str b_, x = .text str b_ ∧ slice cs.toList a b = str.toList.map Char.toNat) ∧ h0 = 2 * b := by
                  unfold SynTerm at hsynT
                  cases x with
                  | cp _ => cases hsynT
                  | text str b_ =>
                    simp only [hpF, Bool.false_eq_true, ↓reduceIte] at hsynT
                    obtain ⟨a, b, lt, tr, hsc, hnc, htxt, hhEq⟩ := hsynT
                    exact ⟨a, b, lt, tr, hsc, hnc, ⟨str, b_, rfl, htxt⟩, hhEq⟩
                obtain ⟨rs2, mkTl, hc2, hsk2, hbnd2, hgl2, hemb2⟩ :=
                  ihIs (k + 1) h0 m0 dksr nds0 hszR (Nat.succ_le_of_lt hkLt) hdrRest hr hkl0
                refine ⟨[st1] ++ rs2, fun off => .leaf off (off + 1) :: mkTl (off + 1),
                  hc1.append hc2,
                  fun off => ?_,
                  fun bnds off hb => dtreeBndsMatchList_prepend hc1 hb
                    (fun hb1 => ⟨rfl, (hb1 0 (Nat.zero_le _)).symm, hc1.rawBndAt_end.symm.trans (hb1 1 (Nat.le_refl _)).symm⟩)
                    (hbnd2 bnds (off + 1)),
                  fun off => inKids_prepend (r1 := [st1])
                    (fun u hu => by simp only [List.length_singleton] at hu; obtain rfl : u = 0 := (by omega); simp [Tree.goalAt, hsg1])
                    (leaf_goalAt_one off).2 (hgl2 (off + 1)).1 (hgl2 (off + 1)).2,
                  fun els toks off he => ?_⟩
                · rw [List.length_append, List.length_singleton, ← Nat.add_assoc]
                  exact .cons rfl (.leaf off) (hsk2 (off + 1))
                · obtain ⟨he1, he2⟩ := he.split_append hc1
                  obtain ⟨hfhe2, hfor2, hlen2, hrel2, hsq2⟩ := hemb2 els toks (off + 1) he2
                  have hoffLt : off < toks.length := by have := he1.2.1; simp at this; omega
                  have hb0Bnd : tokBnd els toks off = i0 := by simpa [rawBndAt] using he1.2.2.1 0 (Nat.zero_le _)
                  have hb1Bnd : tokBnd els toks (off + 1) = h0 :=
                    (he1.2.2.1 1 (Nat.le_refl _)).trans (by simpa using hc1.rawBndAt_end)
                  -- Extract `toks[off] = ⟨slice cs.toList a0 b0, lt0, none⟩`:
                  have htokOff : toks[off] = ⟨slice cs.toList a0 b0, lt0, none⟩ := by
                    have hsm := he1.2.2.2 0 (by simp)
                    simp only [Nat.add_zero, List.getElem_singleton] at hsm
                    cases st1 with
                    | virt pv =>
                      cases hc1 with
                      | virt hmP _ =>
                        have hpend : vsPending vs (2 * pv) = true :=
                          (vsPending_iff vs (2 * pv)).mpr ⟨by omega, (pv, vsParen vs pv), hmP, by omega⟩
                        rw [hpF] at hpend; cases hpend
                    | real pv av bv ltv lgv trv =>
                      cases hc1 with
                      | real hpv _ _ hlgv hscv _ =>
                        dsimp only [StepMatchesTok] at hsm
                        dsimp only [RawStep.goal] at hsg1
                        have hscvDiv : ScanTok Ecma.Spec.gl cx Engine.Model.codePrims cs.toList first .InputElementDiv (i0 / 2) av bv ltv trv := by
                          rw [hsg1, hpv] at hscv; exact hscv
                        obtain ⟨rfl, rfl, rfl⟩ := scanTok_span_unique hok hcp hsc0 hscvDiv
                        exact Option.some.inj ((List.getElem?_eq_getElem hoffLt).symm.trans hsm)
                  have hvNone : toks[off].virt = none := by rw [htokOff]
                  refine ⟨⟨trivial, hfhe2⟩, ?_, by simpa [Tree.isLeaf] using hlen2,
                    by simpa [Tree.isLeaf] using hrel2, fun k0 => ?_⟩
                  · intro hn d hd hntD
                    rcases List.mem_cons.mp hd with rfl | hmem
                    · cases hntD
                    · exact hfor2 hn d hmem hntD
                  · rw [List.length_append, List.length_singleton, ← Nat.add_assoc]
                    refine .butNotT (htm1 els toks off he1) (fun hexT => hsynEx ?_) (hsq2 k0)
                    rw [← hb0Bnd, ← hb1Bnd]
                    let ⟨hinv1⟩ := he1.1
                    exact (excl_token_iff_synExcluded hok hcp hinv1 hsSpec hkLt hrhsK hoffLt hvNone
                      ⟨a0, b0, lt0, tr0, hb0Bnd.symm ▸ hsc0, hb1Bnd.trans hh0Eq, htokOff⟩ k0 ps).mp hexT
              | @leaf _ _ _ m args o _ _ h0 _ mr dksr hem hl hkKeep _ hr =>
                have hszR : sizeOf dksr ≤ sizeOf dks := by
                  simp +arith only [List.cons.sizeOf_spec] at hsz0; omega
                have hnlLex : (!(DTree.lex m i0 h0).isLeaf) = true := rfl
                simp only [List.filter_cons, hnlLex, ↓reduceIte] at hkl0
                cases hkl0 with
                | @cons cNd _ ndsr _ hhdRel hklr =>
                  cases hhdRel with
                  | lex _ _ _ _ hlnr =>
                    obtain ⟨hnp, a0, b0, lt0, tr0, tLex, hh0Eq, hnc0, hsc0, hsynSp0, hderLex0, hnrel0⟩ := hlnr
                    have hntLex : tLex.nt? = some m := derives_code_nt? hderLex0
                    have hnilM : Ecma.Spec.gl.alts cx .syntactic m = [] :=
                      List.isEmpty_iff.mp ((altsOf_eq hok cx .syntactic m) ▸ hem)
                    have ⟨_, hnoCA⟩ := noCondAfter_of_synItems (fun x hx => hallOk x (List.mem_cons_of_mem _ hx))
                    let st1 : RawStep := .real (i0 / 2) a0 b0 lt0 (lexicalGoalOf m) tr0
                    have hc1 : RawChain cx cs first vs i0 h0 [st1] :=
                      hh0Eq ▸ .real rfl hnp hnc0 (isSynLexGoal_lexicalGoalOf m) hsc0 (.nil _)
                    obtain ⟨rs2, mkTl, hc2, hsk2, hbnd2, hgl2, hemb2⟩ :=
                      ihIs (k + 1) h0 mr dksr ndsr hszR (Nat.succ_le_of_lt hkLt) hdrRest hr hklr
                    refine ⟨[st1] ++ rs2, fun off => .lex off tLex :: mkTl (off + 1),
                      hc1.append hc2,
                      fun off => ?_,
                      fun bnds off hb => dtreeBndsMatchList_prepend hc1 hb
                        (fun hb1 => ⟨rfl, (hb1 0 (Nat.zero_le _)).symm, hc1.rawBndAt_end.symm.trans (hb1 1 (Nat.le_refl _)).symm⟩)
                        (hbnd2 bnds (off + 1)),
                      fun off => inKids_prepend (r1 := [st1])
                        (fun u hu => by simp only [List.length_singleton] at hu; obtain rfl : u = 0 := (by omega); simp [Tree.goalAt, hntLex, st1, RawStep.goal])
                        (lex_goalAt_one off hntLex).2
                        (hgl2 (off + 1)).1 (hgl2 (off + 1)).2,
                      fun els toks off he => ?_⟩
                    · rw [List.length_append, List.length_singleton, ← Nat.add_assoc]
                      exact .cons rfl (.lex off hntLex) (hsk2 (off + 1))
                    · obtain ⟨he1, he2⟩ := he.split_append hc1
                      obtain ⟨hfhe2, hfor2, hlen2, hrel2, hsq2⟩ := hemb2 els toks (off + 1) he2
                      have hoffLt : off < toks.length := by have := he1.2.1; simp at this; omega
                      have hgetOff : toks[off]? = some ⟨slice cs.toList a0 b0, lt0, none⟩ := by
                        simpa [StepMatchesTok] using he1.2.2.2 0 (by simp)
                      have hb0Bnd : tokBnd els toks off = i0 := by simpa [rawBndAt] using he1.2.2.1 0 (Nat.zero_le _)
                      have hb1Bnd : tokBnd els toks (off + 1) = h0 :=
                        (he1.2.2.1 1 (Nat.le_refl _)).trans (by simpa using hc1.rawBndAt_end)
                      have hspEq0 : Ecma.Grammar.tokenSpan els toks off (off + 1) = (a0, b0) := by
                        let ⟨hinv1⟩ := he1.1
                        rw [hinv1.tokenSpan_eq_synSpanOf hok hcp (by omega) (by omega), hb0Bnd, hb1Bnd, hsynSp0]
                      have hlenSl : (slice cs.toList a0 b0).length = b0 - a0 := by
                        unfold slice; rw [List.length_take, List.length_drop]; have := hsc0.2.1; have := hsc0.2.2.1; omega
                      have hnlT : (!(Tree.lex off tLex).isLeaf) = true := rfl
                      refine ⟨⟨trivial, hfhe2⟩, ?_, by simp [hnlT, hlen2], ?_, fun k0 => ?_⟩
                      · intro hn d hd hntD tok htok
                        rcases List.mem_cons.mp hd with rfl | hmem
                        · dsimp only [Tree.span] at htok
                          rw [Nat.add_sub_cancel, hgetOff] at htok
                          injection htok with heq; exact heq ▸ rfl
                        · exact hfor2 hn d hmem hntD tok htok
                      · intro idx tk ck htk hck
                        simp only [List.filter_cons, hnlT, ↓reduceIte] at htk
                        cases idx with
                        | zero =>
                          simp only [List.getElem?_cons_zero, Option.some.injEq] at htk hck
                          subst htk; subst hck
                          exact .lex (by simpa [hspEq0] using hnrel0)
                        | succ idx' =>
                          simp only [List.getElem?_cons_succ] at htk hck
                          exact hrel2 idx' tk ck htk hck
                      · rw [List.length_append, List.length_singleton, ← Nat.add_assoc]
                        refine .nt (.lex hnilM hgetOff ⟨rfl, by dsimp only; rwa [hlenSl]⟩)
                          (by
                            have hnc := (noCondAfter_of_synItems (fun x hx => hallOk x (List.mem_cons_of_mem _ hx))).1
                            cases rest with
                            | nil => trivial
                            | cons hd _ => cases hd <;> simp [noCondAfter, CondOk] at hnc ⊢)
                          (hsq2 k0)
              | @butNotLeaf _ _ _ m args ex _ _ h0 _ _ dksr hem hl _ hex hr =>
                have hszR : sizeOf dksr ≤ sizeOf dks := by
                  simp +arith only [List.cons.sizeOf_spec] at hsz0; omega
                have hitOk := hallOk _ (List.mem_cons_self ..)
                have hsynEx : ¬ SynExcluded Ecma.Spec.gl cx Engine.Model.codePrims cs.toList first vs s k i0 h0 ex :=
                  fun hx => hex ((synExcl_iff hok hcp hvs hsSpec hkLt hitOk ps i0 h0).mpr hx)
                have hdivBase : lexicalGoalOf m = .InputElementDiv := by
                  have hd := synSrc_butNot_divOk hsSpec (List.mem_of_getElem? hrhsK)
                  dsimp only [itemButNotDivOk] at hd
                  exact beq_iff_eq.mp (Bool.and_eq_true_iff.mp hd).1
                have hnlLex : (!(DTree.lex m i0 h0).isLeaf) = true := rfl
                simp only [List.filter_cons, hnlLex, ↓reduceIte] at hkl0
                cases hkl0 with
                | @cons cNd _ ndsr _ hhdRel hklr =>
                  cases hhdRel with
                  | lex _ _ _ _ hlnr =>
                    obtain ⟨hnp, a0, b0, lt0, tr0, tLex, hh0Eq, hnc0, hsc0, hsynSp0, hderLex0, hnrel0⟩ := hlnr
                    have hntLex : tLex.nt? = some m := derives_code_nt? hderLex0
                    have hnilM : Ecma.Spec.gl.alts cx .syntactic m = [] :=
                      List.isEmpty_iff.mp ((altsOf_eq hok cx .syntactic m) ▸ hem)
                    let st1 : RawStep := .real (i0 / 2) a0 b0 lt0 (lexicalGoalOf m) tr0
                    have hc1 : RawChain cx cs first vs i0 h0 [st1] :=
                      hh0Eq ▸ .real rfl hnp hnc0 (isSynLexGoal_lexicalGoalOf m) hsc0 (.nil _)
                    obtain ⟨rs2, mkTl, hc2, hsk2, hbnd2, hgl2, hemb2⟩ :=
                      ihIs (k + 1) h0 m0 dksr ndsr hszR (Nat.succ_le_of_lt hkLt) hdrRest hr hklr
                    refine ⟨[st1] ++ rs2, fun off => .lex off tLex :: mkTl (off + 1),
                      hc1.append hc2,
                      fun off => ?_,
                      fun bnds off hb => dtreeBndsMatchList_prepend hc1 hb
                        (fun hb1 => ⟨rfl, (hb1 0 (Nat.zero_le _)).symm, hc1.rawBndAt_end.symm.trans (hb1 1 (Nat.le_refl _)).symm⟩)
                        (hbnd2 bnds (off + 1)),
                      fun off => inKids_prepend (r1 := [st1])
                        (fun u hu => by simp only [List.length_singleton] at hu; obtain rfl : u = 0 := (by omega); simp [Tree.goalAt, hntLex, st1, RawStep.goal])
                        (lex_goalAt_one off hntLex).2
                        (hgl2 (off + 1)).1 (hgl2 (off + 1)).2,
                      fun els toks off he => ?_⟩
                    · rw [List.length_append, List.length_singleton, ← Nat.add_assoc]
                      exact .cons rfl (.lex off hntLex) (hsk2 (off + 1))
                    · obtain ⟨he1, he2⟩ := he.split_append hc1
                      obtain ⟨hfhe2, hfor2, hlen2, hrel2, hsq2⟩ := hemb2 els toks (off + 1) he2
                      have hoffLt : off < toks.length := by have := he1.2.1; simp at this; omega
                      have hgetOff : toks[off]? = some ⟨slice cs.toList a0 b0, lt0, none⟩ := by
                        simpa [StepMatchesTok] using he1.2.2.2 0 (by simp)
                      have htokOff : toks[off] = ⟨slice cs.toList a0 b0, lt0, none⟩ :=
                        Option.some.inj ((List.getElem?_eq_getElem hoffLt).symm.trans hgetOff)
                      have hvNone : toks[off].virt = none := by rw [htokOff]
                      have hb0Bnd : tokBnd els toks off = i0 := by simpa [rawBndAt] using he1.2.2.1 0 (Nat.zero_le _)
                      have hb1Bnd : tokBnd els toks (off + 1) = h0 :=
                        (he1.2.2.1 1 (Nat.le_refl _)).trans (by simpa using hc1.rawBndAt_end)
                      have hspEq0 : Ecma.Grammar.tokenSpan els toks off (off + 1) = (a0, b0) := by
                        let ⟨hinv1⟩ := he1.1
                        rw [hinv1.tokenSpan_eq_synSpanOf hok hcp (by omega) (by omega), hb0Bnd, hb1Bnd, hsynSp0]
                      have hlenSl : (slice cs.toList a0 b0).length = b0 - a0 := by
                        unfold slice; rw [List.length_take, List.length_drop]; have := hsc0.2.1; have := hsc0.2.2.1; omega
                      have hnlT : (!(Tree.lex off tLex).isLeaf) = true := rfl
                      refine ⟨⟨trivial, hfhe2⟩, ?_, by simp [hnlT, hlen2], ?_, fun k0 => ?_⟩
                      · intro hn d hd hntD tok htok
                        rcases List.mem_cons.mp hd with rfl | hmem
                        · dsimp only [Tree.span] at htok
                          rw [Nat.add_sub_cancel, hgetOff] at htok
                          injection htok with heq; exact heq ▸ rfl
                        · exact hfor2 hn d hmem hntD tok htok
                      · intro idx tk ck htk hck
                        simp only [List.filter_cons, hnlT, ↓reduceIte] at htk
                        cases idx with
                        | zero =>
                          simp only [List.getElem?_cons_zero, Option.some.injEq] at htk hck
                          subst htk; subst hck
                          exact .lex (by simpa [hspEq0] using hnrel0)
                        | succ idx' =>
                          simp only [List.getElem?_cons_succ] at htk hck
                          exact hrel2 idx' tk ck htk hck
                      · rw [List.length_append, List.length_singleton, ← Nat.add_assoc]
                        refine .butNotN (.lex hnilM hgetOff ⟨rfl, by dsimp only; rwa [hlenSl]⟩) (fun hexT => hsynEx ?_) (hsq2 k0)
                        rw [← hb0Bnd, ← hb1Bnd]
                        let ⟨hinv1⟩ := he1.1
                        exact (excl_token_iff_synExcluded hok hcp hinv1 hsSpec hkLt hrhsK hoffLt hvNone
                          ⟨a0, b0, lt0, tr0, hb0Bnd.symm ▸ (hdivBase ▸ hsc0), hb1Bnd.trans hh0Eq, htokOff⟩ k0 ps).mp hexT
              | butNotN hem _ _ _ _ =>
                have hitOk := hallOk _ (List.mem_cons_self ..)
                dsimp only [synItemOk] at hitOk
                simp only [Bool.and_eq_true] at hitOk
                dsimp only [Syntax.alpha] at hem
                rw [altsOf_eq hok, ← glData_eq, hitOk.1] at hem
                cases hem
              | @nt _ _ _ m args o _ _ h0 _ mr dk dksr hem hd0 hkKeep _ hr =>
                have hszDk : sizeOf dk < sz := by
                  simp +arith only [List.cons.sizeOf_spec] at hsz0; omega
                have hszR : sizeOf dksr ≤ sizeOf dks := by
                  simp +arith only [List.cons.sizeOf_spec] at hsz0; omega
                have hnlDk : (!dk.isLeaf) = true := by cases hd0; rfl
                simp only [List.filter_cons, hnlDk, ↓reduceIte] at hkl0
                cases hkl0 with
                | @cons cNd _ ndsr _ hhdRel hklr =>
                  obtain ⟨rs1, mkHd, hc1, hsk1, hbnd1, hspHd, hgl1, hemb1⟩ :=
                    ihOuter (sizeOf dk) hszDk (Nat.le_refl _) hd0 hhdRel
                  obtain ⟨rs2, mkTl, hc2, hsk2, hbnd2, hgl2, hemb2⟩ :=
                    ihIs (k + 1) h0 mr dksr ndsr hszR (Nat.succ_le_of_lt hkLt) hdrRest hr hklr
                  refine ⟨rs1 ++ rs2, fun off => mkHd off :: mkTl (off + rs1.length),
                    hc1.append hc2,
                    fun off => ?_,
                    fun bnds off hb => dtreeBndsMatchList_prepend hc1 hb (hbnd1 bnds off) (hbnd2 bnds (off + rs1.length)),
                    fun off => inKids_prepend (hgl1 off).1 (hgl1 off).2 (hgl2 (off + rs1.length)).1 (hgl2 (off + rs1.length)).2,
                    fun els toks off he => ?_⟩
                  · rw [List.length_append, ← Nat.add_assoc]
                    exact .cons (hspHd off).1 (hsk1 off) (hsk2 (off + rs1.length))
                  · obtain ⟨he1, he2⟩ := he.split_append hc1
                    obtain ⟨hfhe1, hnrel1, hder1⟩ := hemb1 els toks off he1
                    obtain ⟨hfhe2, hfor2, hlen2, hrel2, hsq2⟩ := hemb2 els toks (off + rs1.length) he2
                    have hnlT : (!(mkHd off).isLeaf) = true := by rw [(hspHd off).2.2]; rfl
                    refine ⟨⟨hfhe1, hfhe2⟩, ?_, by simp [hnlT, hlen2], ?_, fun k0 => ?_⟩
                    · intro hn d hd hntD tok htok
                      rcases List.mem_cons.mp hd with rfl | hmem
                      · have hnEq : n = .ForStatement := beq_iff_eq.mp hn
                        have hmEq : m = .LexicalDeclaration := Option.some.inj ((hspHd off).2.1.symm.trans hntD)
                        subst hnEq; subst hmEq
                        dsimp only [Syntax.alpha] at hkKeep
                        rw [hlhsS] at hkKeep
                        unfold forKeep at hkKeep
                        have hh0Even : h0 % 2 = 0 := by
                          cases hev : h0 % 2 == 1 with
                          | false => simp at hev; omega
                          | true => simp [hev] at hkKeep
                        have hposLD := lexicalDeclaration_pos hok hcp hvs hd0
                        have hrs1Ne : rs1 ≠ [] := by
                          intro hnil; subst hnil; cases hc1; omega
                        obtain ⟨pL, aL, bL, ltL, lgL, trL, hlastR⟩ := hc1.even_end_last_not_virt hrs1Ne hh0Even
                        have hlenPos : 0 < rs1.length := List.length_pos_iff.mpr hrs1Ne
                        have hidxLt : rs1.length - 1 < rs1.length := by omega
                        have hrLastEq : rs1[rs1.length - 1]'hidxLt = .real pL aL bL ltL lgL trL :=
                          Option.some.inj ((List.getElem?_eq_getElem hidxLt).symm.trans hlastR)
                        have hsm := he1.2.2.2 (rs1.length - 1) hidxLt
                        rw [hrLastEq] at hsm; dsimp only [StepMatchesTok] at hsm
                        rw [(hspHd off).1] at htok; dsimp only at htok
                        rw [show off + rs1.length - 1 = off + (rs1.length - 1) from by omega, hsm] at htok
                        injection htok with heq; exact heq ▸ rfl
                      · exact hfor2 hn d hmem hntD tok htok
                    · intro idx tk ck htk hck
                      simp only [List.filter_cons, hnlT, ↓reduceIte] at htk
                      cases idx with
                      | zero =>
                        simp only [List.getElem?_cons_zero, Option.some.injEq] at htk hck
                        subst htk; subst hck; exact hnrel1
                      | succ idx' =>
                        simp only [List.getElem?_cons_succ] at htk hck
                        exact hrel2 idx' tk ck htk hck
                    · rw [List.length_append, ← Nat.add_assoc]
                      exact .nt (hder1 k0)
                        (by
                          have hnc := (noCondAfter_of_synItems (fun x hx => hallOk x (List.mem_cons_of_mem _ hx))).1
                          cases rest with
                          | nil => trivial
                          | cons hd _ => cases hd <;> simp [noCondAfter, CondOk] at hnc ⊢)
                        (hsq2 k0)
          obtain ⟨rs, mkKids, hc, hsk, hbnd, hgl, hemb⟩ :=
            hseq s.alt.rhs 0 i mask dks ((Engine.builder.kids nd).toList.filterMap Prod.snd)
              (Nat.le_refl _) (Nat.zero_le _) rfl hsw hkl
          refine ⟨rs, fun off => .node n pId ps off (off + rs.length) (mkKids off),
            hc,
            fun off => .node (hsk off),
            fun bnds off hb => ⟨(hb 0 (Nat.zero_le _)).symm,
              hc.rawBndAt_end.symm.trans (hb rs.length (Nat.le_refl _)).symm, hbnd bnds off hb⟩,
            fun off => ⟨rfl, rfl, rfl⟩,
            fun off => hgl off,
            fun els toks off he => ?_⟩
          obtain ⟨hfheK, hforK, hlenK, hrelK, hsqK⟩ := hemb els toks off he
          refine ⟨⟨hforK, hfheK⟩, ?_, fun k0 => .node s hsSpec hgrd hpidSpec (hsqK k0)⟩
          -- Assemble `Ecma.Model.NodeRel` for `nd`:
          rcases nd with ⟨st0, lo, hi, p0, nt0, ps0, ks0, txt0⟩
          dsimp only [Engine.builder] at hnt hprod hargs hstNd hspNd htxtNd hlenK hrelK
          dsimp only [S, synAlphaSpec] at hspNd htxtNd
          have hb0Bnd : tokBnd els toks off = i := by simpa [rawBndAt] using he.2.2.1 0 (Nat.zero_le _)
          have hb1Bnd : tokBnd els toks (off + rs.length) = j := by
            simpa [hc.rawBndAt_end] using he.2.2.1 rs.length (Nat.le_refl _)
          have hspEq : Ecma.Grammar.tokenSpan els toks off (off + rs.length) = synSpanOf cs first cx i j := by
            let ⟨hinv⟩ := he.1
            rw [hinv.tokenSpan_eq_synSpanOf hok hcp (Nat.le_add_right _ _) he.2.1, hb0Bnd, hb1Bnd]
          refine .node hnt hprod (by rw [hargs]; exact fun _ => Iff.rfl) hstNd (hspNd.trans hspEq.symm) ?_ ?_ ?_ ?_ ?_
          · show Engine.Model.MathVal.int (txt0.toArray.map Engine.Impl.ofNat).size =
              Engine.Model.MathVal.int (slice cs.toList (Ecma.Grammar.tokenSpan els toks off (off + rs.length)).1
                (Ecma.Grammar.tokenSpan els toks off (off + rs.length)).2).length
            simp only [Array.size_map, htxtNd, ← hspEq, ← extract_toList_eq_slice, Array.length_toList]
          · intro k
            rw [impl_seqGet_nat]
            show (txt0.toArray.map Engine.Impl.ofNat)[k]? =
              (slice cs.toList (Ecma.Grammar.tokenSpan els toks off (off + rs.length)).1
                (Ecma.Grammar.tokenSpan els toks off (off + rs.length)).2)[k]?.map Engine.Impl.ofNat
            rw [Array.getElem?_map, htxtNd, ← hspEq, ← extract_toList_eq_slice, Array.getElem?_toList]
          · show Engine.Model.MathVal.int (ks0.filterMap Prod.snd).size =
              Engine.Model.MathVal.int ((mkKids off).filter (fun t => !t.isLeaf)).length
            rw [← Array.length_toList, Array.toList_filterMap, hlenK]
          · intro k
            rw [impl_seqGet_nat]
            change ((ks0.filterMap Prod.snd)[k]?.isSome = true) = (k < ((mkKids off).filter (fun t => !t.isLeaf)).length)
            rw [← Array.getElem?_toList, Array.toList_filterMap, ← hlenK]
            rcases opt_none_or_some ((ks0.toList.filterMap Prod.snd)[k]?) with hnone | ⟨_, hsome⟩
            · have hge := List.getElem?_eq_none_iff.mp hnone
              rw [hnone]; simp [show ¬ k < (ks0.toList.filterMap Prod.snd).length from by omega]
            · have hlt := (List.getElem?_eq_some_iff.mp hsome).1
              rw [hsome]; simp [hlt]
          · intro k tk ck htk hck
            rw [impl_seqGet_nat] at hck
            change (ks0.filterMap Prod.snd)[k]? = some ck at hck
            rw [← Array.getElem?_toList, Array.toList_filterMap] at hck
            exact hrelK k tk ck htk hck
  intro n ps i j dt nd hpl hdrel
  exact hmain (sizeOf dt) (Nat.le_refl _) hpl hdrel

/-! ### Building `(els, toks)` from `RawChain` (`build_tokStream_of_rawChain`) -/

private theorem rawChain_crosses_vs {cx : Ctx} {cs : Array Nat} {first : Bool} {vs : List (Nat × Bool)}
    {cur e : Nat} {rs : List RawStep}
    (hc : RawChain cx cs first vs cur e rs)
    (hnpEnd : vsPending vs e = false)
    {q : Nat} {paren : Bool} (hqMem : (q, paren) ∈ vs)
    (hcurLe : cur ≤ 2 * q) (hqLe : q ≤ e / 2) :
    ∃ (u : Nat) (hu : u < rs.length), rs[u]'hu = .virt q := by
  have hpend2q : vsPending vs (2 * q) = true :=
    (vsPending_iff vs (2 * q)).mpr ⟨by omega, (q, paren), hqMem, by omega⟩
  induction hc with
  | nil c0 =>
    have hcEq : c0 = 2 * q := by omega
    subst hcEq; rw [hpend2q] at hnpEnd; cases hnpEnd
  | @virt p _ rs0 _ hr ih =>
    by_cases hpq : p = q
    · subst hpq; exact ⟨0, by simp, rfl⟩
    · obtain ⟨u, hu, heq⟩ := ih hnpEnd (by omega) hqLe
      exact ⟨u + 1, Nat.succ_lt_succ hu, heq⟩
  | @real c0 p a b _ lt lg tr rs0 hpEq hnp hnc _ _ hr ih =>
    have hcNe : c0 ≠ 2 * q := fun heq => by subst heq; rw [hpend2q] at hnp; cases hnp
    have hpLtQ : p < q := by omega
    have hnotLt : ¬ (q < b) := by
      intro hltB
      have h1 := List.all_eq_true.mp hnc (q, paren) hqMem
      simp [hpLtQ, hltB] at h1
    obtain ⟨u, hu, heq⟩ := ih hnpEnd (by omega) hqLe
    exact ⟨u + 1, Nat.succ_lt_succ hu, heq⟩

private theorem rawChain_build_aux (hok : parseTablesOk = true) {cx : Ctx} {cs : Array Nat}
    (hcp : ∀ c ∈ cs.toList, c ≤ 0x10FFFF) {first : Bool} {vs : List (Nat × Bool)}
    {cur e : Nat} {rs : List RawStep}
    (hc : RawChain cx cs first vs cur e rs) :
    ∃ (blocks : List TokBlock) (toks : List Token),
      BlocksChain (cur / 2) (e / 2) blocks ∧
      (∀ blk ∈ blocks, ValidTokBlock cx cs first blk) ∧
      toks.filter (·.virt.isNone) =
        blocks.map (fun blk => ⟨slice cs.toList blk.tokEl.i blk.tokEl.j, blk.lt, none⟩) ∧
      toks.all (fun k => k.virt.isNone || !k.lt) = true ∧
      toks.length = rs.length ∧
      (∀ (u : Nat) (hu : u < rs.length), StepMatchesTok cs toks u (rs[u]'hu)) ∧
      (cur % 2 = 1 → ∀ t0, toks[0]? = some t0 → t0.virt = none) ∧
      (∀ k t1 t2, toks[k]? = some t1 → toks[k + 1]? = some t2 → t1.virt = none ∨ t2.virt = none) ∧
      (∀ u, u ≤ rs.length →
        let r := (toks.take u).countP (·.virt.isNone)
        let pos := if hr : r < blocks.length then (blocks[r]'hr).p else e / 2
        2 * pos + (if u == 0 then cur % 2 else if ((toks[u - 1]?).bind Token.virt).isSome then 1 else 0) =
          rawBndAt cur rs u) ∧
      (∀ k tok why, toks[k]? = some tok → tok.virt = some why →
        ∃ (hk : k < rs.length),
          let p := let r := (toks.take k).countP (·.virt.isNone);
            if hr : r < blocks.length then (blocks[r]'hr).p else e / 2
          rs[k]'hk = .virt p ∧
          why = (if vsParen vs p then .paren else if k + 1 == toks.length then .eof else .offending) ∧
          (p, vsParen vs p) ∈ vs) ∧
      (∀ r (hr : r < blocks.length),
        let u := realIdx r toks
        ∃ (hu : u < rs.length),
          (blocks[r]'hr).tokEl.goal =
            (if first && (blocks[r]'hr).tokEl.i == 0 then .InputElementHashbangOrRegExp else (rs[u]'hu).goal)) := by
  induction hc with
  | nil c0 =>
    refine ⟨[], [], .nil _, (fun _ h => nomatch h), rfl, rfl, rfl, (fun _ h => nomatch h),
      (fun _ _ h => nomatch h), (fun _ _ _ h _ => nomatch h), ?_, (fun _ _ _ h _ => nomatch h),
      (fun _ h => nomatch h)⟩
    intro u hu; simp only [List.length_nil] at hu; have hu0 : u = 0 := by omega
    subst hu0; dsimp only [rawBndAt]; simp; omega
  | @virt p e0 rs0 hpMem hr ih =>
    obtain ⟨bs0, toks0, hbc0, hv0, hfilt0, hall0, hlen0, hsm0, hodd0, hadj0, hbnd0, hvirt0, hgoal0⟩ := ih
    let why0 : Why := if vsParen vs p then .paren else if rs0.isEmpty then .eof else .offending
    let tok0 : Token := ⟨";".toList.map Char.toNat, false, some why0⟩
    have hpDiv : (2 * p) / 2 = p := by omega
    have hp1Div : (2 * p + 1) / 2 = p := by omega
    rw [hp1Div] at hbc0
    have hpos0Eq : (if hr0 : 0 < bs0.length then (bs0[0]'hr0).p else e0 / 2) = p := by
      have hb0 := hbnd0 0 (Nat.zero_le _)
      dsimp only [List.take, List.countP, List.countP.go, rawBndAt] at hb0
      simp only [beq_self_eq_true, ↓reduceIte] at hb0
      omega
    have hbc0' : BlocksChain ((2 * p) / 2) (e0 / 2) bs0 := by rw [hpDiv]; exact hbc0
    refine ⟨bs0, tok0 :: toks0, hbc0', hv0,
      by simpa [tok0] using hfilt0,
      by simp [tok0, hall0],
      by simp [hlen0],
      ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro u hu
      cases u with
      | zero => exact ⟨tok0, why0, rfl, rfl, rfl, rfl⟩
      | succ u' => exact hsm0 u' (by simp at hu; exact hu)
    · intro hodd; omega
    · intro k t1 t2 hg1 hg2
      cases k with
      | zero =>
        simp only [List.getElem?_cons_zero, List.getElem?_cons_succ] at hg1 hg2
        exact Or.inr (hodd0 (by omega) t2 hg2)
      | succ k' =>
        simp only [List.getElem?_cons_succ] at hg1 hg2
        exact hadj0 k' t1 t2 hg1 hg2
    · intro u hu
      cases u with
      | zero =>
        dsimp only [List.take, List.countP, List.countP.go, rawBndAt]
        rw [hpos0Eq]
        simp only [beq_self_eq_true, ↓reduceIte]
        omega
      | succ u' =>
        have hu' : u' ≤ rs0.length := by simp at hu; exact hu
        have hb' := hbnd0 u' hu'
        simp only [List.take_succ_cons, List.countP_cons, show tok0.virt.isNone = false from rfl,
          Bool.false_eq_true, ↓reduceIte, Nat.add_zero, beq_iff_eq, Nat.succ_ne_zero,
          Nat.add_sub_cancel, rawBndAt, RawStep.nextBnd]
        cases u' with
        | zero =>
          simp only [List.getElem?_cons_zero, Option.bind_some, show tok0.virt.isSome = true from rfl, ↓reduceIte]
          simpa [show (2 * p + 1) % 2 = 1 from by omega] using hb'
        | succ v =>
          simp only [List.getElem?_cons_succ]
          simpa [Nat.succ_ne_zero] using hb'
    · intro k tok why hgk hvk
      cases k with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hgk
        subst hgk
        dsimp only [tok0] at hvk; injection hvk with hwEq; subst hwEq
        refine ⟨by simp, ?_⟩
        have hisEm : (1 == rs0.length + 1) = rs0.isEmpty := by
          cases rs0 <;> simp
        simp [List.take, List.countP, List.countP.go, hlen0, hpos0Eq, hisEm, why0, hpMem]
      | succ k' =>
        simp only [List.getElem?_cons_succ] at hgk
        obtain ⟨hk', heqV, hwEq, hmV⟩ := hvirt0 k' tok why hgk hvk
        refine ⟨Nat.succ_lt_succ hk', ?_⟩
        simp only [List.take_succ_cons, List.countP_cons, show tok0.virt.isNone = false from rfl,
          Bool.false_eq_true, ↓reduceIte, Nat.add_zero, List.getElem_cons_succ, List.length_cons,
          show (k' + 1 + 1 == toks0.length + 1) = (k' + 1 == toks0.length) from by simp]
        exact ⟨heqV, hwEq, hmV⟩
    · intro r hr
      obtain ⟨hu0, hgEq0⟩ := hgoal0 r hr
      dsimp only
      have hri : realIdx r (tok0 :: toks0) = realIdx r toks0 + 1 := by
        cases r <;> simp [realIdx, tok0, Nat.add_comm 1]
      rw [hri]
      exact ⟨Nat.succ_lt_succ hu0, hgEq0⟩
  | @real c0 p a b e0 lt lg tr rs0 hpEq _ _ hlgSyn hsc hr ih =>
    obtain ⟨bs0, toks0, hbc0, hv0, hfilt0, hall0, hlen0, hsm0, _, hadj0, hbnd0, hvirt0, hgoal0⟩ := ih
    obtain ⟨triv0, hchTriv0, hvTriv0, hbrTriv0⟩ := trivia_chainEls hok hcp hsc.1
    let gEl : NT := if first && a == 0 then .InputElementHashbangOrRegExp else lg
    let tokEl0 : Element := ⟨a, b, gEl, tr⟩
    let blk0 : TokBlock := ⟨triv0, tokEl0, p, lt⟩
    let tok0 : Token := ⟨slice cs.toList a b, lt, none⟩
    have hbSz : b ≤ cs.size := by simpa using hsc.2.2.1
    have hvalid0 : ValidTokBlock cx cs first blk0 :=
      ⟨hchTriv0, hvTriv0, hbrTriv0, hsc.1, hsc.2.1, hbSz, hsc.2.2.2.1, lg, hlgSyn, rfl, hsc⟩
    have h2bDiv : (2 * b) / 2 = b := by omega
    rw [h2bDiv] at hbc0
    refine ⟨blk0 :: bs0, tok0 :: toks0, hpEq ▸ .cons blk0 rfl hbc0,
      fun blk hbm => by rcases List.mem_cons.mp hbm with rfl | hm; exact hvalid0; exact hv0 blk hm,
      by simp [tok0, blk0, tokEl0, hfilt0],
      by simp [tok0, hall0],
      by simp [hlen0],
      ?_, (fun _ _ ht => by simp only [List.getElem?_cons_zero, Option.some.injEq] at ht; exact ht ▸ rfl),
      ?_, ?_, ?_, ?_⟩
    · intro u hu
      cases u with
      | zero => exact rfl
      | succ u' => exact hsm0 u' (by simp at hu; exact hu)
    · intro k t1 t2 hg1 hg2
      cases k with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hg1
        exact Or.inl (hg1 ▸ rfl)
      | succ k' =>
        simp only [List.getElem?_cons_succ] at hg1 hg2
        exact hadj0 k' t1 t2 hg1 hg2
    · intro u hu
      cases u with
      | zero =>
        simp only [List.take_zero, List.countP_nil, List.length_cons, Nat.zero_lt_succ, ↓reduceDIte,
          List.getElem_cons_zero, beq_self_eq_true, ↓reduceIte, rawBndAt]
        dsimp only [blk0]; omega
      | succ u' =>
        have hu' : u' ≤ rs0.length := by simp at hu; exact hu
        have hb' := hbnd0 u' hu'
        have hcntS : ((tok0 :: toks0).take (u' + 1)).countP (·.virt.isNone) =
            (toks0.take u').countP (·.virt.isNone) + 1 := by
          simp [tok0]
        have hposS : (let r := ((tok0 :: toks0).take (u' + 1)).countP (·.virt.isNone);
            if hr : r < (blk0 :: bs0).length then ((blk0 :: bs0)[r]'hr).p else e0 / 2) =
            (let r0 := (toks0.take u').countP (·.virt.isNone);
            if hr0 : r0 < bs0.length then (bs0[r0]'hr0).p else e0 / 2) := by
          dsimp only
          rw [hcntS]
          by_cases hr0 : (toks0.take u').countP (·.virt.isNone) < bs0.length
          · simp [Nat.succ_lt_succ hr0, hr0]
          · simp [hr0]
        dsimp only at hposS hb' ⊢
        rw [hposS]
        simp only [beq_iff_eq, Nat.succ_ne_zero, ↓reduceIte, Nat.add_sub_cancel, rawBndAt, RawStep.nextBnd]
        cases u' with
        | zero =>
          simp only [List.getElem?_cons_zero, Option.bind_some, show tok0.virt.isSome = false from rfl,
            Bool.false_eq_true, ↓reduceIte]
          simpa [show (2 * b) % 2 = 0 from by omega] using hb'
        | succ v =>
          simp only [List.getElem?_cons_succ]
          simpa [Nat.succ_ne_zero] using hb'
    · intro k tok why hgk hvk
      cases k with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hgk
        subst hgk; cases hvk
      | succ k' =>
        simp only [List.getElem?_cons_succ] at hgk
        obtain ⟨hk', heqV, hwEq, hmV⟩ := hvirt0 k' tok why hgk hvk
        have hcntS : ((tok0 :: toks0).take (k' + 1)).countP (·.virt.isNone) =
            (toks0.take k').countP (·.virt.isNone) + 1 := by
          simp [tok0]
        have hposS : (let r := ((tok0 :: toks0).take (k' + 1)).countP (·.virt.isNone);
            if hr : r < (blk0 :: bs0).length then ((blk0 :: bs0)[r]'hr).p else e0 / 2) =
            (let r0 := (toks0.take k').countP (·.virt.isNone);
            if hr0 : r0 < bs0.length then (bs0[r0]'hr0).p else e0 / 2) := by
          dsimp only; rw [hcntS]
          by_cases hr0 : (toks0.take k').countP (·.virt.isNone) < bs0.length
          · simp [Nat.succ_lt_succ hr0, hr0]
          · simp [hr0]
        refine ⟨Nat.succ_lt_succ hk', ?_⟩
        dsimp only at hposS ⊢
        rw [hposS]
        simp only [List.getElem_cons_succ, List.length_cons,
          show (k' + 1 + 1 == toks0.length + 1) = (k' + 1 == toks0.length) from by simp]
        exact ⟨heqV, hwEq, hmV⟩
    · intro r hr
      cases r with
      | zero =>
        dsimp only [realIdx, tok0]
        refine ⟨by simp, ?_⟩
        simp [blk0, tokEl0, gEl, RawStep.goal]
      | succ r' =>
        have hr' : r' < bs0.length := by simp at hr; exact hr
        obtain ⟨hu0, hgEq0⟩ := hgoal0 r' hr'
        dsimp only
        have hri : realIdx (r' + 1) (tok0 :: toks0) = realIdx r' toks0 + 1 := by
          simp [realIdx, tok0, Nat.add_comm 1]
        rw [hri]
        exact ⟨Nat.succ_lt_succ hu0, hgEq0⟩

private theorem build_tokStream_of_rawChain (hok : parseTablesOk = true)
    {cx : Ctx} {cs : Array Nat} (hcp : ∀ c ∈ cs.toList, c ≤ 0x10FFFF)
    {goal : NT} {vs : List (Nat × Bool)} (hvs : ∀ pb ∈ vs, pb.1 ≤ cs.size)
    (hvsUniq : ∀ p b1 b2, (p, b1) ∈ vs → (p, b2) ∈ vs → b1 = b2)
    {e : Nat} {rs : List RawStep}
    (hc : RawChain cx cs (firstOf goal) vs 0 e rs)
    (heof : (Lex.skip Engine.builder cs (firstOf goal) cx (e / 2)).1 ≥ cs.size)
    (hnpEnd : vsPending vs e = false)
    (hallVs : vs.all (fun (q, _) => q ≤ e / 2) = true)
    {t : Tree}
    (htGoal : ∀ (u : Nat) (hu : u < rs.length), t.goalAt u = some (rs[u]'hu).goal) :
    ∃ (els : List Element) (toks : List Token) (_hinv : TokStreamInv cx cs (firstOf goal) vs els toks),
      EmbedsAt cx cs (firstOf goal) vs els toks 0 0 rs ∧
      toks.length = rs.length ∧
      GoalsAt goal els toks t := by
  let first := firstOf goal
  obtain ⟨blocks, toks, hbc, hval, hfilt, hall, hlen, hsm, _, hadj, hbnd, hvirt, hgoalBlk⟩ :=
    rawChain_build_aux hok hcp hc
  have heBound : e / 2 ≤ cs.size := by
    rcases rs with _ | ⟨hd, tl⟩
    · generalize hs0 : (0 : Nat) = s0 at hc
      cases hc; omega
    · have ⟨_, hle2⟩ := (hc.bound hok hcp hvs).2 (List.cons_ne_nil _ _)
      omega
  have ⟨_, hkLeSz, _, htrSk, elsEnd, hchEnd, hvEnd, _⟩ := skip_spec (cx := cx) hok hcp first (e / 2)
  have hskEqSz : (Lex.skip Engine.builder cs first cx (e / 2)).1 = cs.size :=
    Nat.le_antisymm (hkLeSz heBound) heof
  rw [hskEqSz] at htrSk hchEnd
  let els := (blocks.flatMap fun blk => blk.triv ++ [blk.tokEl]) ++ elsEnd
  have htoksFiltEls : toks.filter (·.virt.isNone) = tokensOf cs.toList els := by
    rw [hfilt, blocks_tokensOf hval hvEnd]
  -- Compute `tokPos els toks k` directly from `blocks`:
  have htokPosEq : ∀ k, tokPos els toks k =
      (let r := (toks.take k).countP (·.virt.isNone);
       if hr : r < blocks.length then (blocks[r]'hr).p else e / 2) := by
    intro k
    have hcntLe : (toks.take k).countP (·.virt.isNone) ≤ blocks.length := by
      have h1 : (toks.take k).countP (·.virt.isNone) ≤ toks.countP (·.virt.isNone) := by
        conv => rhs; rw [← List.take_append_drop k toks, List.countP_append]
        omega
      simp only [List.countP_eq_length_filter, hfilt, List.length_map] at h1 ⊢
      exact h1
    have hesEq : els.filter Element.isToken = blocks.map (·.tokEl) := blocks_filter_isToken hval hvEnd
    have ⟨_, hidx, hlast, hnil⟩ := blocksChain_pos_mono hbc hval
    unfold tokPos
    rw [hesEq]
    dsimp only
    generalize (toks.take k).countP (·.virt.isNone) = r at hcntLe ⊢
    by_cases hrLt : r < blocks.length
    · simp only [hrLt, ↓reduceDIte]
      obtain ⟨hprev, _⟩ := hidx r hrLt
      cases r with
      | zero => simpa using hprev
      | succ r' =>
        have hrNe : (r' + 1 == 0) = false := rfl
        simp only [hrNe, Bool.false_eq_true, ↓reduceIte, Nat.add_sub_cancel]
        have hr'Lt : r' < blocks.length := Nat.lt_of_succ_lt hrLt
        simp only [List.getElem?_map, List.getElem?_eq_getElem hr'Lt, Option.map_some, Option.getD_some]
        simpa using hprev
    · simp only [hrLt, ↓reduceDIte]
      have hrEq : r = blocks.length := by omega
      cases hblks : blocks with
      | nil =>
        have hr0 : r = 0 := by rw [hblks] at hrEq; exact hrEq
        have h0 := hnil hblks
        simp only [Nat.zero_div] at h0
        rw [hr0]; simpa using h0
      | cons b0 bs =>
        have hrNe : (r == 0) = false := beq_eq_false_iff_ne.mpr (by rw [hrEq, hblks]; simp)
        simp only [hrNe, Bool.false_eq_true, ↓reduceIte]
        have hrm1 : r - 1 < (b0 :: bs).length := by rw [hrEq, hblks]; simp
        simp only [List.getElem?_map, List.getElem?_eq_getElem hrm1, Option.map_some, Option.getD_some]
        have hlastEq := hlast (by rw [hblks]; exact List.cons_ne_nil _ _)
        have hgetEq : (b0 :: bs)[r - 1]'hrm1 = blocks[blocks.length - 1]'(by rw [hblks]; simp) := by
          cases hblks; congr 1; omega
        rw [hgetEq]; exact hlastEq
  have hasiMatch : toksMatchASI els toks vs := by
    refine ⟨hadj, fun k tok why hgk hvk => ?_, fun q paren hqMem => ?_⟩
    · obtain ⟨_, _, hwEq, hmV⟩ := hvirt k tok why hgk hvk
      rw [htokPosEq k]
      exact ⟨hwEq, hmV⟩
    · have hqLe : q ≤ e / 2 := by
        have h1 := List.all_eq_true.mp hallVs (q, paren) hqMem
        simpa using h1
      obtain ⟨u, hu, hruEq⟩ := rawChain_crosses_vs hc hnpEnd hqMem (Nat.zero_le _) hqLe
      have hsmU := hsm u hu
      rw [hruEq] at hsmU
      obtain ⟨tok, why, hgetU, _, _, hvirtU⟩ := hsmU
      obtain ⟨hu', hruEq', _, _⟩ := hvirt u tok why hgetU hvirtU
      have hpEqQ : tokPos els toks u = q := by
        rw [htokPosEq u]
        have := hruEq'.symm.trans hruEq
        injection this
      exact ⟨u, tok, hgetU, by rw [hvirtU]; rfl, hpEqQ⟩
  have hinv : TokStreamInv cx cs first vs els toks :=
    { blocks := blocks
      elsEnd := elsEnd
      endPos := e / 2
      endLt := (Lex.skip Engine.builder cs first cx (e / 2)).2
      hchain := hbc
      hvalid := hval
      hendChain := hchEnd
      hendValid := hvEnd
      hendTriv := htrSk
      helsEq := rfl
      htoksFilt := htoksFiltEls
      htoksAll := hall
      hasi := hasiMatch
      hvsBound := hvs
      hvsUniq := hvsUniq }
  have hemb : EmbedsAt cx cs first vs els toks 0 0 rs := by
    refine ⟨⟨hinv⟩, by omega, fun u hu => ?_, fun u hu => by simpa using hsm u hu⟩
    simp only [Nat.zero_add]
    unfold tokBnd
    rw [htokPosEq u]
    have hbU := hbnd u hu
    by_cases hu0 : u = 0
    · subst hu0; simpa using hbU
    · have hposU : 0 < u := by omega
      have hne0 : (u == 0) = false := beq_eq_false_iff_ne.mpr hu0
      rw [hne0] at hbU
      simpa [hposU] using hbU
  -- Prove `GoalsAt goal els toks t`:
  have hgoals : GoalsAt goal els toks t := by
    -- Walk `els = (blocks.flatMap ...) ++ elsEnd` by indexing:
    have hchEls : ChainEls 0 cs.size els := (blocks_chainEls hbc hval).append hchEnd
    have hposAll : ∀ x ∈ els, x.i < x.j := by
      intro x hx
      rcases List.mem_append.mp hx with hblk | hend
      · obtain ⟨b, hbM, hbx⟩ := List.mem_flatMap.mp hblk
        have hb := hval b hbM
        rcases List.mem_append.mp hbx with htr | hsing
        · exact (hb.2.1 x htr).1
        · rw [List.mem_singleton] at hsing; subst hsing; exact hb.2.2.2.2.1
      · exact (hvEnd x hend).1
    have hei0_iff : ∀ k el, els[k]? = some el → (k = 0 → el.i = 0) ∧ (0 < k → 0 < el.i) := by
      intro k el hgetK
      generalize hels0 : els = es0 at hchEls hgetK hposAll
      generalize ha0 : (0 : Nat) = a0 at hchEls
      generalize hb0 : cs.size = b0 at hchEls
      cases hchEls with
      | nil _ => simp at hgetK
      | @cons _ m0 _ e0 tl hi0 hj0 htl =>
        subst ha0
        cases k with
        | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hgetK
          exact ⟨fun _ => hgetK ▸ hi0, (fun h => nomatch h)⟩
        | succ k' =>
          simp only [List.getElem?_cons_succ] at hgetK
          have he0Lt : 0 < m0 := by
            have := hposAll e0 (List.mem_cons_self ..)
            omega
          have hm0Le : m0 ≤ el.i := by
            have hgen : ∀ {a b : Nat} {l : List Element}, ChainEls a b l →
                (∀ (y : Element), y ∈ l → y.i < y.j) → ∀ (idx : Nat) (y : Element), l[idx]? = some y → a ≤ y.i := by
              intro a b l hl hpy
              induction hl with
              | nil _ => intro _ _ h; simp at h
              | cons ey hiy hjy hly ihl =>
                intro idx y hg
                cases idx with
                | zero => simp only [List.getElem?_cons_zero, Option.some.injEq] at hg; subst hg; omega
                | succ idx' =>
                  simp only [List.getElem?_cons_succ] at hg
                  have h1 := hpy ey (List.mem_cons_self ..)
                  have h2 := ihl (fun z hz => hpy z (List.mem_cons_of_mem _ hz)) idx' y hg
                  omega
            exact hgen htl (fun y hy => hposAll y (List.mem_cons_of_mem _ hy)) k' el hgetK
          exact ⟨(fun h => nomatch h), fun _ => by omega⟩
    -- Relate any element `els[k]? = some el` to either a `ValidTrivEl` or `blocks[r].tokEl` with `r = ((els.take k).filter isToken).length`:
    have helsDecomp : ∀ k el, els[k]? = some el →
        (el.isToken = false ∧ ValidTrivEl cx cs first el) ∨
        (el.isToken = true ∧
          let r := ((els.take k).filter Element.isToken).length
          ∃ (hr : r < blocks.length), el = (blocks[r]'hr).tokEl) := by
      -- Generalize with prefix `pre` of `els`:
      have htrivStep : ∀ (pre tr rest : List Element) (idx : Nat) (el : Element),
          (∀ x ∈ tr, ValidTrivEl cx cs first x) →
          idx < tr.length →
          (pre ++ tr ++ rest)[pre.length + idx]? = some el →
          el.isToken = false ∧ ValidTrivEl cx cs first el := by
        intro pre tr rest idx el hvT hidx hg
        rw [List.append_assoc, List.getElem?_append_right (Nat.le_add_right _ _),
            Nat.add_sub_cancel_left, List.getElem?_append_left hidx,
            List.getElem?_eq_getElem hidx, Option.some.injEq] at hg
        subst hg
        have hvEl := hvT _ (List.getElem_mem hidx)
        exact ⟨hvEl.2.2.1, hvEl⟩
      have hgen : ∀ (pre : List Element) (rem : List TokBlock),
          (∀ b ∈ rem, ValidTokBlock cx cs first b) →
          ∀ idx el,
            (pre ++ ((rem.flatMap fun b => b.triv ++ [b.tokEl]) ++ elsEnd))[pre.length + idx]? = some el →
            (el.isToken = false ∧ ValidTrivEl cx cs first el) ∨
            (el.isToken = true ∧
              let r := (((pre ++ ((rem.flatMap fun b => b.triv ++ [b.tokEl]) ++ elsEnd)).take (pre.length + idx)).filter Element.isToken).length -
                (pre.filter Element.isToken).length
              ∃ (hr : r < rem.length), el = (rem[r]'hr).tokEl) := by
        intro pre rem
        induction rem generalizing pre with
        | nil =>
          intro _ idx el hg
          simp only [List.flatMap_nil, List.nil_append] at hg
          rw [List.getElem?_append_right (Nat.le_add_right _ _), Nat.add_sub_cancel_left] at hg
          have hvEl := hvEnd el (List.mem_of_getElem? hg)
          exact Or.inl ⟨hvEl.2.2.1, hvEl⟩
        | cons blk bs ih =>
          intro hvR idx el hg
          have hb := hvR blk (List.mem_cons_self ..)
          have hbs := fun b hbm => hvR b (List.mem_cons_of_mem _ hbm)
          let tail := (bs.flatMap fun b => b.triv ++ [b.tokEl]) ++ elsEnd
          have heqL : pre ++ ((blk :: bs).flatMap (fun b => b.triv ++ [b.tokEl]) ++ elsEnd) =
              pre ++ blk.triv ++ [blk.tokEl] ++ tail := by simp [tail, List.append_assoc]
          by_cases h1 : idx < blk.triv.length
          · rw [heqL] at hg
            have hg' : (pre ++ blk.triv ++ ([blk.tokEl] ++ tail))[pre.length + idx]? = some el := by
              simpa [List.append_assoc] using hg
            exact Or.inl (htrivStep pre blk.triv ([blk.tokEl] ++ tail) idx el hb.2.1 h1 hg')
          · by_cases h2 : idx = blk.triv.length
            · subst h2
              have hg' : ((pre ++ blk.triv) ++ blk.tokEl :: tail)[(pre ++ blk.triv).length]? = some el := by
                rw [List.length_append]; simpa [heqL, List.append_assoc] using hg
              rw [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self, List.getElem?_cons_zero,
                  Option.some.injEq] at hg'
              subst hg'
              refine Or.inr ⟨hb.2.2.2.2.2.2.1, ?_⟩
              have htkEq : ((pre ++ ((blk :: bs).flatMap (fun b => b.triv ++ [b.tokEl]) ++ elsEnd)).take
                  (pre.length + blk.triv.length)) = pre ++ blk.triv := by
                rw [heqL, List.append_assoc, ← List.length_append, List.take_left]
              have htrivFilt : blk.triv.filter Element.isToken = [] :=
                List.filter_eq_nil_iff.mpr fun x hx => by rw [(hb.2.1 x hx).2.2.1]; simp
              simp only [htkEq, List.filter_append, htrivFilt, List.append_nil, Nat.sub_self]
              exact ⟨by simp, rfl⟩
            · have hgt : blk.triv.length + 1 ≤ idx := by omega
              let pre' := pre ++ blk.triv ++ [blk.tokEl]
              let idx' := idx - (blk.triv.length + 1)
              have hsumEq : pre.length + idx = pre'.length + idx' := by
                simp [pre', idx', List.length_append]; omega
              have hfullEq : pre ++ ((blk :: bs).flatMap (fun b => b.triv ++ [b.tokEl]) ++ elsEnd) =
                  pre' ++ tail := by simp [pre', tail, List.append_assoc]
              rw [hfullEq, hsumEq] at hg ⊢
              rcases ih pre' hbs idx' el hg with hl | ⟨hisT, hr', helEq⟩
              · exact Or.inl hl
              · refine Or.inr ⟨hisT, ?_⟩
                have hpre'Filt : (pre'.filter Element.isToken).length = (pre.filter Element.isToken).length + 1 := by
                  have htrivFilt : blk.triv.filter Element.isToken = [] :=
                    List.filter_eq_nil_iff.mpr fun x hx => by rw [(hb.2.1 x hx).2.2.1]; simp
                  simp [pre', List.filter_append, htrivFilt, hb.2.2.2.2.2.2.1]
                have hge1 : (pre'.filter Element.isToken).length ≤
                    (((pre' ++ tail).take (pre'.length + idx')).filter Element.isToken).length := by
                  have htkP : (pre' ++ tail).take (pre'.length + idx') = pre' ++ tail.take idx' := by
                    rw [List.take_add, List.take_left, List.drop_left]
                  simp only [htkP, List.filter_append, List.length_append]
                  omega
                let tot := (((pre' ++ tail).take (pre'.length + idx')).filter Element.isToken).length
                have hrShift : tot - (pre.filter Element.isToken).length =
                    (tot - (pre'.filter Element.isToken).length) + 1 := by omega
                dsimp only [tot, tail] at hr' helEq hge1 hrShift ⊢
                change ∃ hr : (((pre' ++ (bs.flatMap (fun b => b.triv ++ [b.tokEl]) ++ elsEnd)).take (pre'.length + idx')).filter Element.isToken).length - (pre.filter Element.isToken).length < (blk :: bs).length, _
                refine ⟨by simp only [List.length_cons]; omega, ?_⟩
                simpa [hrShift] using helEq
      intro k el hgk
      simpa using hgen [] blocks hval k el (by simpa using hgk)
    intro k el hgk
    have ⟨hk0I, hkPosI⟩ := hei0_iff k el hgk
    have hfirstEq : (goal == .Script || goal == .Module) = first := rfl
    rw [hfirstEq]
    rcases helsDecomp k el hgk with ⟨hisTF, hvEl⟩ | ⟨hisTT, hr, helEq⟩
    · by_cases hk0F : (k == 0 && first) = true
      · simp only [hk0F, ↓reduceIte]
        simp only [Bool.and_eq_true, beq_iff_eq] at hk0F
        have hi0 := hk0I hk0F.1
        have hg := hvEl.2.2.2.1
        simp [hk0F.2, hi0] at hg; exact hg
      · simp only [hk0F, Bool.false_eq_true, ↓reduceIte, hisTF, Bool.not_false]
        have hfaF : (first && el.i == 0) = false := by
          cases hf : first with
          | false => rfl
          | true =>
            have hkNe0 : k ≠ 0 := fun hk0 => hk0F (by simp [hk0, hf])
            have hiPos := hkPosI (by omega)
            simp [show el.i ≠ 0 from by omega]
        have hg := hvEl.2.2.2.1
        rw [hfaF] at hg; exact hg
    · by_cases hk0F : (k == 0 && first) = true
      · simp only [hk0F, ↓reduceIte]
        simp only [Bool.and_eq_true, beq_iff_eq] at hk0F
        have hi0 := hk0I hk0F.1
        obtain ⟨hu, hgEq⟩ := hgoalBlk _ hr
        dsimp only [first] at hk0F
        rw [← helEq] at hgEq
        simp [hk0F.2, hi0] at hgEq; exact hgEq
      · simp only [hk0F, Bool.false_eq_true, ↓reduceIte, hisTT, Bool.not_true]
        have hfaF : (first && el.i == 0) = false := by
          cases hf : first with
          | false => rfl
          | true =>
            have hkNe0 : k ≠ 0 := fun hk0 => hk0F (by simp [hk0, hf])
            have hiPos := hkPosI (by omega)
            simp [show el.i ≠ 0 from by omega]
        obtain ⟨hu, hgEq⟩ := hgoalBlk _ hr
        rw [← helEq, hfaF] at hgEq
        simp only [Bool.false_eq_true, ↓reduceIte] at hgEq
        rw [htGoal _ hu, hgEq]
  exact ⟨els, toks, hinv, hemb, hlen, hgoals⟩

/-! ### Part 5B: Completeness translation (`(els, toks, t)` → `TokStreamInv` + `PlainDerives` + `SynDone`) -/

private theorem tree_goalAt_isSynLexGoal :
    ∀ (t : Tree) (idx : Nat) (g : NT), t.goalAt idx = some g → isSynLexGoal g = true
  | .leaf i j, idx, g, h => by
    unfold Tree.goalAt at h
    split at h
    · injection h with heq; subst heq; decide
    · cases h
  | .lex k lt, idx, g, h => by
    unfold Tree.goalAt at h
    split at h
    · simp only [Option.map_eq_some_iff] at h
      obtain ⟨m, _, rfl⟩ := h
      exact isSynLexGoal_lexicalGoalOf m
    · cases h
  | .node _ _ _ _ _ kids, idx, g, h => by
    unfold Tree.goalAt at h
    exact inKids_isSynLexGoal kids idx g h
where
  inKids_isSynLexGoal : ∀ (ks : List Tree) (idx : Nat) (g : NT),
      Tree.goalAt.inKids idx ks = some g → isSynLexGoal g = true
    | [], _, _, h => by cases h
    | d :: ds, idx, g, h => by
      dsimp only [Tree.goalAt.inKids] at h
      cases hd : d.goalAt idx with
      | some g' => rw [hd] at h; injection h with heq; subst heq; exact tree_goalAt_isSynLexGoal d idx g' hd
      | none => rw [hd] at h; exact inKids_isSynLexGoal ds idx g h

private theorem scans_to_chainEls {cx : Ctx} {P : CodePrims} {src : List Nat} {els : List Element}
    (hscans : Scans Ecma.Spec.gl cx P src els) :
    ChainEls 0 src.length els := by
  obtain ⟨hzip, hlast, _⟩ := hscans
  cases els with
  | nil =>
    simp only [List.getLast?_nil, Option.map_none, Option.getD_none] at hlast
    rw [← hlast]; exact .nil 0
  | cons e0 tl =>
    simp only [List.zipIdx_cons, List.all_cons, Bool.and_eq_true] at hzip
    obtain ⟨hi0, hzipTl⟩ := hzip
    simp only [beq_iff_eq, ↓reduceIte] at hi0
    have hgen : ∀ (pre : List Element) (cur : Element) (rem : List Element),
        ((cur :: rem).getLast?.map (·.j)).getD 0 = src.length →
        (rem.zipIdx (pre.length + 1)).all (fun (e, k) =>
          e.i == (if k == 0 then 0 else ((pre ++ cur :: rem)[k - 1]?.map (·.j)).getD 0)) = true →
        ChainEls cur.j src.length rem := by
      intro pre cur rem
      induction rem generalizing pre cur with
      | nil =>
        intro hl _
        simp only [List.getLast?_singleton, Option.map_some, Option.getD_some] at hl
        rw [← hl]; exact .nil _
      | cons e1 r1 ih =>
        intro hl hz
        simp only [List.zipIdx_cons, List.all_cons, Bool.and_eq_true] at hz
        obtain ⟨hz1, hz2⟩ := hz
        simp only [beq_iff_eq, Nat.succ_ne_zero, ↓reduceIte, Nat.add_sub_cancel] at hz1
        have hgetPre : (pre ++ cur :: e1 :: r1)[pre.length]? = some cur := by
          rw [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self, List.getElem?_cons_zero]
        rw [hgetPre, Option.map_some, Option.getD_some] at hz1
        have hl' : ((e1 :: r1).getLast?.map (·.j)).getD 0 = src.length := by
          simpa [List.getLast?_cons_cons] using hl
        have hassoc : (pre ++ [cur]) ++ e1 :: r1 = pre ++ cur :: e1 :: r1 := by simp
        refine .cons e1 hz1 rfl (ih (pre ++ [cur]) e1 hl' ?_)
        rw [List.length_append, List.length_singleton, hassoc]
        exact hz2
    exact .cons e0 hi0 rfl (hgen [] e0 tl hlast hzipTl)

private theorem chainEls_end_le {a b : Nat} {es : List Element}
    (hch : ChainEls a b es) (hpos : ∀ x ∈ es, x.i < x.j) :
    ∀ e ∈ es, e.j ≤ b := by
  induction hch with
  | nil _ => intro _ h; nomatch h
  | @cons _ m _ e0 rest _ hj0 hr ih =>
    intro e he
    have hmLeB := chainEls_le hr (fun x hx => hpos x (List.mem_cons_of_mem _ hx))
    rcases List.mem_cons.mp he with rfl | hmem
    · omega
    · exact ih (fun x hx => hpos x (List.mem_cons_of_mem _ hx)) e hmem

private theorem chainEls_trivia_of_stop {cx : Ctx} {cs : Array Nat} {first : Bool}
    {p k : Nat} {triv : List Element}
    (hch : ChainEls p k triv)
    (hv : ∀ e ∈ triv, ValidTrivEl cx cs first e)
    (hstop : ¬ ∃ m e', TriviaElem Ecma.Spec.gl cx Engine.Model.codePrims cs.toList first k m e') :
    Trivia Ecma.Spec.gl cx Engine.Model.codePrims cs.toList first p k
      (triv.any fun e => e.breaks cs.toList) := by
  induction hch with
  | nil _ => exact .stop hstop
  | @cons a m _ e0 rest hi0 hj0 hr ih =>
    have hv0 := hv e0 (List.mem_cons_self ..)
    have hte0 : TriviaElem Ecma.Spec.gl cx Engine.Model.codePrims cs.toList first a m e0 :=
      ⟨by rw [← hi0, ← hj0]; exact hv0.1,
       by rw [Array.length_toList, ← hj0]; exact hv0.2.1,
       hi0, hj0,
       by rw [hv0.2.2.1]; rfl,
       by rw [← hi0]; exact hv0.2.2.2.1,
       by rw [← hi0, ← hj0]; exact hv0.2.2.2.2.1,
       by rw [← hi0, ← hj0]; exact hv0.2.2.2.2.2.1⟩
    simp only [List.any_cons]
    exact .step e0 hte0 (ih (fun x hx => hv x (List.mem_cons_of_mem _ hx)) hstop)

private theorem build_tokStreamInv_of_scans (hok : parseTablesOk = true)
    {cx : Ctx} {cs : Array Nat} (hcp : ∀ c ∈ cs.toList, c ≤ 0x10FFFF)
    {goal : NT} {ps : List Param} {vs : List (Nat × Bool)}
    {els : List Element} {toks : List Token} {tRoot : Tree}
    (hscans : Scans Ecma.Spec.gl cx Engine.Model.codePrims cs.toList els)
    (hgoals : GoalsAt goal els toks tRoot)
    (hfilt : toks.filter (·.virt.isNone) = tokensOf cs.toList els)
    (hall : toks.all (fun k => k.virt.isNone || !k.lt) = true)
    (hvalid : ValidASI Ecma.Spec.gl cx Engine.Model.codePrims cs.toList (firstOf goal) goal ps vs)
    (hmatch : toksMatchASI els toks vs) :
    ∃ (hinv : TokStreamInv cx cs (firstOf goal) vs els toks),
      ∀ r (hr : r < hinv.blocks.length) (g : NT),
        tRoot.goalAt (realIdx r toks) = some g →
        ScanTok Ecma.Spec.gl cx Engine.Model.codePrims cs.toList (firstOf goal) g
          (hinv.blocks[r]'hr).p (hinv.blocks[r]'hr).tokEl.i (hinv.blocks[r]'hr).tokEl.j
          (hinv.blocks[r]'hr).lt (hinv.blocks[r]'hr).tokEl.tree := by
  let first := firstOf goal
  obtain ⟨hvsBnd, hvsUniq⟩ := validASI_props hok hcp hvalid
  have hchFull : ChainEls 0 cs.size els := by simpa using scans_to_chainEls hscans
  have hposAll : ∀ e ∈ els, e.i < e.j := fun e he => (hscans.2.2 e he).1
  have hjLeSz : ∀ e ∈ els, e.j ≤ cs.size := chainEls_end_le hchFull hposAll
  -- Walk `rem` from `cur` to `cs.size` with accumulator `(p, curTriv, pre)`:
  have hsplit : ∀ {cur : Nat} (rem : List Element) (p : Nat) (curTriv pre : List Element),
      ChainEls cur cs.size rem →
      ChainEls p cur curTriv →
      (∀ x ∈ curTriv, ValidTrivEl cx cs first x) →
      ChainEls 0 cur pre →
      els = pre ++ rem →
      ∃ (blocks : List TokBlock) (elsEnd : List Element) (endPos : Nat) (endLt : Bool),
        BlocksChain p endPos blocks ∧
        (∀ blk ∈ blocks, ValidTokBlock cx cs first blk) ∧
        ChainEls endPos cs.size elsEnd ∧
        (∀ x ∈ elsEnd, ValidTrivEl cx cs first x) ∧
        Trivia Ecma.Spec.gl cx Engine.Model.codePrims cs.toList first endPos cs.size endLt ∧
        curTriv ++ rem = (blocks.flatMap fun blk => blk.triv ++ [blk.tokEl]) ++ elsEnd ∧
        ∀ r (hr : r < blocks.length) (g : NT),
          tRoot.goalAt (realIdx ((pre.filter Element.isToken).length - (curTriv.filter Element.isToken).length + r) toks) = some g →
          ScanTok Ecma.Spec.gl cx Engine.Model.codePrims cs.toList first g
            (blocks[r]'hr).p (blocks[r]'hr).tokEl.i (blocks[r]'hr).tokEl.j
            (blocks[r]'hr).lt (blocks[r]'hr).tokEl.tree := by
    intro cur rem
    induction rem generalizing cur with
    | nil =>
      intro p curTriv pre hchR hchT hvT _ _
      cases hchR
      have hstopEnd : ¬ ∃ m e', TriviaElem Ecma.Spec.gl cx Engine.Model.codePrims cs.toList first cs.size m e' := by
        rintro ⟨m, _, hm1, hm2, _⟩; rw [Array.length_toList] at hm2; omega
      exact ⟨[], curTriv, p, curTriv.any (·.breaks cs.toList),
        .nil p, (fun _ h => nomatch h), hchT, hvT,
        chainEls_trivia_of_stop hchT hvT hstopEnd,
        by simp, fun _ hr => nomatch hr⟩
    | cons e rest ih =>
      intro p curTriv pre hchR hchT hvT hchPre helsEq
      cases hchR with
      | @cons _ m _ _ _ hei hej hchRest =>
        let k := pre.length
        have hgetK : els[k]? = some e := by
          rw [helsEq, List.getElem?_append_right (Nat.le_refl _), Nat.sub_self, List.getElem?_cons_zero]
        have htakeK : els.take k = pre := by
          rw [helsEq, List.take_left]
        have heMem : e ∈ els := List.mem_of_getElem? hgetK
        obtain ⟨heLt, heDer, heMax, heFol⟩ := hscans.2.2 e heMem
        have hejSz : e.j ≤ cs.size := hjLeSz e heMem
        have hgK := hgoals k e hgetK
        have hfirstEq : (goal == .Script || goal == .Module) = first := rfl
        rw [hfirstEq] at hgK
        -- Relating `k == 0 && first` and `first && e.i == 0`:
        have hk0_iff_ei0 : (k == 0 && first) = (first && e.i == 0) := by
          cases hf : first with
          | false => simp
          | true =>
            cases hpre : pre with
            | nil =>
              have hc0 : cur = 0 := by rw [hpre] at hchPre; cases hchPre; rfl
              simp [k, hpre, hei, hc0]
            | cons e0 ptl =>
              have hcPos : 0 < cur := by
                rw [hpre] at hchPre
                cases hchPre with
                | cons _ hi0 hj0 hr0 =>
                  have hlt0 := hposAll e0 (by rw [helsEq, hpre]; exact List.mem_cons_self ..)
                  have hle0 := chainEls_le hr0 (fun y hy => hposAll y (by
                    rw [helsEq, hpre]; exact List.mem_append_left _ (List.mem_cons_of_mem _ hy)))
                  omega
              simp [k, hpre, hei, show cur ≠ 0 from by omega]
        have hcurTrivFilt : (curTriv.filter Element.isToken).length = 0 := by
          rw [List.length_eq_zero_iff, List.filter_eq_nil_iff]
          intro x hx; rw [(hvT x hx).2.2.1]; simp
        cases hisT : e.isToken with
        | false =>
          have heGoalEq : e.goal = (if first && e.i == 0 then .InputElementHashbangOrRegExp else .InputElementDiv) := by
            rw [hk0_iff_ei0] at hgK
            by_cases hfa : (first && e.i == 0) = true
            · simp [hfa] at hgK ⊢; exact hgK
            · simp [hfa, hisT] at hgK ⊢; exact hgK
          have hgLex : isLexGoal e.goal = true := by rw [heGoalEq]; split <;> decide
          have hhasF : e.tree.has .NumericLiteral e.i e.j = false := by
            rcases unpackInputElement hok hgLex hejSz heDer with ⟨_, hhF, _⟩ | ⟨hisT', _⟩
            · exact hhF
            · have : e.isToken = true := hisT'
              rw [hisT] at this; cases this
          have hvE : ValidTrivEl cx cs first e :=
            ⟨heLt, hejSz, hisT, heGoalEq, heDer, heMax, hhasF⟩
          have hchT' : ChainEls p m (curTriv ++ [e]) := hchT.append (.cons e hei hej (.nil m))
          have hvT' : ∀ x ∈ curTriv ++ [e], ValidTrivEl cx cs first x := by
            intro x hx; rcases List.mem_append.mp hx with h1 | h2
            · exact hvT x h1
            · rw [List.mem_singleton] at h2; exact h2 ▸ hvE
          have hchPre' : ChainEls 0 m (pre ++ [e]) := hchPre.append (.cons e hei hej (.nil m))
          have helsEq' : els = (pre ++ [e]) ++ rest := by simp [helsEq]
          obtain ⟨bs, elsEnd, endPos, endLt, hbc, hvb, hcEnd, hvEnd, htrEnd, hflat, hscanB⟩ :=
            ih p (curTriv ++ [e]) (pre ++ [e]) hchRest hchT' hvT' hchPre' helsEq'
          refine ⟨bs, elsEnd, endPos, endLt, hbc, hvb, hcEnd, hvEnd, htrEnd,
            by simpa [List.append_assoc] using hflat, fun r hr g htg => ?_⟩
          have hfiltEq : ((pre ++ [e]).filter Element.isToken).length - ((curTriv ++ [e]).filter Element.isToken).length =
              (pre.filter Element.isToken).length - (curTriv.filter Element.isToken).length := by
            simp [List.filter_append, hisT]
          exact hscanB r hr g (by rwa [hfiltEq])
        | true =>
          -- `e` is a token! Determine `lg`:
          have ⟨lg, hlgSyn, heGoalEq, hlgGoalAt⟩ : ∃ lg, isSynLexGoal lg = true ∧
              e.goal = (if first && e.i == 0 then .InputElementHashbangOrRegExp else lg) ∧
              ((first && e.i == 0) = false →
                tRoot.goalAt (realIdx ((pre.filter Element.isToken).length) toks) = some lg) := by
            rw [hk0_iff_ei0] at hgK
            by_cases hfa : (first && e.i == 0) = true
            · simp only [hfa, ↓reduceIte] at hgK
              exact ⟨.InputElementDiv, by decide, by simp [hfa, hgK], fun hf => by rw [hfa] at hf; cases hf⟩
            · simp only [hfa, Bool.false_eq_true, ↓reduceIte, hisT, Bool.not_true, htakeK] at hgK
              exact ⟨e.goal, tree_goalAt_isSynLexGoal tRoot _ _ hgK, by simp [hfa], fun _ => hgK⟩
          have hgLex : isLexGoal e.goal = true := by
            rw [heGoalEq]; split
            · decide
            · exact isLexGoal_of_isSynLexGoal hlgSyn
          have hfb : (first && e.i == 0) = true → e.goal = .InputElementHashbangOrRegExp := fun hfa => by
            rw [heGoalEq, hfa]; simp
          have hstopEi := no_triviaElem_at_max_token hok hcp hgLex hfb heLt hejSz
            (show Element.isToken ⟨e.i, e.j, e.goal, e.tree⟩ = true from hisT) heDer heMax
          have htrP : Trivia Ecma.Spec.gl cx Engine.Model.codePrims cs.toList first p e.i
              (curTriv.any (·.breaks cs.toList)) :=
            hei ▸ chainEls_trivia_of_stop hchT hvT (hei ▸ hstopEi)
          let blk : TokBlock := ⟨curTriv, e, p, curTriv.any (·.breaks cs.toList)⟩
          have hscLg : ScanTok Ecma.Spec.gl cx Engine.Model.codePrims cs.toList first lg p e.i e.j
              blk.lt e.tree := by
            refine ⟨htrP, heLt, by rw [Array.length_toList]; exact hejSz, ?_⟩
            dsimp only
            rw [← heGoalEq]
            exact ⟨hisT, heDer, heMax, heFol⟩
          have hvalidBlk : ValidTokBlock cx cs first blk :=
            ⟨hei ▸ hchT, hvT, rfl, htrP, heLt, hejSz, hisT, lg, hlgSyn, heGoalEq, hscLg⟩
          have hchPre' : ChainEls 0 m (pre ++ [e]) := hchPre.append (.cons e hei hej (.nil m))
          have helsEq' : els = (pre ++ [e]) ++ rest := by simp [helsEq]
          obtain ⟨bs, elsEnd, endPos, endLt, hbc, hvb, hcEnd, hvEnd, htrEnd, hflat, hscanB⟩ :=
            ih m [] (pre ++ [e]) hchRest (.nil m) (fun _ h => nomatch h) hchPre' helsEq'
          simp only [List.nil_append] at hflat
          refine ⟨blk :: bs, elsEnd, endPos, endLt, .cons blk rfl (hej ▸ hbc),
            fun b hbm => by rcases List.mem_cons.mp hbm with rfl | hm; exact hvalidBlk; exact hvb b hm,
            hcEnd, hvEnd, htrEnd,
            by simp [blk, hflat],
            fun r hr g htg => ?_⟩
          rw [hcurTrivFilt, Nat.sub_zero] at htg
          cases r with
          | zero =>
            simp only [Nat.add_zero] at htg
            dsimp only [List.getElem_cons_zero, blk]
            by_cases hfa : (first && e.i == 0) = true
            · refine ⟨htrP, heLt, by rw [Array.length_toList]; exact hejSz, ?_⟩
              simp only [hfa, ↓reduceIte]
              have hgEqH : e.goal = .InputElementHashbangOrRegExp := hfb hfa
              rw [← hgEqH]
              exact ⟨hisT, heDer, heMax, heFol⟩
            · have hfaF : (first && e.i == 0) = false := Bool.eq_false_iff.mpr hfa
              have hgEqLg : lg = g := Option.some.inj ((hlgGoalAt hfaF).symm.trans htg)
              exact hgEqLg ▸ hscLg
          | succ r' =>
            have hr' : r' < bs.length := by simp at hr; exact hr
            have hpre'Filt : ((pre ++ [e]).filter Element.isToken).length =
                (pre.filter Element.isToken).length + 1 := by
              simp [List.filter_append, hisT]
            refine hscanB r' hr' g ?_
            simp only [List.filter_nil, List.length_nil, Nat.sub_zero, hpre'Filt]
            rw [show (pre.filter Element.isToken).length + 1 + r' = (pre.filter Element.isToken).length + (r' + 1) from by omega]
            exact htg
  obtain ⟨blocks, elsEnd, endPos, endLt, hbc, hvb, hcEnd, hvEnd, htrEnd, hflat, hscanB⟩ :=
    hsplit els 0 [] [] hchFull (.nil 0) (fun _ h => nomatch h) (.nil 0) rfl
  simp only [List.nil_append, List.filter_nil, List.length_nil, Nat.sub_zero, Nat.zero_add] at hflat hscanB
  exact ⟨{
    blocks := blocks
    elsEnd := elsEnd
    endPos := endPos
    endLt := endLt
    hchain := hbc
    hvalid := hvb
    hendChain := hcEnd
    hendValid := hvEnd
    hendTriv := htrEnd
    helsEq := hflat
    htoksFilt := hfilt
    htoksAll := hall
    hasi := hmatch
    hvsBound := hvsBnd
    hvsUniq := hvsUniq }, hscanB⟩

mutual
private def treeSynSize : Tree → Nat
  | .leaf _ _ => 1
  | .lex _ _ => 1
  | .node _ _ _ _ _ ks => 1 + treeListSynSize ks

private def treeListSynSize : List Tree → Nat
  | [] => 0
  | t :: ts => treeSynSize t + treeListSynSize ts
end

private theorem step_span_and_goalAt_out {cx : Ctx} {P : CodePrims} {toks : List Token}
    {neg : NT → List Param → Nat → Nat → Prop} :
    ∀ (sz : Nat),
      (∀ {n ps i j u}, treeSynSize u ≤ sz →
        Step (tokenAlphabet Ecma.Spec.gl cx P) neg toks Ecma.Spec.gl cx .syntactic n ps i j u →
        i ≤ j ∧ u.span = (i, j) ∧ ∀ idx, (idx < i ∨ j ≤ idx) → u.goalAt idx = none) ∧
      (∀ {s ps k is i j m ts}, treeListSynSize ts ≤ sz →
        Ecma.Grammar.Seq (tokenAlphabet Ecma.Spec.gl cx P) neg toks Ecma.Spec.gl cx .syntactic s ps k is i j m ts →
        i ≤ j ∧ ∀ idx, (idx < i ∨ j ≤ idx) → Tree.goalAt.inKids idx ts = none) := by
  intro sz
  induction sz using Nat.strongRecOn with
  | ind sz ih =>
    have htermLt : ∀ {s k x i h}, (tokenAlphabet Ecma.Spec.gl cx P).term s k x (slice toks i h) → i < h := by
      intro s k x i h ht
      dsimp only [tokenAlphabet] at ht
      cases x with
      | cp _ => cases ht
      | text _ _ =>
        cases hsc : slice toks i h with
        | nil => rw [hsc] at ht; cases ht
        | cons t0 rest =>
          by_cases hle : h ≤ i
          · unfold slice at hsc; rw [Nat.sub_eq_zero_of_le hle, List.take_zero] at hsc; cases hsc
          · omega
    have hst : ∀ {n ps i j u}, treeSynSize u ≤ sz →
        Step (tokenAlphabet Ecma.Spec.gl cx P) neg toks Ecma.Spec.gl cx .syntactic n ps i j u →
        i ≤ j ∧ u.span = (i, j) ∧ ∀ idx, (idx < i ∨ j ≤ idx) → u.goalAt idx = none := by
      intro n ps i j u hsz hs
      cases hs with
      | lex _ _ _ =>
        refine ⟨by omega, rfl, fun idx hout => ?_⟩
        unfold Tree.goalAt; simp [show i ≠ idx from by omega]
      | node s _ _ _ hseq =>
        rw [treeSynSize] at hsz
        obtain ⟨hle, hout⟩ := (ih _ (by omega)).2 (Nat.le_refl _) hseq
        exact ⟨hle, rfl, hout⟩
    refine ⟨hst, ?_⟩
    intro s ps k is
    induction is generalizing k with
    | nil => intro _ _ _ _ _ hs; cases hs; exact ⟨Nat.le_refl _, fun _ _ => rfl⟩
    | cons _ _ ihr =>
      intro i j m ts hsz hs
      cases hs with
      | absent hr | look _ hr | noLT _ hr | empty hr | onlyIf hr => exact ihr hsz hr
      | phrase hp _ => cases hp
      | @term _ _ _ _ _ _ _ h _ _ _ ht hr | @butNotT _ _ _ _ _ _ _ h _ _ _ ht _ hr =>
        rw [treeListSynSize, treeSynSize] at hsz
        have hlt := htermLt ht
        obtain ⟨hle, houtR⟩ := ihr (by omega) hr
        refine ⟨by omega, fun idx hout => ?_⟩
        dsimp only [Tree.goalAt.inKids]
        have hleafNone : (Tree.leaf i h).goalAt idx = none := by
          unfold Tree.goalAt
          rcases hout with h1 | h2
          · simp [show ¬ (i ≤ idx) from by omega]
          · simp [show ¬ (idx < h) from by omega]
        rw [hleafNone]
        exact houtR idx (by omega)
      | nt hs0 _ hr | butNotN hs0 _ hr =>
        have hpos_step : ∀ {n0 ps0 a0 b0 u0},
            Step (tokenAlphabet Ecma.Spec.gl cx P) neg toks Ecma.Spec.gl cx .syntactic n0 ps0 a0 b0 u0 →
            0 < treeSynSize u0 := by
          intro _ _ _ _ _ hs; cases hs <;> (rw [treeSynSize]; omega)
        rw [treeListSynSize] at hsz
        have hpos0 := hpos_step hs0
        obtain ⟨hle1, _, hout1⟩ := hst (by omega) hs0
        obtain ⟨hle2, hout2⟩ := ihr (by omega) hr
        refine ⟨by omega, fun idx hout => ?_⟩
        dsimp only [Tree.goalAt.inKids]
        rw [hout1 idx (by omega)]
        exact hout2 idx (by omega)

private theorem complete_translate (hok : parseTablesOk = true)
    {cx : Ctx} {cs : Array Nat} (hcp : ∀ c ∈ cs.toList, c ≤ 0x10FFFF)
    {goal : NT} (hhasSyn : (Ecma.Spec.gl.rulesOf .syntactic).any (·.lhs == goal) = true)
    {ps : List Param} {vs : List (Nat × Bool)} {stamp : Nat}
    {els : List Element} {toks : List Token} {t : Tree}
    (hscans : Scans Ecma.Spec.gl cx Engine.Model.codePrims cs.toList els)
    (hgoals : GoalsAt goal els toks t)
    (hfilt : toks.filter (·.virt.isNone) = tokensOf cs.toList els)
    (hall : toks.all (fun k => k.virt.isNone || !k.lt) = true)
    (hvalid : ValidASI Ecma.Spec.gl cx Engine.Model.codePrims cs.toList (firstOf goal) goal ps vs)
    (hmatch : toksMatchASI els toks vs)
    (hsent : Sentence Ecma.Spec.gl cx Engine.Model.codePrims goal ps toks t)
    (hfhe : ForHeadersExplicit toks t) :
    ∃ (hinv : TokStreamInv cx cs (firstOf goal) vs els toks) (dt : DTree),
      (synAlphaSpec hok hcp (firstOf goal) cx stamp vs hinv.hvsBound).PlainDerives
        goal ps 0 (tokBnd els toks toks.length) dt ∧
      SameDTreeSkeleton dt 0 t ∧
      DTreeBndsMatch (tokBnd els toks) dt 0 toks.length ∧
      SynDone Ecma.Spec.gl cx Engine.Model.codePrims cs.toList (firstOf goal) vs goal ps := by
  let first := firstOf goal
  obtain ⟨hinv, hscanGoal⟩ := build_tokStreamInv_of_scans hok hcp hscans hgoals hfilt hall hvalid hmatch
  let S := synAlphaSpec hok hcp first cx stamp vs hinv.hvsBound
  obtain ⟨K, hK⟩ := hsent
  have hstepRoot := hK (max K 2) (Nat.le_max_left K 2)
  let k0 := max K 2 - 2
  have hk0Eq : max K 2 = k0 + 2 := by omega
  rw [hk0Eq] at hstepRoot
  dsimp only [DerivesAt] at hstepRoot
  let neg0 := fun m ps' a b => ∃ t', DerivesAt Ecma.Spec.gl cx .syntactic
    (tokenAlphabet Ecma.Spec.gl cx Engine.Model.codePrims) toks (k0 + 1) m ps' a b t'
  have htermLt : ∀ {s k x i h}, h ≤ toks.length →
      (tokenAlphabet Ecma.Spec.gl cx Engine.Model.codePrims).term s k x (slice toks i h) →
      i < toks.length ∧ h = i + 1 := by
    intro s k x i h hhLe ht
    dsimp only [tokenAlphabet] at ht
    cases x with
    | cp _ => cases ht
    | text _ _ =>
      cases hsc : slice toks i h with
      | nil => rw [hsc] at ht; cases ht
      | cons t0 rest =>
        cases rest with
        | cons _ _ => rw [hsc] at ht; cases ht
        | nil =>
          have hlen : (slice toks i h).length = 1 := by rw [hsc]; rfl
          have hlt : i < h := by
            by_cases hle : h ≤ i
            · unfold slice at hlen; rw [Nat.sub_eq_zero_of_le hle, List.take_zero] at hlen; cases hlen
            · omega
          unfold slice at hlen; rw [List.length_take, List.length_drop, Nat.min_eq_left (by omega)] at hlen
          exact ⟨by omega, by omega⟩
  have hterm1 : ∀ {s k x i h} (hhLe : h ≤ toks.length)
      (ht : (tokenAlphabet Ecma.Spec.gl cx Engine.Model.codePrims).term s k x (slice toks i h)),
      h = i + 1 ∧ i < toks.length ∧ (tokenAlphabet Ecma.Spec.gl cx Engine.Model.codePrims).term s k x [toks[i]'(htermLt hhLe ht).1] := by
    intro s k x i h hhLe ht
    obtain ⟨hiLt, hhEq⟩ := htermLt hhLe ht
    refine ⟨hhEq, hiLt, ?_⟩
    subst hhEq
    have hsc1 : slice toks i (i + 1) = [toks[i]] := by
      unfold slice
      rw [Nat.add_sub_cancel_left, List.drop_eq_getElem_cons hiLt, List.take_succ_cons, List.take_zero]
    rwa [hsc1] at ht
  -- Translate any syntactic `Step` `u` (not `.lex`, i.e. `gl.alts cx .syntactic n ≠ []`):
  have htrans : ∀ (sz : Nat) {n0 : NT} {ps0 : List Param} {i0 j0 : Nat} {u : Tree},
      treeSynSize u ≤ sz →
      j0 ≤ toks.length →
      Ecma.Spec.gl.alts cx .syntactic n0 ≠ [] →
      Step (tokenAlphabet Ecma.Spec.gl cx Engine.Model.codePrims) neg0 toks Ecma.Spec.gl cx .syntactic n0 ps0 i0 j0 u →
      ForHeadersExplicit toks u →
      (∀ idx g, i0 ≤ idx → idx < j0 → u.goalAt idx = some g → t.goalAt idx = some g) →
      ∃ dt,
        S.PlainDerives n0 ps0 (tokBnd els toks i0) (tokBnd els toks j0) dt ∧
        SameDTreeSkeleton dt i0 u ∧
        DTreeBndsMatch (tokBnd els toks) dt i0 j0 := by
    intro sz
    induction sz using Nat.strongRecOn with
    | ind sz ihOuter =>
      intro n0 ps0 i0 j0 u hsz hj0Le hneAlts hst hfheU hgoalU
      cases hst with
      | lex hnil _ _ => exact absurd hnil hneAlts
      | @node _ _ _ _ mMask kids pId s hsSpec hgrd hpidSpec hseq0 =>
        have hsMem : s ∈ altsOf cx .syntactic n0 := (altsOf_eq hok cx .syntactic n0).symm ▸ hsSpec
        obtain ⟨hlhsS, hoptsS⟩ := alt_lhs_and_opts hok hsSpec
        rw [treeSynSize] at hsz
        unfold ForHeadersExplicit at hfheU
        obtain ⟨hforU, hfheKids⟩ := hfheU
        -- Inner induction over `is : List Item` (`s.alt.rhs.drop k = is`):
        have hseqT : ∀ (is : List Item) (k a0 : Nat) (m0 : List Bool) (ts0 : List Tree),
            treeListSynSize ts0 ≤ treeListSynSize kids →
            k ≤ s.alt.rhs.length →
            s.alt.rhs.drop k = is →
            Ecma.Grammar.Seq (tokenAlphabet Ecma.Spec.gl cx Engine.Model.codePrims) neg0 toks
              Ecma.Spec.gl cx .syntactic s ps0 k is a0 j0 m0 ts0 →
            ForHeadersExplicit.all toks ts0 →
            (∀ d ∈ ts0, d ∈ kids) →
            (∀ idx g, a0 ≤ idx → idx < j0 → Tree.goalAt.inKids idx ts0 = some g → t.goalAt idx = some g) →
            ∃ dks,
              S.SeqWith (fun _ _ _ _ => True) s ps0 k is (tokBnd els toks a0) (tokBnd els toks j0) m0 dks ∧
              SameDTreeSkeletonList dks a0 j0 ts0 ∧
              DTreeBndsMatchList (tokBnd els toks) dks a0 j0 := by
          intro is
          induction is with
          | nil =>
            intro k a0 m0 ts0 _ _ _ hsq _ _ _
            cases hsq
            exact ⟨[], .nil, .nil _, rfl⟩
          | cons it rest ihIs =>
            intro k a0 m0 ts0 hszTs hk0 hdr0 hsq hfheTs hsubK hgoalTs
            have hallOk : ∀ x ∈ it :: rest, synItemOk cx x = true := fun x hx =>
              synItemOk_of_mem hok hsSpec (List.mem_of_mem_drop (hdr0 ▸ hx))
            have hkLt : k < s.alt.rhs.length := by
              have hlen : 0 < (s.alt.rhs.drop k).length := by rw [hdr0]; simp
              rw [List.length_drop] at hlen; omega
            have hdrRest : s.alt.rhs.drop (k + 1) = rest := by
              rw [← List.tail_drop, hdr0]; rfl
            have hrhsK : s.alt.rhs[k]? = some it := by
              have h1 : (s.alt.rhs.drop k).head? = some it := by rw [hdr0]; rfl
              rw [List.head?_drop] at h1; exact h1
            have ha0LeJ0 : a0 ≤ j0 :=
              ((step_span_and_goalAt_out (treeListSynSize ts0)).2 (Nat.le_refl _) hsq).1
            have ha0LeLen : a0 ≤ toks.length := Nat.le_trans ha0LeJ0 hj0Le
            cases hsq with
            | absent hr =>
              obtain ⟨dks, hsw, hsk, hbnd⟩ :=
                ihIs (k + 1) a0 _ ts0 hszTs (Nat.succ_le_of_lt hkLt) hdrRest hr hfheTs hsubK hgoalTs
              exact ⟨dks, .absent hsw, hsk, hbnd⟩
            | empty hr =>
              obtain ⟨dks, hsw, hsk, hbnd⟩ :=
                ihIs (k + 1) a0 m0 ts0 hszTs (Nat.succ_le_of_lt hkLt) hdrRest hr hfheTs hsubK hgoalTs
              exact ⟨dks, .empty hsw, hsk, hbnd⟩
            | onlyIf hr =>
              obtain ⟨dks, hsw, hsk, hbnd⟩ :=
                ihIs (k + 1) a0 m0 ts0 hszTs (Nat.succ_le_of_lt hkLt) hdrRest hr hfheTs hsubK hgoalTs
              exact ⟨dks, .onlyIf hsw, hsk, hbnd⟩
            | noLT hnl hr =>
              obtain ⟨dks, hsw, hsk, hbnd⟩ :=
                ihIs (k + 1) a0 m0 ts0 hszTs (Nat.succ_le_of_lt hkLt) hdrRest hr hfheTs hsubK hgoalTs
              exact ⟨dks, .noLT ((hinv.noLT_iff_synNoLT hok hcp ha0LeLen).mp hnl) hsw, hsk, hbnd⟩
            | @look _ _ _ l _ _ _ _ _ hlk hr =>
              obtain ⟨dks, hsw, hsk, hbnd⟩ :=
                ihIs (k + 1) a0 m0 ts0 hszTs (Nat.succ_le_of_lt hkLt) hdrRest hr hfheTs hsubK hgoalTs
              have hhitOk := hallOk _ (List.mem_cons_self ..)
              have hsynLk : SynLookOk Ecma.Spec.gl cx Engine.Model.codePrims cs.toList first vs l (tokBnd els toks a0) := by
                dsimp only [synItemOk] at hhitOk
                cases l with
                | eq q =>
                  exact (hinv.startsWith_iff_synStarts hok hcp s q (by simpa [lookSeqsOk] using hhitOk) ha0LeLen).mp hlk
                | ne q =>
                  exact fun hsy => hlk ((hinv.startsWith_iff_synStarts hok hcp s q (by simpa [lookSeqsOk] using hhitOk) ha0LeLen).mpr hsy)
                | mem qs =>
                  obtain ⟨q, hq, hswQ⟩ := hlk
                  have hqOk : lookSeqsOk synLookTermOk [q] = true := by
                    simp only [lookSeqsOk, List.all_cons, List.all_nil, Bool.and_true]
                    exact List.all_eq_true.mp hhitOk q hq
                  exact ⟨q, hq, (hinv.startsWith_iff_synStarts hok hcp s q hqOk ha0LeLen).mp hswQ⟩
                | notMem qs =>
                  intro q hq hsy
                  have hqOk : lookSeqsOk synLookTermOk [q] = true := by
                    simp only [lookSeqsOk, List.all_cons, List.all_nil, Bool.and_true]
                    exact List.all_eq_true.mp hhitOk q hq
                  exact hlk q hq ((hinv.startsWith_iff_synStarts hok hcp s q hqOk ha0LeLen).mpr hsy)
                | notMemNT _ => cases hhitOk
              exact ⟨dks, .look ((synLook_iff hok hcp hinv.hvsBound hhitOk _).mpr hsynLk) hsw, hsk, hbnd⟩
            | phrase hp _ => cases hp
            | @term _ _ _ x o _ _ h0 _ mr tsr ht hr =>
              have hh0LeJ0 : h0 ≤ j0 :=
                ((step_span_and_goalAt_out (treeListSynSize tsr)).2 (Nat.le_refl _) hr).1
              obtain ⟨hhEq, ha0LtLen, ht1⟩ := hterm1 (Nat.le_trans hh0LeJ0 hj0Le) ht
              subst hhEq
              have ha0p1LeJ0 : a0 + 1 ≤ j0 := hh0LeJ0
              have hszR : treeListSynSize tsr ≤ treeListSynSize kids := by
                rw [treeListSynSize, treeSynSize] at hszTs; omega
              have hgoalR : ∀ idx g, a0 + 1 ≤ idx → idx < j0 → Tree.goalAt.inKids idx tsr = some g → t.goalAt idx = some g := by
                intro idx g hlo hhi hgR
                refine hgoalTs idx g (by omega) hhi ?_
                dsimp only [Tree.goalAt.inKids]
                rw [(leaf_goalAt_one a0).2 idx (Or.inr hlo)]
                exact hgR
              obtain ⟨dksr, hswr, hskr, hbndr⟩ :=
                ihIs (k + 1) (a0 + 1) mr tsr hszR (Nat.succ_le_of_lt hkLt) hdrRest hr hfheTs.2
                  (fun d hd => hsubK d (List.mem_cons_of_mem _ hd)) hgoalR
              -- Build `SynTermFast`:
              have hsynTF : SynTermFast cx cs first vs s k x (tokBnd els toks a0) (tokBnd els toks (a0 + 1)) := by
                refine (synTermFast_iff_synTerm hok hsSpec hkLt x _ _).mpr ?_
                cases x with
                | cp _ => cases ht1
                | text str b_ =>
                  have hgetA : toks[a0]? = some toks[a0] := List.getElem?_eq_getElem ha0LtLen
                  cases hv : toks[a0].virt with
                  | some why =>
                    obtain ⟨hbnd0, hpend, hbnd1, hwhyEq, _⟩ := hinv.tokBnd_virt hgetA hv
                    dsimp only [tokenAlphabet] at ht1
                    rw [hv] at ht1
                    obtain ⟨_, c, hctor, cls, hsem, hclsOk⟩ := ht1
                    obtain ⟨bS, oS, hrhsSemi⟩ := synSrc_semis_imp hok hsSpec hkLt hctor hsem
                    rw [hrhsK] at hrhsSemi
                    injection hrhsSemi with hItEq; injection hItEq with hSymEq _; injection hSymEq with hTermEq
                    injection hTermEq with hStrEq _
                    subst hStrEq
                    unfold SynTerm
                    rw [hpend]; simp only [↓reduceIte]
                    refine ⟨trivial, ⟨c, cls, hctor, hsem, ?_⟩, hbnd1.trans (congrArg (· + 1) hbnd0.symm)⟩
                    rw [(hbnd0 ▸ rfl : (tokBnd els toks a0) / 2 = (2 * tokPos els toks a0) / 2),
                        show (2 * tokPos els toks a0) / 2 = tokPos els toks a0 from by omega]
                    cases cls with
                    | doWhile => trivial
                    | emptyStatement | forHeader => exact hclsOk
                    | insertable | forHeaderIfDeclaration =>
                      cases hparen : vsParen vs (tokPos els toks a0) with
                      | false => rfl
                      | true => simp [hparen] at hwhyEq; rw [hwhyEq] at hclsOk; cases hclsOk
                  | none =>
                    obtain ⟨hrIdx, hdiv2, hnp, htokEq, hnc, hbndNext, hriEq⟩ := hinv.tokBnd_real hgetA hv
                    have htGoalDiv : t.goalAt a0 = some .InputElementDiv := by
                      refine hgoalTs a0 .InputElementDiv (Nat.le_refl _) (by omega) ?_
                      dsimp only [Tree.goalAt.inKids]
                      have hg0 : (Tree.leaf a0 (a0 + 1)).goalAt a0 = some .InputElementDiv := by
                        simpa using (leaf_goalAt_one a0).1 0 (by omega)
                      rw [hg0]
                    have hscDiv := hscanGoal _ hrIdx .InputElementDiv (hriEq.symm ▸ htGoalDiv)
                    dsimp only [tokenAlphabet] at ht1
                    rw [htokEq] at ht1
                    unfold SynTerm
                    rw [hnp]; simp only [Bool.false_eq_true, ↓reduceIte, hdiv2]
                    exact ⟨_, _, _, _, hscDiv, hnc, ht1.1, hbndNext⟩
              exact ⟨.leaf (tokBnd els toks a0) (tokBnd els toks (a0 + 1)) :: dksr,
                .term hsynTF hswr,
                .cons rfl (.leaf a0) hskr,
                ⟨a0 + 1, by omega, ha0p1LeJ0, ⟨rfl, rfl, rfl⟩, hbndr⟩⟩
            | @butNotT _ _ _ x ex _ _ h0 _ _ tsr ht hexT hr =>
              have hh0LeJ0 : h0 ≤ j0 :=
                ((step_span_and_goalAt_out (treeListSynSize tsr)).2 (Nat.le_refl _) hr).1
              obtain ⟨hhEq, ha0LtLen, ht1⟩ := hterm1 (Nat.le_trans hh0LeJ0 hj0Le) ht
              subst hhEq
              have ha0p1LeJ0 : a0 + 1 ≤ j0 := hh0LeJ0
              have hszR : treeListSynSize tsr ≤ treeListSynSize kids := by
                rw [treeListSynSize, treeSynSize] at hszTs; omega
              have hgoalR : ∀ idx g, a0 + 1 ≤ idx → idx < j0 → Tree.goalAt.inKids idx tsr = some g → t.goalAt idx = some g := by
                intro idx g hlo hhi hgR
                refine hgoalTs idx g (by omega) hhi ?_
                dsimp only [Tree.goalAt.inKids]
                rw [(leaf_goalAt_one a0).2 idx (Or.inr hlo)]
                exact hgR
              obtain ⟨dksr, hswr, hskr, hbndr⟩ :=
                ihIs (k + 1) (a0 + 1) m0 tsr hszR (Nat.succ_le_of_lt hkLt) hdrRest hr hfheTs.2
                  (fun d hd => hsubK d (List.mem_cons_of_mem _ hd)) hgoalR
              have hgetA : toks[a0]? = some toks[a0] := List.getElem?_eq_getElem ha0LtLen
              have hvNone : toks[a0].virt = none := by
                cases hv : toks[a0].virt with
                | none => rfl
                | some why =>
                  cases x with
                  | cp _ => cases ht1
                  | text _ _ =>
                    dsimp only [tokenAlphabet] at ht1
                    rw [hv] at ht1
                    obtain ⟨_, c, hctor, cls, hsem, _⟩ := ht1
                    obtain ⟨_, _, hrhsSemi⟩ := synSrc_semis_imp hok hsSpec hkLt hctor hsem
                    rw [hrhsK] at hrhsSemi; cases hrhsSemi
              obtain ⟨hrIdx, hdiv2, hnp, htokEq, hnc, hbndNext, hriEq⟩ := hinv.tokBnd_real hgetA hvNone
              have htGoalDiv : t.goalAt a0 = some .InputElementDiv := by
                refine hgoalTs a0 .InputElementDiv (Nat.le_refl _) (by omega) ?_
                dsimp only [Tree.goalAt.inKids]
                have hg0 : (Tree.leaf a0 (a0 + 1)).goalAt a0 = some .InputElementDiv := by
                  simpa using (leaf_goalAt_one a0).1 0 (by omega)
                rw [hg0]
              have hscDiv := hscanGoal _ hrIdx .InputElementDiv (hriEq.symm ▸ htGoalDiv)
              have hsynTF : SynTermFast cx cs first vs s k x (tokBnd els toks a0) (tokBnd els toks (a0 + 1)) := by
                refine (synTermFast_iff_synTerm hok hsSpec hkLt x _ _).mpr ?_
                cases x with
                | cp _ => cases ht1
                | text str b_ =>
                  dsimp only [tokenAlphabet] at ht1
                  rw [htokEq] at ht1
                  unfold SynTerm
                  rw [hnp]; simp only [Bool.false_eq_true, ↓reduceIte, hdiv2]
                  exact ⟨_, _, _, _, hscDiv, hnc, ht1.1, hbndNext⟩
              have hitOk := hallOk _ (List.mem_cons_self ..)
              have hnoEx : ¬ S.ExclHolds s k ps0 (tokBnd els toks a0) (tokBnd els toks (a0 + 1)) ex := by
                intro hexH
                have hsynEx := (synExcl_iff hok hcp hinv.hvsBound hsSpec hkLt hitOk ps0 _ _).mp hexH
                exact hexT ((excl_token_iff_synExcluded hok hcp hinv hsSpec hkLt hrhsK ha0LtLen hvNone
                  ⟨_, _, _, _, hdiv2.symm ▸ hscDiv, hbndNext, htokEq⟩ k0 ps0).mpr hsynEx)
              exact ⟨.leaf (tokBnd els toks a0) (tokBnd els toks (a0 + 1)) :: dksr,
                .butNotT hsynTF hnoEx hswr,
                .cons rfl (.leaf a0) hskr,
                ⟨a0 + 1, by omega, ha0p1LeJ0, ⟨rfl, rfl, rfl⟩, hbndr⟩⟩
            | @butNotN _ _ _ m args ex _ _ h0 _ _ t0 tsr hstM hexT hr =>
              have hitOk := hallOk _ (List.mem_cons_self ..)
              have hnilM : Ecma.Spec.gl.alts cx .syntactic m = [] := by
                dsimp only [synItemOk] at hitOk
                exact List.isEmpty_iff.mp (glData_eq ▸ (Bool.and_eq_true_iff.mp hitOk).1)
              have hdivBase : lexicalGoalOf m = .InputElementDiv := by
                have hd := synSrc_butNot_divOk hsSpec (List.mem_of_getElem? hrhsK)
                dsimp only [itemButNotDivOk] at hd
                exact beq_iff_eq.mp (Bool.and_eq_true_iff.mp hd).1
              cases hstM with
              | node _ hsM _ _ _ => rw [hnilM] at hsM; cases hsM
              | @lex _ _ _ tLex tokM _ hgetA hleafM =>
                have ha0LtLen : a0 < toks.length := (List.getElem?_eq_some_iff.mp hgetA).1
                have ha0p1LeJ0 : a0 + 1 ≤ j0 :=
                  ((step_span_and_goalAt_out (treeListSynSize tsr)).2 (Nat.le_refl _) hr).1
                have hszR : treeListSynSize tsr ≤ treeListSynSize kids := by
                  rw [treeListSynSize, treeSynSize] at hszTs; omega
                have hntLex : tLex.nt? = some m := derives_code_nt? hleafM.2
                have hgoalR : ∀ idx g, a0 + 1 ≤ idx → idx < j0 → Tree.goalAt.inKids idx tsr = some g → t.goalAt idx = some g := by
                  intro idx g hlo hhi hgR
                  refine hgoalTs idx g (by omega) hhi ?_
                  dsimp only [Tree.goalAt.inKids]
                  rw [(lex_goalAt_one a0 hntLex).2 idx (Or.inr hlo)]
                  exact hgR
                obtain ⟨dksr, hswr, hskr, hbndr⟩ :=
                  ihIs (k + 1) (a0 + 1) m0 tsr hszR (Nat.succ_le_of_lt hkLt) hdrRest hr hfheTs.2
                    (fun d hd => hsubK d (List.mem_cons_of_mem _ hd)) hgoalR
                obtain ⟨hrIdx, hdiv2, hnp, htokEq, hnc, hbndNext, hriEq⟩ := hinv.tokBnd_real hgetA hleafM.1
                have htGoalDiv : t.goalAt a0 = some .InputElementDiv := by
                  refine hgoalTs a0 .InputElementDiv (Nat.le_refl _) (by omega) ?_
                  dsimp only [Tree.goalAt.inKids]
                  have hg1 := (lex_goalAt_one a0 hntLex).1 0 (by omega)
                  rw [Nat.add_zero, hdivBase] at hg1
                  rw [hg1]
                have hscDiv := hscanGoal _ hrIdx .InputElementDiv (hriEq.symm ▸ htGoalDiv)
                let blk := hinv.blocks[(toks.take a0).countP (·.virt.isNone)]'hrIdx
                have hbV := hinv.hvalid blk (List.getElem_mem hrIdx)
                have hlenSl : (slice cs.toList blk.tokEl.i blk.tokEl.j).length = blk.tokEl.j - blk.tokEl.i := by
                  unfold slice; rw [List.length_take, List.length_drop, Array.length_toList]
                  have := hbV.2.2.2.2.1; have := hbV.2.2.2.2.2.1; omega
                have hderLexM := hleafM.2
                rw [htokEq] at hderLexM; dsimp only at hderLexM; rw [hlenSl] at hderLexM
                have hsynLf : SynLeaf Ecma.Spec.gl cx Engine.Model.codePrims cs.toList first vs m
                    (tokBnd els toks a0) (tokBnd els toks (a0 + 1)) :=
                  ⟨hnp, blk.tokEl.i, blk.tokEl.j, blk.lt, blk.tokEl.tree, tLex,
                   hdiv2.symm ▸ (hdivBase.symm ▸ hscDiv), hdiv2.symm ▸ hnc, hderLexM, hbndNext⟩
                have hemM : (altsOf cx .syntactic m).isEmpty = true := by rw [altsOf_eq hok, hnilM]; rfl
                have hfk : forKeep s.rule.lhs m (tokBnd els toks (a0 + 1)) = true :=
                  hbndNext ▸ forKeep_two_mul _ _ _
                have htokEqIdx : toks[a0] = ⟨slice cs.toList blk.tokEl.i blk.tokEl.j, blk.lt, none⟩ :=
                  Option.some.inj ((List.getElem?_eq_getElem ha0LtLen).symm.trans hgetA) ▸ htokEq
                have hvNoneIdx : toks[a0].virt = none := by rw [htokEqIdx]
                have hnoEx : ¬ S.ExclHolds s k ps0 (tokBnd els toks a0) (tokBnd els toks (a0 + 1)) ex := by
                  intro hexH
                  have hsynEx := (synExcl_iff hok hcp hinv.hvsBound hsSpec hkLt hitOk ps0 _ _).mp hexH
                  exact hexT ((excl_token_iff_synExcluded hok hcp hinv hsSpec hkLt hrhsK ha0LtLen hvNoneIdx
                    ⟨_, _, _, _, hdiv2.symm ▸ hscDiv, hbndNext, htokEqIdx⟩ k0 ps0).mpr hsynEx)
                exact ⟨.lex m (tokBnd els toks a0) (tokBnd els toks (a0 + 1)) :: dksr,
                  .butNotLeaf hemM hsynLf hfk hnoEx hswr,
                  .cons rfl (.lex a0 hntLex) hskr,
                  ⟨a0 + 1, by omega, ha0p1LeJ0, ⟨rfl, rfl, rfl⟩, hbndr⟩⟩
            | @nt _ _ _ m args o _ _ h0 _ mr t0 tsr hstM _ hr =>
              have ⟨ha0LeH0, hspT0, houtT0⟩ :=
                (step_span_and_goalAt_out (treeSynSize t0)).1 (Nat.le_refl _) hstM
              have hh0LeJ0 : h0 ≤ j0 :=
                ((step_span_and_goalAt_out (treeListSynSize tsr)).2 (Nat.le_refl _) hr).1
              have hposT0 : 0 < treeSynSize t0 := by cases hstM <;> (rw [treeSynSize]; omega)
              have hszR : treeListSynSize tsr ≤ treeListSynSize kids := by
                rw [treeListSynSize] at hszTs; omega
              have hgoalR : ∀ idx g, h0 ≤ idx → idx < j0 → Tree.goalAt.inKids idx tsr = some g → t.goalAt idx = some g := by
                intro idx g hlo hhi hgR
                refine hgoalTs idx g (by omega) hhi ?_
                dsimp only [Tree.goalAt.inKids]
                rw [houtT0 idx (Or.inr hlo)]
                exact hgR
              obtain ⟨dksr, hswr, hskr, hbndr⟩ :=
                ihIs (k + 1) h0 mr tsr hszR (Nat.succ_le_of_lt hkLt) hdrRest hr hfheTs.2
                  (fun d hd => hsubK d (List.mem_cons_of_mem _ hd)) hgoalR
              have ⟨_, hca⟩ := noCondAfter_of_synItems (fun x hx => hallOk x (List.mem_cons_of_mem _ hx))
              have hchCond : S.CondHolds rest (tokBnd els toks a0) (tokBnd els toks h0) := by
                unfold AlphaSpec.CondHolds; rw [hca]; trivial
              cases hemM : (altsOf cx .syntactic m).isEmpty with
              | true =>
                have hnilM : Ecma.Spec.gl.alts cx .syntactic m = [] :=
                  List.isEmpty_iff.mp ((altsOf_eq hok cx .syntactic m) ▸ hemM)
                cases hstM with
                | node _ hsM _ _ _ => rw [hnilM] at hsM; cases hsM
                | @lex _ _ _ tLex tokM _ hgetA hleafM =>
                  have hntLex : tLex.nt? = some m := derives_code_nt? hleafM.2
                  obtain ⟨hrIdx, hdiv2, hnp, htokEq, hnc, hbndNext, hriEq⟩ := hinv.tokBnd_real hgetA hleafM.1
                  have htGoalM : t.goalAt a0 = some (lexicalGoalOf m) := by
                    refine hgoalTs a0 (lexicalGoalOf m) (Nat.le_refl _) (by omega) ?_
                    dsimp only [Tree.goalAt.inKids]
                    have hg1 := (lex_goalAt_one a0 hntLex).1 0 (by omega)
                    rw [Nat.add_zero] at hg1; rw [hg1]
                  have hscM := hscanGoal _ hrIdx (lexicalGoalOf m) (hriEq.symm ▸ htGoalM)
                  let blk := hinv.blocks[(toks.take a0).countP (·.virt.isNone)]'hrIdx
                  have hbV := hinv.hvalid blk (List.getElem_mem hrIdx)
                  have hlenSl : (slice cs.toList blk.tokEl.i blk.tokEl.j).length = blk.tokEl.j - blk.tokEl.i := by
                    unfold slice; rw [List.length_take, List.length_drop, Array.length_toList]
                    have := hbV.2.2.2.2.1; have := hbV.2.2.2.2.2.1; omega
                  have hderLexM := hleafM.2
                  rw [htokEq] at hderLexM; dsimp only at hderLexM; rw [hlenSl] at hderLexM
                  have hsynLf : SynLeaf Ecma.Spec.gl cx Engine.Model.codePrims cs.toList first vs m
                      (tokBnd els toks a0) (tokBnd els toks (a0 + 1)) :=
                    ⟨hnp, blk.tokEl.i, blk.tokEl.j, blk.lt, blk.tokEl.tree, tLex,
                     hdiv2.symm ▸ hscM, hdiv2.symm ▸ hnc, hderLexM, hbndNext⟩
                  have hfk : forKeep s.rule.lhs m (tokBnd els toks (a0 + 1)) = true :=
                    hbndNext ▸ forKeep_two_mul _ _ _
                  exact ⟨.lex m (tokBnd els toks a0) (tokBnd els toks (a0 + 1)) :: dksr,
                    .leaf hemM hsynLf hfk hchCond hswr,
                    .cons rfl (.lex a0 hntLex) hskr,
                    ⟨a0 + 1, by omega, hh0LeJ0, ⟨rfl, rfl, rfl⟩, hbndr⟩⟩
              | false =>
                have hneM : Ecma.Spec.gl.alts cx .syntactic m ≠ [] := by
                  intro hnil; rw [altsOf_eq hok, hnil] at hemM; cases hemM
                have hszT0 : treeSynSize t0 < sz := by
                  rw [treeListSynSize] at hszTs; omega
                have hgoalT0 : ∀ idx g, a0 ≤ idx → idx < h0 → t0.goalAt idx = some g → t.goalAt idx = some g := by
                  intro idx g hlo hhi hg0
                  refine hgoalTs idx g hlo (by omega) ?_
                  dsimp only [Tree.goalAt.inKids]; rw [hg0]
                obtain ⟨dt0, hpl0, hsk0, hbnd0⟩ :=
                  ihOuter (treeSynSize t0) hszT0 (Nat.le_refl _) (by omega) hneM hstM hfheTs.1 hgoalT0
                -- Prove `forKeep s.rule.lhs m (tokBnd els toks h0) = true`:
                have hfk : forKeep s.rule.lhs m (tokBnd els toks h0) = true := by
                  rw [hlhsS]; unfold forKeep
                  by_cases hfm : (n0 == .ForStatement && m == .LexicalDeclaration) = true
                  · simp only [Bool.and_eq_true, beq_iff_eq] at hfm
                    obtain ⟨rfl, rfl⟩ := hfm
                    have hbndLt := lexicalDeclaration_pos hok hcp hinv.hvsBound hpl0
                    have ha0LtH0 : a0 < h0 := by
                      by_cases hle : h0 ≤ a0
                      · have := (hinv.tokBnd_le_iff (by omega) ha0LeLen).mpr hle; omega
                      · omega
                    have ht0Nt : t0.nt? = some .LexicalDeclaration := by
                      cases hstM with
                      | node _ _ _ _ _ => rfl
                      | lex hnil _ _ => exact absurd hnil hneM
                    have hm1Lt : h0 - 1 < toks.length := by omega
                    have hvNoneLast : toks[h0 - 1].virt = none :=
                      hforU rfl t0 (hsubK t0 (List.mem_cons_self ..)) ht0Nt toks[h0 - 1]
                        (by rw [hspT0]; exact List.getElem?_eq_getElem hm1Lt)
                    unfold tokBnd
                    rw [List.getElem?_eq_getElem hm1Lt, Option.bind_some, hvNoneLast]
                    simp [show (2 * tokPos els toks h0) % 2 = 0 from by omega]
                  · simp only [Bool.and_assoc] at *
                    cases hn0F : n0 == .ForStatement
                    · simp
                    · cases hmF : m == .LexicalDeclaration
                      · simp
                      · simp [hn0F, hmF] at hfm
                exact ⟨dt0 :: dksr,
                  .nt hemM hpl0 hfk hchCond hswr,
                  .cons hspT0 hsk0 hskr,
                  ⟨h0, ha0LeH0, hh0LeJ0, hbnd0, hbndr⟩⟩
        obtain ⟨dks, hsw, hsk, hbnd⟩ :=
          hseqT s.alt.rhs 0 i0 mMask kids (Nat.le_refl _) (Nat.zero_le _) rfl hseq0 hfheKids
            (fun _ h => h) hgoalU
        have hmMask : mMask ∈ masks s.alt.opts := hoptsS ▸ S.seqWith_masks hsw
        obtain ⟨hpeq, id', _, hid', _⟩ := prodIdOf_spec hok hsSpec hmMask
        have hidEq : id' = pId := Option.some.inj (hid'.symm.trans hpidSpec)
        subst hidEq
        exact ⟨.node n0 id' s ps0 (tokBnd els toks i0) (tokBnd els toks j0) mMask dks,
          .node s hsMem trivial hgrd (hpeq.trans hid') hsw,
          .node hsk,
          ⟨rfl, rfl, hbnd⟩⟩
  have hneGoal : Ecma.Spec.gl.alts cx .syntactic goal ≠ [] := by
    have hhr : hasRule .syntactic goal.ctorIdx = true :=
      (hasRule_iff hok .syntactic goal.ctorIdx).mpr ⟨goal, rfl, hhasSyn⟩
    rw [Strict.hasRule_syntactic_eq hok cx goal] at hhr
    intro hnil; rw [hnil] at hhr; cases hhr
  obtain ⟨dt, hpl, hsk, hbnd⟩ :=
    htrans (treeSynSize t) (Nat.le_refl _) (Nat.le_refl _) hneGoal hstepRoot hfhe
      (fun _ _ _ _ hg => hg)
  have hbnd0 : tokBnd els toks 0 = 0 := by
    have h0F : (0 < 0 && ((toks[0 - 1]?).bind Token.virt).isSome) = false := rfl
    unfold tokBnd
    rw [h0F]
    simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
    by_cases hlenB : 0 < hinv.blocks.length
    · have hp0 : tokPos els toks 0 = (hinv.blocks[0]'hlenB).p := (hinv.tokPos_eq 0).1 hlenB
      rw [hp0]
      have ⟨hprev0, _⟩ := (blocksChain_pos_mono hinv.hchain hinv.hvalid).2.1 0 hlenB
      simp only [beq_self_eq_true, ↓reduceIte] at hprev0
      omega
    · have hp0 : tokPos els toks 0 = hinv.endPos :=
        (hinv.tokPos_eq 0).2 (by dsimp only [List.take, List.countP, List.countP.go]; omega)
      rw [hp0]
      have hnilB : hinv.blocks = [] := List.eq_nil_of_length_eq_zero (by omega)
      have hend0 := (blocksChain_pos_mono hinv.hchain hinv.hvalid).2.2.2 hnilB
      omega
  rw [hbnd0] at hpl
  obtain ⟨heDiv2, hnpEnd, hallVs⟩ := hinv.tokBnd_end
  have hsynDer := plainDerives_to_synDerives hok hcp hinv.hvsBound hpl
  have hdone : SynDone Ecma.Spec.gl cx Engine.Model.codePrims cs.toList first vs goal ps :=
    ⟨tokBnd els toks toks.length, cs.size, hinv.endLt, hsynDer,
     heDiv2 ▸ hinv.hendTriv, by simp, hnpEnd, hallVs⟩
  exact ⟨hinv, dt, hpl, hsk, hbnd, hdone⟩

/-! ### Part 5C: `Syntax.run` (`syntax_run_some_spec` and `syntax_run_none_spec`) -/

private theorem forIn_unique_find_spec {T : Type} {p : Nat → Bool}
    {body : Nat → Option Nat → SM T (ForInStep (Option Nat))}
    (hfalse : ∀ e acc st, p e = false → (body e acc).run st = .ok (.yield acc, st))
    (htrueNone : ∀ e st, p e = true → (body e none).run st = .ok (.yield (some e), st))
    (htrueSome : ∀ e a st r s', p e = true → (body e (some a)).run st ≠ .ok (r, s')) :
    ∀ (l : List Nat) (init : Option Nat) (st : St T) (res : Option Nat) (st' : St T),
      (forIn l init body).run st = .ok (res, st') →
      st' = st ∧
      match init, res with
      | none, none => ∀ x ∈ l, p x = false
      | none, some e => e ∈ l ∧ p e = true ∧ ∀ x ∈ l, p x = true → x = e
      | some _a, none => False
      | some a, some e => e = a ∧ ∀ x ∈ l, p x = false := by
  intro l
  induction l with
  | nil =>
    intro init st res st' hrun
    rw [List.forIn_nil] at hrun
    obtain ⟨rfl, rfl⟩ := sm_pure_ok hrun
    refine ⟨rfl, ?_⟩
    cases init <;> simp
  | cons hd tl ih =>
    intro init st res st' hrun
    rw [List.forIn_cons] at hrun
    obtain ⟨step, s1, hbRun, hrRest⟩ := sm_bind_ok hrun
    cases hp : p hd with
    | false =>
      rw [hfalse hd init st hp] at hbRun
      injection hbRun with hp1; injection hp1 with hstep hs1; subst hstep; subst hs1
      dsimp only at hrRest
      obtain ⟨rfl, hspec⟩ := ih init st res st' hrRest
      refine ⟨rfl, ?_⟩
      cases init <;> cases res
      · intro x hx; rcases List.mem_cons.mp hx with rfl | hm; exact hp; exact hspec x hm
      · refine ⟨List.mem_cons_of_mem _ hspec.1, hspec.2.1, fun x hx hpx => ?_⟩
        rcases List.mem_cons.mp hx with rfl | hm
        · rw [hp] at hpx; cases hpx
        · exact hspec.2.2 x hm hpx
      · exact hspec
      · refine ⟨hspec.1, fun x hx => ?_⟩
        rcases List.mem_cons.mp hx with rfl | hm; exact hp; exact hspec.2 x hm
    | true =>
      cases init with
      | some a => exact absurd hbRun (htrueSome hd a st step s1 hp)
      | none =>
        rw [htrueNone hd st hp] at hbRun
        injection hbRun with hp1; injection hp1 with hstep hs1; subst hstep; subst hs1
        dsimp only at hrRest
        obtain ⟨rfl, hspec⟩ := ih (some hd) st res st' hrRest
        refine ⟨rfl, ?_⟩
        cases res with
        | none => exact nomatch hspec
        | some e =>
          obtain ⟨rfl, hallF⟩ := hspec
          refine ⟨List.mem_cons_self .., hp, fun x hx hpx => ?_⟩
          rcases List.mem_cons.mp hx with rfl | hm
          · rfl
          · rw [hallF x hm] at hpx; cases hpx

private theorem isDone_iff_synDone (hok : parseTablesOk = true)
    {cx : Ctx} {cs : Array Nat} (hcp : ∀ c ∈ cs.toList, c ≤ 0x10FFFF)
    {first : Bool} {stamp : Nat} {vs : List (Nat × Bool)} (hvs : ∀ pb ∈ vs, pb.1 ≤ cs.size)
    {goal : NT} {ps : List Param} {es : Ends}
    (hesIff : ∀ j, es.mem j = true ↔ ∃ dt, (synAlphaSpec hok hcp first cx stamp vs hvs).PlainDerives goal ps 0 j dt) :
    (∃ e ∈ es.toList,
      ((Lex.skip Engine.builder cs first cx (e / 2)).1 ≥ cs.size &&
        !Syntax.pending vs e && vs.all (fun (p, _) => p ≤ e / 2)) = true) ↔
    SynDone Ecma.Spec.gl cx Engine.Model.codePrims cs.toList first vs goal ps := by
  constructor
  · rintro ⟨e, heMem, hcond⟩
    simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true', Syntax.pending] at hcond
    obtain ⟨⟨hskGe, hnp⟩, hallVs⟩ := hcond
    obtain ⟨dt, hpl⟩ := (hesIff e).mp ((Ends.mem_toList es e).mp heMem)
    have hsynD := plainDerives_to_synDerives hok hcp hvs hpl
    have htrSk := (skip_spec (cx := cx) hok hcp first (e / 2)).2.2.2.1
    exact ⟨e, _, _, hsynD, htrSk, by rw [Array.length_toList]; exact hskGe, hnp, hallVs⟩
  · rintro ⟨e, k, lt, hsynD, htr, hkGe, hnp, hallVs⟩
    obtain ⟨dt, hpl⟩ := synDerives_to_plainDerives (stamp := stamp) hok hcp hvs hsynD
    have heMem : e ∈ es.toList := (Ends.mem_toList es e).mpr ((hesIff e).mpr ⟨dt, hpl⟩)
    have hskEq := (trivia_eq_skip hok hcp).mp htr
    refine ⟨e, heMem, ?_⟩
    rw [hskEq]; dsimp only [Syntax.pending]
    rw [Array.length_toList] at hkGe
    simp [hkGe, hnp, hallVs]

theorem syntax_run_some_spec (hok : parseTablesOk = true)
    {cs : Array Nat} (hcp : ∀ c ∈ cs.toList, c ≤ 0x10FFFF)
    {cx : Ctx} {stamp : Nat} {goal : NT}
    (hhasSyn : (Ecma.Spec.gl.rulesOf .syntactic).any (·.lhs == goal) = true)
    {ps : List Param} {nd : Engine.Model.Node}
    (hrun : Syntax.run Engine.builder cs cx stamp goal ps = .ok (some nd)) :
    ∃ els toks t,
      Scans Ecma.Spec.gl cx Engine.Model.codePrims cs.toList els ∧
      GoalsAt goal els toks t ∧
      toks.filter (·.virt.isNone) = tokensOf cs.toList els ∧
      toks.all (fun k => k.virt.isNone || !k.lt) = true ∧
      ASIOk Ecma.Spec.gl cx Engine.Model.codePrims goal ps cs.toList els toks ∧
      Sentence Ecma.Spec.gl cx Engine.Model.codePrims goal ps toks t ∧
      ForHeadersExplicit toks t ∧
      Ecma.Model.NodeRel Engine.Impl stamp cs.toList (Ecma.Grammar.tokenSpan els toks) nd t ∧
      Strict.PosSynStep cx Engine.Model.codePrims toks goal ps 0 toks.length t ∧
      Strict.synHeight t ≤ Syntax.depth cs.size + 1 ∧
      (∀ (strict : Bool) els2 toks2 t2,
        let G : Ecma.GrammarCtx := { gl := Ecma.Spec.gl, cx := cx, P := Engine.Model.codePrims, strict := strict }
        Scans Ecma.Spec.gl cx Engine.Model.codePrims cs.toList els2 →
        GoalsAt goal els2 toks2 t2 →
        toks2.filter (·.virt.isNone) = tokensOf cs.toList els2 →
        toks2.all (fun k => k.virt.isNone || !k.lt) = true →
        ASIOk Ecma.Spec.gl cx Engine.Model.codePrims goal ps cs.toList els2 toks2 →
        Sentence Ecma.Spec.gl cx Engine.Model.codePrims goal ps toks2 t2 →
        ForHeadersExplicit toks2 t2 →
        NonStrictOk Ecma.Spec.gl (G.StrictIn cs.toList els2 toks2) [] t2 →
        NonStrictOk Ecma.Spec.gl (G.StrictIn cs.toList els toks) [] t) := by
  let first := firstOf goal
  unfold Syntax.run at hrun
  rw [StateT.run'_eq] at hrun
  rcases except_eq_err_or_ok
      ((Syntax.run.go Engine.builder cs cx stamp goal ps (2 * cs.size + 2) first (cs.size + 2) []).run
        { steps := Syntax.budget cs.size }) with ⟨err, Hgo⟩ | ⟨⟨optN, stEnd⟩, Hgo⟩
  · rw [Hgo] at hrun; cases hrun
  · rw [Hgo] at hrun; simp only [Functor.map, Except.map] at hrun
    injection hrun with hoptEq; subst hoptEq
    -- Induct on `fuel` in `Syntax.run.go`:
    have hgo : ∀ (fuel : Nat) (vs : List (Nat × Bool))
        (st st' : St (Syntax.Memo Engine.builder cs first cx)),
        ValidASI Ecma.Spec.gl cx Engine.Model.codePrims cs.toList first goal ps vs →
        (Syntax.run.go Engine.builder cs cx stamp goal ps (2 * cs.size + 2) first fuel vs).run st =
          .ok (some nd, st') →
        ∃ els toks t,
          Scans Ecma.Spec.gl cx Engine.Model.codePrims cs.toList els ∧
          GoalsAt goal els toks t ∧
          toks.filter (·.virt.isNone) = tokensOf cs.toList els ∧
          toks.all (fun k => k.virt.isNone || !k.lt) = true ∧
          ASIOk Ecma.Spec.gl cx Engine.Model.codePrims goal ps cs.toList els toks ∧
          Sentence Ecma.Spec.gl cx Engine.Model.codePrims goal ps toks t ∧
          ForHeadersExplicit toks t ∧
          Ecma.Model.NodeRel Engine.Impl stamp cs.toList (Ecma.Grammar.tokenSpan els toks) nd t ∧
          Strict.PosSynStep cx Engine.Model.codePrims toks goal ps 0 toks.length t ∧
          Strict.synHeight t ≤ Syntax.depth cs.size + 1 ∧
          (∀ (strict : Bool) els2 toks2 t2,
            let G : Ecma.GrammarCtx := { gl := Ecma.Spec.gl, cx := cx, P := Engine.Model.codePrims, strict := strict }
            Scans Ecma.Spec.gl cx Engine.Model.codePrims cs.toList els2 →
            GoalsAt goal els2 toks2 t2 →
            toks2.filter (·.virt.isNone) = tokensOf cs.toList els2 →
            toks2.all (fun k => k.virt.isNone || !k.lt) = true →
            ASIOk Ecma.Spec.gl cx Engine.Model.codePrims goal ps cs.toList els2 toks2 →
            Sentence Ecma.Spec.gl cx Engine.Model.codePrims goal ps toks2 t2 →
            ForHeadersExplicit toks2 t2 →
            NonStrictOk Ecma.Spec.gl (G.StrictIn cs.toList els2 toks2) [] t2 →
            NonStrictOk Ecma.Spec.gl (G.StrictIn cs.toList els toks) [] t) := by
      intro fuel
      induction fuel with
      | zero =>
        intro _ _ _ _ hr
        unfold Syntax.run.go at hr; rw [sm_run_throw] at hr; cases hr
      | succ fuel ih =>
        intro vs st st' hvalid hr
        obtain ⟨hvsBnd, hvsUniq⟩ := validASI_props hok hcp hvalid
        let S := synAlphaSpec hok hcp first cx stamp vs hvsBnd
        have hordF : orderedBy cx .syntactic = false := orderedBy_syntactic_false hok cx
        unfold Syntax.run.go at hr
        obtain ⟨_, s0, hmod, hr1⟩ := sm_bind_ok hr
        rw [sm_run_modify] at hmod; cases hmod
        obtain ⟨es, s1, hfe, hr2⟩ := sm_bind_ok hr1
        have ⟨hmi1, hna1, hfw1, hesIff, hhitFar, hubFar⟩ :=
          S.finalEnds_far_spec hok (Or.inl rfl) hordF (Syntax.depth cs.size) goal ps
            _ es s1 trivial rfl rfl rfl rfl hfe
        obtain ⟨doneOpt, s2, hforRun, hr3⟩ := sm_bind_ok hr2
        let isDoneP := fun e : Nat =>
          decide ((Lex.skip Engine.builder cs first cx (e / 2)).1 ≥ cs.size) &&
            !Syntax.pending vs e && vs.all (fun (p, _) => p ≤ e / 2)
        have ⟨hs2Eq, hdoneSpec⟩ := forIn_unique_find_spec (p := isDoneP)
          (fun e acc st0 hpF => by
            dsimp only [isDoneP] at hpF; dsimp only; rw [hpF]
            simp only [Bool.false_eq_true, ↓reduceIte]; rfl)
          (fun e st0 hpT => by
            dsimp only [isDoneP] at hpT; dsimp only; rw [hpT]
            simp only [↓reduceIte, Option.isSome_none, Bool.false_eq_true]; rfl)
          (fun e a st0 r s' hpT => by
            dsimp only [isDoneP] at hpT; dsimp only; rw [hpT]
            simp only [↓reduceIte, Option.isSome_some]; rintro ⟨⟩)
          es.toList none s1 doneOpt s2 hforRun
        subst s2
        cases doneOpt with
        | some e =>
          obtain ⟨heInEs, hpTrue, heUniq⟩ := hdoneSpec
          dsimp only at hr3
          obtain ⟨ndBuilt, s3, hbldRun, hr4⟩ := sm_bind_ok hr3
          obtain ⟨_, hr5⟩ := sm_unless_throw_jp hr4
          obtain ⟨hEqSome, _⟩ := sm_pure_ok hr5
          injection hEqSome with hndEq; subst ndBuilt
          have hbi1 : S.BuildInv s1 :=
            AlphaSpec.BuildInv.of_fresh_after_finalEnds hmi1 hna1 hfw1
          have hstmp : S.LeafStamp.all (· == stamp) = true := beq_self_eq_true stamp
          obtain ⟨_, _, _, dt, hmd, hdrel, hdtUniq⟩ :=
            S.build_spec hok builderSpec_engine (Or.inl rfl) (Syntax.depth cs.size) stamp hstmp
              (Syntax.depth cs.size) goal ps 0 e s1 nd s3 hbi1 hbldRun
          have hdHeight : dtreeSynHeight dt ≤ Syntax.depth cs.size + 1 :=
            build_dtreeSynHeight S hok (Or.inl rfl) (Syntax.depth cs.size) stamp hstmp
              (Syntax.depth cs.size) goal ps 0 e s1 nd s3 hbi1 hbldRun dt hmd
          have hpl : S.PlainDerives goal ps 0 e dt :=
            S.derivesWith_mono_allow (fun _ _ _ _ _ => trivial) hmd
          obtain ⟨rs, mkTree, hc, hsk, hbndM, _, hgl, hembTree⟩ :=
            sound_extract hok hcp hvsBnd hvsUniq hpl hdrel
          have hpTrue' := hpTrue
          dsimp only [isDoneP, Syntax.pending] at hpTrue'
          simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at hpTrue'
          obtain ⟨⟨heof, hnpEnd⟩, hallVs⟩ := hpTrue'
          obtain ⟨els, toks, hinv, hemb, hlenEq, hgoals⟩ :=
            build_tokStream_of_rawChain hok hcp hvsBnd hvsUniq hc heof hnpEnd hallVs
              (fun u hu => by simpa using (hgl 0).1 u hu)
          obtain ⟨hfhe, hnrel, hderK⟩ := hembTree els toks 0 hemb
          simp only [Nat.zero_add, ← hlenEq] at hnrel hderK
          have hsent : Sentence Ecma.Spec.gl cx Engine.Model.codePrims goal ps toks (mkTree 0) :=
            ⟨2, fun k hk => by
              obtain ⟨k0, rfl⟩ : ∃ k0, k = k0 + 2 := ⟨k - 2, by omega⟩
              exact hderK k0⟩
          have hsk0 := hsk 0
          have hbnd1 : DTreeBndsMatch (tokBnd els toks) dt 0 toks.length := by
            have := hbndM (tokBnd els toks) 0 (fun u hu => by simpa using hemb.2.2.1 u hu)
            simpa [← hlenEq] using this
          have hdone1 : SynDone Ecma.Spec.gl cx Engine.Model.codePrims cs.toList first vs goal ps :=
            (isDone_iff_synDone hok hcp hvsBnd hesIff).mp ⟨e, heInEs, hpTrue⟩
          refine ⟨els, toks, mkTree 0, hinv.scans, hgoals, hinv.htoksFilt, hinv.htoksAll,
            ⟨vs, hvalid, hinv.hasi⟩, hsent, hfhe, hnrel,
            Strict.posSynStep_of_derives hsent,
            by rw [sameDTreeSkeleton_synHeight hsk0]; exact hdHeight,
            fun strict els2 toks2 t2 hsc2 hgl2 hfi2 hal2 ⟨vs2, hv2, hm2⟩ hsn2 hfh2 hns2 => ?_⟩
          obtain ⟨hinv2, dt2, hpl2, hsk2, hbnd2, hdone2⟩ :=
            complete_translate (stamp := stamp) hok hcp hhasSyn hsc2 hgl2 hfi2 hal2 hv2 hm2 hsn2 hfh2
          have hvsEq : vs2 = vs := validASI_unique_done hok hcp hv2 hdone2 hvalid hdone1
          subst hvsEq
          -- `dt2` ends at `e2 := tokBnd els2 toks2 toks2.length`, which must equal `e`:
          let e2 := tokBnd els2 toks2 toks2.length
          have he2InEs : e2 ∈ es.toList :=
            (Ends.mem_toList es e2).mpr ((hesIff e2).mpr ⟨dt2, hpl2⟩)
          obtain ⟨he2Div2, hnp2, hallVs2⟩ := hinv2.tokBnd_end
          have hskEq2 := (trivia_eq_skip hok hcp).mp hinv2.hendTriv
          have hp2True : isDoneP e2 = true := by
            dsimp only [isDoneP, Syntax.pending, e2]
            rw [he2Div2, hskEq2]
            simp [hnp2, he2Div2 ▸ hallVs2]
          have he2Eq : e2 = e := heUniq e2 he2InEs hp2True
          have hpl2' : S.PlainDerives goal ps 0 e dt2 := he2Eq ▸ hpl2
          have hdt2Eq : dt2 = dt :=
            hdtUniq dt2 (S.derivesWith_mono_allow (fun _ _ _ _ _ => by
              simp [AlphaSpec.CommitAllow, Syntax.alpha, orderedNts_nil_of_ordered_false hok hordF]) hpl2')
          subst hdt2Eq
          have ⟨_, hsynSkel⟩ := sameDTreeSkeleton_unique_and_syn hsk2 hsk0
          obtain ⟨hlen12, hbndEq⟩ := dtreeBndsMatch_eq hbnd2 hbnd1
          have hspEq := tokenSpan_congr_of_tokBnd_eq hok hcp hinv2 hinv hlen12 (fun u hu => hbndEq u (Nat.zero_le u) hu)
          have htxtEq : Ecma.Grammar.tokenText cs.toList els2 toks2 = Ecma.Grammar.tokenText cs.toList els toks := by
            funext a b; unfold Ecma.Grammar.tokenText; rw [hspEq]
          exact (sameSynSkeleton_nonStrictOk _ htxtEq .nil hsynSkel).mp hns2
        | none =>
          dsimp only at hr3
          have hnotDone : ¬ SynDone Ecma.Spec.gl cx Engine.Model.codePrims cs.toList first vs goal ps := by
            dsimp only at hdoneSpec
            rw [← isDone_iff_synDone hok hcp hvsBnd hesIff]
            rintro ⟨e, heIn, hpT⟩
            change isDoneP e = true at hpT
            rw [hdoneSpec e heIn] at hpT; cases hpT
          have hhitSyn := (specHit_iff_synHit hok hcp hvsBnd).mp hhitFar
          have hubSyn : ∀ h, SynHit Ecma.Spec.gl cx Engine.Model.codePrims cs.toList first vs goal ps h → h ≤ s1.far :=
            fun h hh => hubFar h ((specHit_iff_synHit hok hcp hvsBnd).mpr hh)
          obtain ⟨_, _, hget3, hr3⟩ := sm_bind_ok hr3
          cases hget3
          obtain ⟨insOpt, s3, hinsRun, hr4⟩ := sm_bind_ok hr3
          obtain ⟨hinsSome, _⟩ := insertion_spec hok hcp hnotDone hhitSyn hubSyn hinsRun
          cases insOpt with
          | some pp =>
            exact ih (vs ++ [(pp.1, pp.2)]) s3 st' (.step hvalid ((hinsSome pp.1 pp.2).mp rfl)) hr4
          | none =>
            obtain ⟨hEq, _⟩ := sm_pure_ok hr4; cases hEq
    exact hgo (cs.size + 2) [] _ _ .nil Hgo

theorem syntax_run_none_spec (hok : parseTablesOk = true)
    {cs : Array Nat} (hcp : ∀ c ∈ cs.toList, c ≤ 0x10FFFF)
    {cx : Ctx} {stamp : Nat} {goal : NT}
    (hhasSyn : (Ecma.Spec.gl.rulesOf .syntactic).any (·.lhs == goal) = true)
    {ps : List Param}
    (hrun : Syntax.run Engine.builder cs cx stamp goal ps = .ok none) :
    ∀ els toks t,
      Scans Ecma.Spec.gl cx Engine.Model.codePrims cs.toList els →
      GoalsAt goal els toks t →
      toks.filter (·.virt.isNone) = tokensOf cs.toList els →
      toks.all (fun k => k.virt.isNone || !k.lt) = true →
      ASIOk Ecma.Spec.gl cx Engine.Model.codePrims goal ps cs.toList els toks →
      Sentence Ecma.Spec.gl cx Engine.Model.codePrims goal ps toks t →
      ForHeadersExplicit toks t →
      False := by
  let first := firstOf goal
  unfold Syntax.run at hrun
  rw [StateT.run'_eq] at hrun
  rcases except_eq_err_or_ok
      ((Syntax.run.go Engine.builder cs cx stamp goal ps (2 * cs.size + 2) first (cs.size + 2) []).run
        { steps := Syntax.budget cs.size }) with ⟨err, Hgo⟩ | ⟨⟨optN, stEnd⟩, Hgo⟩
  · rw [Hgo] at hrun; cases hrun
  · rw [Hgo] at hrun; simp only [Functor.map, Except.map] at hrun
    injection hrun with hoptEq; subst hoptEq
    have hgo : ∀ (fuel : Nat) (vs : List (Nat × Bool))
        (st st' : St (Syntax.Memo Engine.builder cs first cx)),
        ValidASI Ecma.Spec.gl cx Engine.Model.codePrims cs.toList first goal ps vs →
        (Syntax.run.go Engine.builder cs cx stamp goal ps (2 * cs.size + 2) first fuel vs).run st =
          .ok (none, st') →
        ∃ vsStuck,
          ValidASI Ecma.Spec.gl cx Engine.Model.codePrims cs.toList first goal ps vsStuck ∧
          ¬ SynDone Ecma.Spec.gl cx Engine.Model.codePrims cs.toList first vsStuck goal ps ∧
          ∀ p paren, ¬ NextASI Ecma.Spec.gl cx Engine.Model.codePrims cs.toList first vsStuck goal ps p paren := by
      intro fuel
      induction fuel with
      | zero =>
        intro _ _ _ _ hr
        unfold Syntax.run.go at hr; rw [sm_run_throw] at hr; cases hr
      | succ fuel ih =>
        intro vs st st' hvalid hr
        obtain ⟨hvsBnd, _⟩ := validASI_props hok hcp hvalid
        let S := synAlphaSpec hok hcp first cx stamp vs hvsBnd
        have hordF : orderedBy cx .syntactic = false := orderedBy_syntactic_false hok cx
        unfold Syntax.run.go at hr
        obtain ⟨_, s0, hmod, hr1⟩ := sm_bind_ok hr
        rw [sm_run_modify] at hmod; cases hmod
        obtain ⟨es, s1, hfe, hr2⟩ := sm_bind_ok hr1
        have ⟨_, _, _, hesIff, hhitFar, hubFar⟩ :=
          S.finalEnds_far_spec hok (Or.inl rfl) hordF (Syntax.depth cs.size) goal ps
            _ es s1 trivial rfl rfl rfl rfl hfe
        obtain ⟨doneOpt, s2, hforRun, hr3⟩ := sm_bind_ok hr2
        let isDoneP := fun e : Nat =>
          decide ((Lex.skip Engine.builder cs first cx (e / 2)).1 ≥ cs.size) &&
            !Syntax.pending vs e && vs.all (fun (p, _) => p ≤ e / 2)
        have ⟨hs2Eq, hdoneSpec⟩ := forIn_unique_find_spec (p := isDoneP)
          (fun e acc st0 hpF => by
            dsimp only [isDoneP] at hpF; dsimp only; rw [hpF]
            simp only [Bool.false_eq_true, ↓reduceIte]; rfl)
          (fun e st0 hpT => by
            dsimp only [isDoneP] at hpT; dsimp only; rw [hpT]
            simp only [↓reduceIte, Option.isSome_none, Bool.false_eq_true]; rfl)
          (fun e a st0 r s' hpT => by
            dsimp only [isDoneP] at hpT; dsimp only; rw [hpT]
            simp only [↓reduceIte, Option.isSome_some]; rintro ⟨⟩)
          es.toList none s1 doneOpt s2 hforRun
        subst s2
        cases doneOpt with
        | some e =>
          dsimp only at hr3
          obtain ⟨_, _, _, hr4⟩ := sm_bind_ok hr3
          obtain ⟨_, hr5⟩ := sm_unless_throw_jp hr4
          obtain ⟨hEq, _⟩ := sm_pure_ok hr5; cases hEq
        | none =>
          dsimp only at hr3
          have hnotDone : ¬ SynDone Ecma.Spec.gl cx Engine.Model.codePrims cs.toList first vs goal ps := by
            dsimp only at hdoneSpec
            rw [← isDone_iff_synDone hok hcp hvsBnd hesIff]
            rintro ⟨e, heIn, hpT⟩
            change isDoneP e = true at hpT
            rw [hdoneSpec e heIn] at hpT; cases hpT
          have hhitSyn := (specHit_iff_synHit hok hcp hvsBnd).mp hhitFar
          have hubSyn : ∀ h, SynHit Ecma.Spec.gl cx Engine.Model.codePrims cs.toList first vs goal ps h → h ≤ s1.far :=
            fun h hh => hubFar h ((specHit_iff_synHit hok hcp hvsBnd).mpr hh)
          obtain ⟨_, _, hget3, hr3⟩ := sm_bind_ok hr3
          cases hget3
          obtain ⟨insOpt, s3, hinsRun, hr4⟩ := sm_bind_ok hr3
          obtain ⟨hinsSome, hinsNone⟩ := insertion_spec hok hcp hnotDone hhitSyn hubSyn hinsRun
          cases insOpt with
          | some pp =>
            exact ih (vs ++ [(pp.1, pp.2)]) s3 st' (.step hvalid ((hinsSome pp.1 pp.2).mp rfl)) hr4
          | none =>
            exact ⟨vs, hvalid, hnotDone, hinsNone.mp rfl⟩
    obtain ⟨vsStuck, hvStuck, hnotDoneStuck, hnoNextStuck⟩ := hgo (cs.size + 2) [] _ _ .nil Hgo
    intro els toks t hscans hgoals hfilt hall ⟨vs2, hv2, hm2⟩ hsent hfhe
    obtain ⟨_, _, _, _, _, hdone2⟩ :=
      complete_translate (stamp := stamp) hok hcp hhasSyn hscans hgoals hfilt hall hv2 hm2 hsent hfhe
    exact validASI_stuck_no_done hok hcp hvStuck hnotDoneStuck hnoNextStuck hv2 hdone2

end Engine.Parse
