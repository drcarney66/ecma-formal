module

public import Engine.Model.Relabel
public import Engine.Model
public import Engine.Proofs.Parse.Laws

@[expose] public section

/-!
# Soundness of `Engine.Model.Relabel.relabel`: `Ecma.Model.CoverLaws`

Proves `Engine.Impl.coverLaws`: for every invocation context `pc`, stamp `st`, parsed node `n`
(`Model.Parsed Impl pc n`), goal nonterminal `goal`, argument list `args`, parameter list `ps`
(`ParamsOf args ps`), code-point list `src` (`Impl.nodeSource n = Impl.seqOfNats src`), and
relabelled node `r` (`Impl.cover pc st n goal.ctorIdx args = some r`), there exists a derivation
tree `t` such that `(G.at pc).CoverIs Impl st goal ps src r t`.
-/

namespace Engine.Impl

open Ecma.Grammar Engine.Model Engine.Parse
open Ecma (ParamId NtId ProdId ParseCx GrammarCtx ParamsOf seqList)

private theorem char_eq_of_toNat_eq {c d : Char} (h : c.toNat = d.toNat) : c = d := by
  have := congrArg Char.ofNat h
  rwa [Char.ofNat_toNat, Char.ofNat_toNat] at this

private theorem nodeRel_node_inv_gen {M : Ecma.Model} {st0 : Nat} {src : List Nat}
    {sp : Nat → Nat → Nat × Nat} {nd0 : M.Node} {t0 : Tree}
    (hrel : Ecma.Model.NodeRel M st0 src sp nd0 t0) :
    ∀ {nd : Node} {nt : NT} {id : Nat} {ps : List Param} {i j : Nat} {kids : List Tree},
      M = Impl → HEq nd0 nd → t0 = .node nt id ps i j kids →
      Impl.nodeNt nd = nt.ctorIdx ∧
      Impl.nodeProd nd = id ∧
      (∀ p, (Impl.nodeArgs nd).contains p = true ↔ p ∈ ps) ∧
      Impl.nodeStamp nd = st0 ∧
      Impl.nodeSpan nd = sp i j ∧
      Impl.seqLen (Impl.nodeSource nd) = Impl.ofNat (slice src (sp i j).1 (sp i j).2).length ∧
      (∀ k, Impl.seqGet (Impl.nodeSource nd) (Impl.ofNat k) = (slice src (sp i j).1 (sp i j).2)[k]?.map Impl.ofNat) ∧
      Impl.seqLen (Impl.nodeKids nd) = Impl.ofNat (kids.filter (!·.isLeaf)).length ∧
      (∀ k, (Impl.seqGet (Impl.nodeKids nd) (Impl.ofNat k)).isSome = decide (k < (kids.filter (!·.isLeaf)).length)) ∧
      (∀ k t c, (kids.filter (!·.isLeaf))[k]? = some t → Impl.seqGet (Impl.nodeKids nd) (Impl.ofNat k) = some c →
        Ecma.Model.NodeRel Impl st0 src sp c t) := by
  cases hrel with
  | leaf => intro _ _ _ _ _ _ _ _ _ ht; cases ht
  | lex => intro _ _ _ _ _ _ _ _ _ ht; cases ht
  | node h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 =>
    intro nd nt id ps i j kids hM hnd ht
    subst hM; cases hnd
    injection ht with hnt hid hps hi hj hks
    subst hnt; subst hid; subst hps; subst hi; subst hj; subst hks
    exact ⟨h1, h2, fun p => List.contains_iff_mem.trans (h3 p), h4, h5, h6, h7, h8,
      fun k => Bool.eq_iff_iff.mpr ((Eq.to_iff (h9 k)).trans decide_eq_true_iff.symm), h10⟩

private theorem nodeRel_node_inv {st0 : Nat} {src : List Nat} {sp : Nat → Nat → Nat × Nat}
    {nd : Node} {nt : NT} {id : Nat} {ps : List Param} {i j : Nat} {kids : List Tree}
    (hrel : Ecma.Model.NodeRel Impl st0 src sp nd (.node nt id ps i j kids)) :
    Impl.nodeNt nd = nt.ctorIdx ∧
    Impl.nodeProd nd = id ∧
    (∀ p, (Impl.nodeArgs nd).contains p = true ↔ p ∈ ps) ∧
    Impl.nodeStamp nd = st0 ∧
    Impl.nodeSpan nd = sp i j ∧
    Impl.seqLen (Impl.nodeSource nd) = Impl.ofNat (slice src (sp i j).1 (sp i j).2).length ∧
    (∀ k, Impl.seqGet (Impl.nodeSource nd) (Impl.ofNat k) = (slice src (sp i j).1 (sp i j).2)[k]?.map Impl.ofNat) ∧
    Impl.seqLen (Impl.nodeKids nd) = Impl.ofNat (kids.filter (!·.isLeaf)).length ∧
    (∀ k, (Impl.seqGet (Impl.nodeKids nd) (Impl.ofNat k)).isSome = decide (k < (kids.filter (!·.isLeaf)).length)) ∧
    (∀ k t c, (kids.filter (!·.isLeaf))[k]? = some t → Impl.seqGet (Impl.nodeKids nd) (Impl.ofNat k) = some c →
      Ecma.Model.NodeRel Impl st0 src sp c t) :=
  nodeRel_node_inv_gen hrel rfl HEq.rfl rfl

private theorem nodeRel_lex_inv_gen {M : Ecma.Model} {st0 : Nat} {src : List Nat}
    {sp : Nat → Nat → Nat × Nat} {nd0 : M.Node} {t0 : Tree}
    (hrel : Ecma.Model.NodeRel M st0 src sp nd0 t0) :
    ∀ {nd : Node} {k : Nat} {sub : Tree},
      M = Impl → HEq nd0 nd → t0 = .lex k sub →
      Ecma.Model.NodeRel Impl st0 src (fun a b => ((sp k (k + 1)).1 + a, (sp k (k + 1)).1 + b)) nd sub := by
  cases hrel with
  | leaf => intro _ _ _ _ _ ht; cases ht
  | node => intro _ _ _ _ _ ht; cases ht
  | lex hsub =>
    intro nd k sub hM hnd ht
    subst hM; cases hnd
    injection ht with hk hsubEq
    subst hk; subst hsubEq
    exact hsub

private theorem nodeRel_lex_inv {st0 : Nat} {src : List Nat} {sp : Nat → Nat → Nat × Nat}
    {nd : Node} {k : Nat} {sub : Tree}
    (hrel : Ecma.Model.NodeRel Impl st0 src sp nd (.lex k sub)) :
    Ecma.Model.NodeRel Impl st0 src (fun a b => ((sp k (k + 1)).1 + a, (sp k (k + 1)).1 + b)) nd sub :=
  nodeRel_lex_inv_gen hrel rfl HEq.rfl rfl

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

/-! ## Section 1: Pure `glData` Grammar Certificates -/

def isCoverNtIdx (m : Nat) : Bool :=
  m == NT.CoverParenthesizedExpressionAndArrowParameterList.ctorIdx ||
  m == NT.CoverCallExpressionAndAsyncArrowHead.ctorIdx

private def noCoverCodeCert : Bool :=
  (List.range 32).all fun ci =>
    codeGrammars.all fun g =>
      (glData.alts (cxOfIdx ci) g .CoverParenthesizedExpressionAndArrowParameterList).isEmpty &&
      (glData.alts (cxOfIdx ci) g .CoverCallExpressionAndAsyncArrowHead).isEmpty

private theorem noCoverCodeCert_true : noCoverCodeCert = true := by decide

private theorem code_alts_cover_empty {cx : Ctx} {g : GrammarId} (hg : g ∈ codeGrammars)
    {n : NT} (hcov : isCoverNtIdx n.ctorIdx = true) :
    Ecma.Spec.gl.alts cx g n = [] := by
  have hci := List.all_eq_true.mp noCoverCodeCert_true (cxIdx cx) (List.mem_range.mpr (cxIdx_lt cx))
  rw [cxOfIdx_cxIdx] at hci
  have hgOk := List.all_eq_true.mp hci g hg
  simp only [Bool.and_eq_true, List.isEmpty_iff] at hgOk
  rw [← glData_eq]
  unfold isCoverNtIdx at hcov
  rcases Bool.or_eq_true_iff.mp hcov with h1 | h2
  · rw [nt_ctorIdx_inj (beq_iff_eq.mp h1)]; exact hgOk.1
  · rw [nt_ctorIdx_inj (beq_iff_eq.mp h2)]; exact hgOk.2

private def termNonEmpty : Terminal → Bool
  | .text str _ => !str.isEmpty
  | .cp _ => true

private def itemTermNonEmpty : Item → Bool
  | .sym (.t x) _ | .butNot (.t x) _ => termNonEmpty x
  | _ => true

private theorem item_term_nonempty_of_alts (hok : parseTablesOk = true) {cx : Ctx} {g : GrammarId} {n : NT} {s : Src}
    (hs : s ∈ Ecma.Spec.gl.alts cx g n) {it : Item} (hit : it ∈ s.alt.rhs) :
    itemTermNonEmpty it = true := by
  have h := srcItemTermOk_of_mem hok hs hit
  cases it with
  | sym sym0 _ | butNot sym0 _ =>
    cases sym0 with
    | t tx => cases tx <;> exact h
    | nt _ _ => rfl
  | _ => rfl

private theorem itemTermNonEmpty_sym {x : Terminal} {o : Bool}
    (h : itemTermNonEmpty (.sym (.t x) o) = true) :
    termNonEmpty x = true := h

private theorem itemTermNonEmpty_butNot {x : Terminal} {ex : Exclusion}
    (h : itemTermNonEmpty (.butNot (.t x) ex) = true) :
    termNonEmpty x = true := h

private def rulesForGrammar (g : GrammarId) : List Rule :=
  glData.rulesOf g ++
  (glData.blocks.flatMap fun b =>
    match b.kind with
    | .overlay sec _ _ => if overlayGrammar sec == g then b.rules else []
    | _ => [])

private theorem mem_writtenAlts_of_srcsOf {g : GrammarId} {r : Rule} {s : Src}
    (hs : s ∈ srcsOf g r) :
    s.grammar = g ∧ s.rule = r ∧ (writtenAlts r)[s.idx]? = some s.alt := by
  unfold srcsOf at hs
  rw [List.mem_map] at hs
  obtain ⟨⟨a, idx⟩, hz, hmk⟩ := hs
  dsimp only at hmk
  subst hmk
  have hgen : ∀ (l : List Alt) (off : Nat), (a, idx) ∈ l.zipIdx off →
      off ≤ idx ∧ l[idx - off]? = some a := by
    intro l; induction l with
    | nil => intro _ hm; nomatch hm
    | cons hd tl ih =>
      intro off hm
      rcases List.mem_cons.mp hm with heq | htl
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq; simp
      · obtain ⟨h1, h2⟩ := ih (off + 1) htl
        exact ⟨by omega, by rw [show idx - off = (idx - (off + 1)) + 1 from by omega, List.getElem?_cons_succ]; exact h2⟩
  exact ⟨rfl, rfl, by simpa using (hgen (writtenAlts r) 0 hz).2⟩

private theorem alts_src_origin {cx : Ctx} {g : GrammarId}
    (hbg : baseGrammar g = none) {n : NT} {s : Src}
    (hs : s ∈ glData.alts cx g n) :
    ((s.grammar = g ∧ s.rule ∈ glData.rulesOf g) ∨
     (s.grammar = .annexB ∧ ∃ b ∈ glData.blocks, ∃ sec md cd,
       b.kind = .overlay sec md cd ∧ overlayGrammar sec = g ∧ s.rule ∈ b.rules)) ∧
    (writtenAlts s.rule)[s.idx]? = some s.alt := by
  have hpin : ∀ x ∈ glData.pinned g n,
      ((x.grammar = g ∧ x.rule ∈ glData.rulesOf g) ∨
       (x.grammar = .annexB ∧ ∃ b ∈ glData.blocks, ∃ sec md cd,
         b.kind = .overlay sec md cd ∧ overlayGrammar sec = g ∧ x.rule ∈ b.rules)) ∧
      (writtenAlts x.rule)[x.idx]? = some x.alt := by
    intro x hx
    unfold GL.pinned at hx
    cases hf : (glData.rulesOf g).find? (·.lhs == n) with
    | some r =>
      rw [hf] at hx
      obtain ⟨hg, hr, halt⟩ := mem_writtenAlts_of_srcsOf hx
      exact ⟨Or.inl ⟨hg, hr ▸ List.mem_of_find?_eq_some hf⟩, hr ▸ halt⟩
    | none =>
      rw [hf, hbg] at hx; nomatch hx
  have hov : ∀ (bs : List (Block × OverlayMode)) (acc : List Src),
      (∀ pm ∈ bs, pm.1 ∈ glData.blocks ∧ ∃ sec md cd, pm.1.kind = .overlay sec md cd ∧ overlayGrammar sec = g) →
      (∀ x ∈ acc,
        ((x.grammar = g ∧ x.rule ∈ glData.rulesOf g) ∨
         (x.grammar = .annexB ∧ ∃ b ∈ glData.blocks, ∃ sec md cd,
           b.kind = .overlay sec md cd ∧ overlayGrammar sec = g ∧ x.rule ∈ b.rules)) ∧
        (writtenAlts x.rule)[x.idx]? = some x.alt) →
      ∀ x ∈ bs.foldl (fun a (b, m) =>
        match b.rules.find? (·.lhs == n), m with
        | none, _ => a
        | some r, .extend => a ++ (srcsOf .annexB r).filter fun s' => !a.any (·.alt == s'.alt)
        | some r, .replace => srcsOf .annexB r) acc,
      ((x.grammar = g ∧ x.rule ∈ glData.rulesOf g) ∨
       (x.grammar = .annexB ∧ ∃ b ∈ glData.blocks, ∃ sec md cd,
         b.kind = .overlay sec md cd ∧ overlayGrammar sec = g ∧ x.rule ∈ b.rules)) ∧
      (writtenAlts x.rule)[x.idx]? = some x.alt := by
    intro bs; induction bs with
    | nil => intro acc _ hacc x hx; exact hacc x hx
    | cons hd tl ih =>
      rcases hd with ⟨b, m⟩
      intro acc hbs hacc x hx
      obtain ⟨hbMem, sec, md, cd, hkind, hog⟩ := hbs (b, m) (List.mem_cons_self ..)
      have hbsTl := fun pm hpm => hbs pm (List.mem_cons_of_mem _ hpm)
      simp only [List.foldl_cons] at hx
      cases hfr : b.rules.find? (·.lhs == n) with
      | none => rw [hfr] at hx; exact ih acc hbsTl hacc x hx
      | some r =>
        have hrMem := List.mem_of_find?_eq_some hfr
        cases m with
        | extend =>
          rw [hfr] at hx
          refine ih _ hbsTl (fun y hy => ?_) x hx
          rcases List.mem_append.mp hy with hya | hyf
          · exact hacc y hya
          · obtain ⟨hg, hr, halt⟩ := mem_writtenAlts_of_srcsOf (List.mem_filter.mp hyf).1
            exact ⟨Or.inr ⟨hg, b, hbMem, sec, md, cd, hkind, hog, hr ▸ hrMem⟩, hr ▸ halt⟩
        | replace =>
          rw [hfr] at hx
          refine ih _ hbsTl (fun y hy => ?_) x hx
          obtain ⟨hg, hr, halt⟩ := mem_writtenAlts_of_srcsOf hy
          exact ⟨Or.inr ⟨hg, b, hbMem, sec, md, cd, hkind, hog, hr ▸ hrMem⟩, hr ▸ halt⟩
  unfold GL.alts at hs
  refine hov (glData.overlays cx g) (glData.pinned g n) (fun pm hpm => ?_) hpin s hs
  unfold GL.overlays at hpm
  split at hpm
  · nomatch hpm
  · rw [List.mem_filterMap] at hpm
    obtain ⟨b, hbMem, hopt⟩ := hpm
    cases hbk : b.kind with
    | main | supplemental _ => rw [hbk] at hopt; cases hopt
    | overlay sec md cd =>
      rw [hbk] at hopt; dsimp only at hopt
      split at hopt
      · next hcond =>
        injection hopt with hpmEq; subst hpmEq
        simp only [Bool.and_eq_true, beq_iff_eq] at hcond
        exact ⟨hbMem, sec, md, cd, hbk, hcond.1.1⟩
      · cases hopt

private theorem mem_rulesForGrammar_of_alts {cx : Ctx} {g : GrammarId}
    (hbg : baseGrammar g = none) {n : NT} {s : Src}
    (hs : s ∈ glData.alts cx g n) :
    s.rule ∈ rulesForGrammar g ∧ s.alt ∈ writtenAlts s.rule := by
  obtain ⟨horig, halt⟩ := alts_src_origin hbg hs
  refine ⟨?_, List.mem_of_getElem? halt⟩
  unfold rulesForGrammar
  rw [List.mem_append]
  rcases horig with ⟨_, hr⟩ | ⟨_, b, hb, sec, md, cd, hbk, hog, hr⟩
  · exact Or.inl hr
  · right
    rw [List.mem_flatMap]
    refine ⟨b, hb, ?_⟩
    rw [hbk]; dsimp only
    have hogB : (overlayGrammar sec == g) = true := beq_iff_eq.mpr hog
    simp only [hogB, ↓reduceIte]
    exact hr

private def semiItemIsSemicolon : Option Item → Bool
  | some (.sym (.t (.text str _)) _) => str == ";"
  | some (.butNot (.t (.text str _)) _) => str == ";"
  | _ => false

private def listNoDupBEq {α : Type} [BEq α] : List α → Bool
  | [] => true
  | x :: xs => !xs.contains x && listNoDupBEq xs

private theorem nodup_eq_of_mem {α β : Type} [BEq β] [LawfulBEq β] {f : α → β} {l : List α}
    (hnd : listNoDupBEq (l.map f) = true) {x y : α} (hx : x ∈ l) (hy : y ∈ l) (heq : f x = f y) :
    x = y := by
  induction l with
  | nil => nomatch hx
  | cons hd tl ih =>
    simp only [List.map_cons, listNoDupBEq, Bool.and_eq_true, Bool.not_eq_true', List.contains_eq_mem, decide_eq_false_iff_not] at hnd
    rcases List.mem_cons.mp hx with rfl | hxtl
    · rcases List.mem_cons.mp hy with rfl | hytl
      · rfl
      · exfalso; exact hnd.1 (heq ▸ List.mem_map_of_mem hytl)
    · rcases List.mem_cons.mp hy with rfl | hytl
      · exfalso; exact hnd.1 (heq.symm ▸ List.mem_map_of_mem hxtl)
      · exact ih hnd.2 hxtl hytl

private def semisProdsCert : Bool :=
  listNoDupBEq (glData.grammars.map Prod.fst) &&
  listNoDupBEq ((glData.rulesOf .syntactic).map (·.lhs)) &&
  (prodsOf [(.annexB, glData.rulesOf .annexB)]).all (fun p =>
    glData.semis.all fun (c', _, _) => !(c' == p.ctor)) &&
  (prodsOf [(.syntactic, glData.rulesOf .syntactic)]).all (fun p =>
    glData.semis.all fun (c', k, _) =>
      !(c' == p.ctor) || match (writtenAlts p.rule)[p.alt]? with
        | some a => semiItemIsSemicolon a.rhs[k]?
        | none => false)

set_option maxRecDepth 4000 in
private theorem semisProdsCert_true : semisProdsCert = true := by decide

private theorem term_non_semi_not_virt {cx : Ctx} {P : CodePrims} {n : NT} {s : Src}
    (hs : s ∈ Ecma.Spec.gl.alts cx .syntactic n) {k : Nat} {str : String} {b : Bool}
    (hitem : (∃ o, s.alt.rhs[k]? = some (.sym (.t (.text str b)) o)) ∨
      (∃ ex, s.alt.rhs[k]? = some (.butNot (.t (.text str b)) ex)))
    (hstr : str ≠ ";") {tok : Token}
    (ht : (tokenAlphabet Ecma.Spec.gl cx P).term s k (.text str b) [tok]) :
    tok.virt = none := by
  dsimp only [tokenAlphabet] at ht
  obtain ⟨_, hv⟩ := ht
  cases hvirt : tok.virt with
  | none => rfl
  | some why =>
    rw [hvirt] at hv
    obtain ⟨c, hctor, cls, hmemSem, _⟩ := hv
    rw [← glData_eq] at hs hctor hmemSem
    have hcert := semisProdsCert_true
    unfold semisProdsCert at hcert
    simp only [Bool.and_eq_true] at hcert
    obtain ⟨⟨⟨hndGram, hndSyn⟩, hannexOk⟩, hsynOk⟩ := hcert
    unfold GL.ctorOf at hctor
    obtain ⟨p, hfindP, rfl⟩ := Option.map_eq_some_iff.mp hctor
    have hpMemAll := List.mem_of_find?_eq_some hfindP
    have hpHit := List.find?_some hfindP
    simp only [Bool.and_eq_true, beq_iff_eq] at hpHit
    obtain ⟨⟨hpGram, hpLhs⟩, hpAlt⟩ := hpHit
    unfold prodsOf at hpMemAll
    rw [List.mem_flatMap] at hpMemAll
    obtain ⟨⟨g0, rs0⟩, hgrMem, hpInG0⟩ := hpMemAll
    have hg0Eq : g0 = p.grammar := by
      rw [List.mem_flatMap] at hpInG0
      obtain ⟨⟨⟨_, _, _⟩, _⟩, _, hm0⟩ := hpInG0
      rw [List.mem_map] at hm0
      obtain ⟨_, _, hmk⟩ := hm0
      exact congrArg Prod.grammar hmk
    subst hg0Eq
    have hrs0Eq : rs0 = glData.rulesOf p.grammar := by
      unfold GL.rulesOf
      have hlk : ∀ gs : List (GrammarId × List Rule),
          listNoDupBEq (gs.map Prod.fst) = true → (p.grammar, rs0) ∈ gs → gs.lookup p.grammar = some rs0 := by
        intro gs
        induction gs with
        | nil => intro _ hm; nomatch hm
        | cons hd tl ih =>
          rcases hd with ⟨g1, r1⟩
          intro hnd hm
          simp only [List.map_cons, listNoDupBEq, Bool.and_eq_true, Bool.not_eq_true', List.contains_eq_mem, decide_eq_false_iff_not] at hnd
          rcases List.mem_cons.mp hm with heq | htl
          · obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
            simp [List.lookup]
          · simp only [List.lookup]
            have hne : (p.grammar == g1) = false := by
              apply Bool.eq_false_iff.mpr; intro h; rw [beq_iff_eq] at h; subst h
              exact hnd.1 (List.mem_map.mpr ⟨(_, rs0), htl, rfl⟩)
            rw [hne]; exact ih hnd.2 htl
      rw [hlk glData.grammars hndGram hgrMem]; rfl
    subst hrs0Eq
    have hpInSingle : p ∈ prodsOf [(p.grammar, glData.rulesOf p.grammar)] := by
      unfold prodsOf
      simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
      exact hpInG0
    obtain ⟨horig, haltS⟩ := alts_src_origin rfl hs
    rcases horig with ⟨hsGram, hsRuleMem⟩ | ⟨hsGram, _⟩
    · rw [hsGram] at hpGram
      rw [hpGram] at hpInG0 hpInSingle
      have hpRuleMem : p.rule ∈ glData.rulesOf .syntactic := by
        rw [List.mem_flatMap] at hpInG0
        obtain ⟨⟨⟨r0, _, _⟩, _⟩, hws, hm0⟩ := hpInG0
        rw [List.mem_map] at hm0; obtain ⟨_, _, hmk⟩ := hm0
        have hrEq : r0 = p.rule := congrArg Prod.rule hmk
        subst hrEq
        have hws1 : ∃ i k, (p.rule, i, k) ∈ (glData.rulesOf .syntactic).flatMap fun r => r.written.zipIdx.map fun (k, i) => (r, i, k) := by
          have hzipMem : ∀ {α : Type} (l : List α) (off : Nat) (x : α × Nat), x ∈ l.zipIdx off → x.1 ∈ l := by
            intro α l; induction l with
            | nil => intro _ _ h; nomatch h
            | cons a tl ih =>
              intro off x hx; rcases List.mem_cons.mp hx with rfl | htl
              · exact List.mem_cons_self ..
              · exact List.mem_cons_of_mem _ (ih (off + 1) x htl)
          exact ⟨_, _, hzipMem _ 0 _ hws⟩
        obtain ⟨_, _, hfm⟩ := hws1
        rw [List.mem_flatMap] at hfm
        obtain ⟨r1, hr1Mem, hmap1⟩ := hfm
        rw [List.mem_map] at hmap1
        obtain ⟨_, _, hpairEq⟩ := hmap1
        injection hpairEq with hr1Eq _
        exact hr1Eq ▸ hr1Mem
      have hrEq : p.rule = s.rule := nodup_eq_of_mem hndSyn hpRuleMem hsRuleMem hpLhs
      have hpOk := List.all_eq_true.mp (List.all_eq_true.mp hsynOk p hpInSingle) (p.ctor, k, cls) hmemSem
      simp only [beq_self_eq_true, Bool.not_true, Bool.false_or] at hpOk
      rw [hrEq, hpAlt, haltS] at hpOk
      dsimp only at hpOk
      rcases hitem with ⟨_, hk⟩ | ⟨_, hk⟩ <;>
        (rw [hk] at hpOk; exact absurd (beq_iff_eq.mp hpOk) hstr)
    · rw [hsGram] at hpGram
      rw [hpGram] at hpInSingle
      have hpNo := List.all_eq_true.mp (List.all_eq_true.mp hannexOk p hpInSingle) (p.ctor, k, cls) hmemSem
      simp at hpNo

private def sParen : Src :=
  ⟨.syntactic, Gen.Syntactic.ParenthesizedExpression, 0,
    ⟨[], [.sym (.t (.text "(" false)) false,
          .sym (.nt .Expression [⟨.plus, .In⟩, ⟨.quest, .Yield⟩, ⟨.quest, .Await⟩]) false,
          .sym (.t (.text ")" false)) false], none⟩⟩

private def sCall : Src :=
  ⟨.syntactic, Gen.Syntactic.CallMemberExpression, 0,
    ⟨[], [.sym (.nt .MemberExpression [⟨.quest, .Yield⟩, ⟨.quest, .Await⟩]) false,
          .sym (.nt .Arguments [⟨.quest, .Yield⟩, ⟨.quest, .Await⟩]) false], none⟩⟩

private def isOpenParenItem : Item → Bool
  | .sym (.t (.text str false)) false => str == "("
  | _ => false

private def isCloseParenItem : Item → Bool
  | .sym (.t (.text str false)) false => str == ")"
  | _ => false

private def argsAltOk (s : Src) : Bool :=
  match s.alt.rhs with
  | firstItem :: rest =>
    isOpenParenItem firstItem &&
    match rest.reverse with
    | lastItem :: midRev =>
      isCloseParenItem lastItem &&
      midRev.all fun
        | .lookahead _ => false
        | _ => true
    | [] => false
  | [] => false

private instance : LawfulBEq Sign where
  rfl {a} := by cases a <;> rfl
  eq_of_beq {a b} h := by cases a <;> cases b <;> cases h <;> rfl

private instance : LawfulBEq Arg where
  rfl {a} := by
    rcases a with ⟨s, p⟩
    show (s == s && p == p) = true
    simp
  eq_of_beq {a b} h := by
    rcases a with ⟨s1, p1⟩; rcases b with ⟨s2, p2⟩
    change (s1 == s2 && p1 == p2) = true at h
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    rw [h.1, h.2]

private instance : LawfulBEq CodePointName where
  rfl {a} := by cases a <;> rfl
  eq_of_beq {a b} h := by cases a <;> cases b <;> cases h <;> rfl

private instance : LawfulBEq Terminal where
  rfl {a} := by
    cases a with
    | text s b => show (s == s && b == b) = true; simp
    | cp n => show (n == n) = true; simp
  eq_of_beq {a b} h := by
    cases a with
    | text s1 b1 =>
      cases b with
      | cp _ => cases h
      | text s2 b2 =>
        change (s1 == s2 && b1 == b2) = true at h
        simp only [Bool.and_eq_true, beq_iff_eq] at h
        rw [h.1, h.2]
    | cp n1 =>
      cases b with
      | text _ _ => cases h
      | cp n2 =>
        change (n1 == n2) = true at h
        rw [beq_iff_eq.mp h]

private instance : LawfulBEq Sym where
  rfl {a} := by
    cases a with
    | t x => show (x == x) = true; simp
    | nt n args => show (n == n && args == args) = true; simp
  eq_of_beq {a b} h := by
    cases a with
    | t x1 =>
      cases b with
      | nt _ _ => cases h
      | t x2 =>
        change (x1 == x2) = true at h
        rw [beq_iff_eq.mp h]
    | nt n1 args1 =>
      cases b with
      | t _ => cases h
      | nt n2 args2 =>
        change (n1 == n2 && args1 == args2) = true at h
        simp only [Bool.and_eq_true, beq_iff_eq] at h
        rw [h.1, h.2]

private theorem sym_false_item_beq_eq {s0 : Sym} {it : Item}
    (h : (Item.sym s0 false == it) = true) : it = .sym s0 false := by
  cases it with
  | sym s1 o1 =>
    change (s0 == s1 && (false == o1)) = true at h
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    rw [← h.1, ← h.2]
  | _ => cases h

private theorem sym_false_list_beq_eq :
    ∀ (targets : List Sym) (xs : List Item),
      ((targets.map (Item.sym · false)) == xs) = true →
      xs = targets.map (Item.sym · false)
  | [], [] => fun _ => rfl
  | [], _ :: _ => fun h => by cases h
  | _ :: _, [] => fun h => by cases h
  | s0 :: rest, it :: xs => fun h => by
    simp only [List.map_cons] at h ⊢
    change ((Item.sym s0 false == it) && ((rest.map (Item.sym · false)) == xs)) = true at h
    simp only [Bool.and_eq_true] at h
    rw [sym_false_item_beq_eq h.1, sym_false_list_beq_eq rest xs h.2]

private def coverGoalsCert : Bool :=
  (glData.rulesOf .syntactic).any (·.lhs == .ParenthesizedExpression) &&
  (glData.rulesOf .syntactic).any (·.lhs == .CallMemberExpression) &&
  (List.range 32).all fun ci =>
    let cx := cxOfIdx ci
    decide (glData.alts cx .syntactic .ParenthesizedExpression = [sParen]) &&
    decide (glData.alts cx .syntactic .CallMemberExpression = [sCall]) &&
    !(glData.alts cx .syntactic .Arguments).isEmpty &&
    (glData.alts cx .syntactic .Arguments).all argsAltOk

private theorem coverGoalsCert_true : coverGoalsCert = true := by decide

private def rhsHasRealStart (cx : Ctx) (acc : List NT) : List Item → Bool
  | [] => false
  | .lookahead _ :: tl | .noLT :: tl | .empty :: tl | .onlyIf _ :: tl => rhsHasRealStart cx acc tl
  | .sym (.t (.text str _)) o :: tl =>
    if str != ";" && str != "" then
      if o then rhsHasRealStart cx acc tl else true
    else false
  | .butNot (.t (.text str _)) _ :: _ => str != ";" && str != ""
  | .sym (.nt m _) o :: tl =>
    if (glData.alts cx .syntactic m).isEmpty || acc.contains m then
      if o then rhsHasRealStart cx acc tl else true
    else false
  | .butNot (.nt m _) _ :: _ =>
    (glData.alts cx .syntactic m).isEmpty || acc.contains m
  | _ => false

private def realStartNTs : List NT :=
  [.MemberExpression, .Arguments, .LexicalDeclaration, .PrimaryExpression, .SuperProperty,
   .MetaProperty, .LetOrConst, .UsingDeclaration, .AwaitUsingDeclaration, .IdentifierReference,
   .Literal, .ArrayLiteral, .ObjectLiteral, .FunctionExpression, .ClassExpression,
   .GeneratorExpression, .AsyncFunctionExpression, .AsyncGeneratorExpression, .TemplateLiteral,
   .CoverParenthesizedExpressionAndArrowParameterList, .NewTarget, .ImportMeta,
   .CoverAwaitExpressionAndAwaitUsingDeclarationHead, .Identifier, .SubstitutionTemplate]

private def realStartCert : Bool :=
  realStartNTs.contains .MemberExpression &&
  realStartNTs.contains .Arguments &&
  realStartNTs.contains .LexicalDeclaration &&
  realStartNTs.all fun n =>
    (List.range 32).all fun ci =>
      let cx := cxOfIdx ci
      !(glData.alts cx .syntactic n).isEmpty &&
      (glData.alts cx .syntactic n).all fun s => rhsHasRealStart cx realStartNTs s.alt.rhs

private theorem realStartCert_true : realStartCert = true := by decide

private def exprFirstSafeNTs : List NT :=
  [.ParenthesizedExpression, .CallMemberExpression, .MemberExpression, .PrimaryExpression,
   .IdentifierReference, .Identifier, .Literal, .ArrayLiteral, .ObjectLiteral,
   .FunctionExpression, .ClassExpression, .GeneratorExpression, .AsyncFunctionExpression,
   .AsyncGeneratorExpression, .TemplateLiteral, .SubstitutionTemplate,
   .CoverParenthesizedExpressionAndArrowParameterList, .SuperProperty, .MetaProperty,
   .NewTarget, .ImportMeta]

private def commonSafeLexNTs : List NT :=
  [.IdentifierName, .NullLiteral, .BooleanLiteral, .NumericLiteral, .StringLiteral,
   .NoSubstitutionTemplate, .TemplateHead]

private def rhsFirstExprSafe (cx : Ctx) : List Item → Bool
  | [] => false
  | .lookahead _ :: tl | .noLT :: tl | .empty :: tl | .onlyIf _ :: tl => rhsFirstExprSafe cx tl
  | .sym (.t (.text str _)) false :: _ =>
    match str.toList with
    | c :: _ => c != '/' && c != '}' && str != ";"
    | [] => false
  | .sym (.nt m _) false :: _ | .butNot (.nt m _) _ :: _ =>
    if (glData.alts cx .syntactic m).isEmpty then
      m == .RegularExpressionLiteral || commonSafeLexNTs.contains m
    else
      exprFirstSafeNTs.contains m
  | _ => false

private def exprFirstSafeCert : Bool :=
  exprFirstSafeNTs.all fun n =>
    (List.range 32).all fun ci =>
      let cx := cxOfIdx ci
      !(glData.alts cx .syntactic n).isEmpty &&
      (glData.alts cx .syntactic n).all fun s => rhsFirstExprSafe cx s.alt.rhs

private theorem exprFirstSafeCert_true : exprFirstSafeCert = true := by decide

set_option maxRecDepth 10000 in
private theorem idStart_not_slash_or_brace :
    Engine.Model.idStart 0x2F = false ∧ Engine.Model.idStart 0x7D = false := by
  simp only [Engine.Model.idStart, Unicode.idStart, Unicode.idStartTable, Thunk.get]
  unfold Unicode.inClassRanges
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Id.run]
  decide

private def noSlashBraceLexNTs : List NT :=
  [.IdentifierName, .NullLiteral, .BooleanLiteral, .NumericLiteral, .StringLiteral,
   .NoSubstitutionTemplate, .TemplateHead, .IdentifierStart, .DecimalLiteral,
   .DecimalBigIntegerLiteral, .NonDecimalIntegerLiteral, .LegacyOctalIntegerLiteral,
   .IdentifierStartChar, .DecimalIntegerLiteral, .NonZeroDigit, .BinaryIntegerLiteral,
   .OctalIntegerLiteral, .HexIntegerLiteral, .UnicodeIDStart, .DecimalDigit,
   .NonOctalDecimalIntegerLiteral]

private def rhsNoSlashBraceStart : List Item → Bool
  | .sym (.t (.text str _)) false :: _ | .butNot (.t (.text str _)) _ :: _ =>
    match str.toList with
    | c :: _ => c != '/' && c != '}'
    | [] => false
  | .sym (.nt m _) false :: _ | .butNot (.nt m _) _ :: _ => noSlashBraceLexNTs.contains m
  | .phrase .idStart :: _ => true
  | _ => false

private def rhsStartsChar (ch : Char) : List Item → Bool
  | .sym (.t (.text str _)) false :: _ =>
    match str.toList with
    | c :: _ => c == ch
    | [] => false
  | _ => false

private def lexFirstCharCert : Bool :=
  [cxHtmlFalse, cxHtmlTrue].all fun cx =>
    (noSlashBraceLexNTs.all fun n =>
      !(glData.alts cx .lexical n).isEmpty &&
      (glData.alts cx .lexical n).all fun s => rhsNoSlashBraceStart s.alt.rhs) &&
    ([NT.DivPunctuator, .RegularExpressionLiteral].all fun n =>
      (glData.alts cx .lexical n).all fun s => rhsStartsChar '/' s.alt.rhs) &&
    ([NT.RightBracePunctuator, .TemplateMiddle, .TemplateTail].all fun n =>
      (glData.alts cx .lexical n).all fun s => rhsStartsChar '}' s.alt.rhs)

private theorem lexFirstCharCert_true : lexFirstCharCert = true := by decide

private def lexEndsNonCloseParenNTs : List NT :=
  [.OctalDigit, .NonZeroOctalDigit, .ZeroToThree, .FourToSeven, .DecimalDigit,
   .HexDigit, .HexDigits, .CodePoint, .NotCodePoint]

private def rhsEndsNonCloseParen : List Item → Bool
  | [.sym (.t (.text str _)) false] =>
    match str.toList.getLast? with
    | some c => c != ')' && str != ""
    | none => false
  | [.sym (.nt m _) false] => lexEndsNonCloseParenNTs.contains m
  | [.butNot (.nt m _) _] => lexEndsNonCloseParenNTs.contains m
  | [.sym (.nt m _) false, .onlyIf _] => lexEndsNonCloseParenNTs.contains m
  | [.sym (.nt _ _) false, .sym (.nt m _) false] => lexEndsNonCloseParenNTs.contains m
  | [.sym (.nt _ _) false, .sym (.nt _ _) false, .sym (.nt m _) false] =>
    lexEndsNonCloseParenNTs.contains m
  | _ => false

private def oneCpTermOk : Terminal → Bool
  | .cp n => n.codePoint.isSome
  | .text str _ => str.toList.length == 1

private def lexLookKindOk : Lookahead → Bool
  | .eq [.t x] | .ne [.t x] => oneCpTermOk x
  | .mem qs | .notMem qs =>
    qs.all fun
      | [.t x] => oneCpTermOk x
      | _ => false
  | .notMemNT d => d == .DecimalDigit || d == .OctalDigit || d == .HexDigit
  | _ => false

private def lexRhsLookScan (safe : Bool) : List Item → Bool
  | [] => true
  | .lookahead lk :: tl => safe && lexLookKindOk lk && lexRhsLookScan safe tl
  | .onlyIf _ :: tl | .empty :: tl => lexRhsLookScan safe tl
  | .sym (.t (.cp .CR)) false :: tl => lexRhsLookScan true tl
  | .sym (.t (.text str _)) false :: tl =>
    let safe' := match str.toList.getLast? with
      | some c => c != ')' && str != ""
      | none => false
    lexRhsLookScan safe' tl
  | .sym (.nt m _) false :: tl =>
    lexRhsLookScan (lexEndsNonCloseParenNTs.contains m) tl
  | _ :: tl => lexRhsLookScan false tl

private def lexLookCert : Bool :=
  ([cxHtmlFalse, cxHtmlTrue].all fun cx =>
    (lexEndsNonCloseParenNTs.all fun n =>
      !(glData.alts cx .lexical n).isEmpty &&
      (glData.alts cx .lexical n).all fun s => rhsEndsNonCloseParen s.alt.rhs) &&
    ([NT.DecimalDigit, .OctalDigit, .HexDigit].all fun d =>
      (glData.alts cx .lexical d).all fun s =>
        match s.alt.rhs with
        | [.sym (.t (.text str false)) false] => str.toList.length == 1 && s.alt.guard.isEmpty
        | _ => false)) &&
  ((rulesForGrammar .lexical).all fun r => (writtenAlts r).all fun a => lexRhsLookScan false a.rhs)

private theorem lexLookCert_true : lexLookCert = true := by decide

private def synLookSeqOk : List LookItem → Bool
  | [.t (.text s1 false)] => s1 != ")" && s1 != ";" && s1 != ""
  | [.t (.text s1 false), .t (.text s2 false)] =>
    s1 != ")" && s1 != ";" && s1 != "" && s2 != ")" && s2 != ";" && s2 != ""
  | [.t (.text s1 false), .noLT, .t (.text s2 false)] =>
    s1 != ")" && s1 != ";" && s1 != "" && s2 != ")" && s2 != ";" && s2 != ""
  | _ => false

private def synLookKindOk : Lookahead → Bool
  | .ne q => synLookSeqOk q
  | .notMem qs => qs.all synLookSeqOk
  | _ => false

private def synRhsItemCert (it : Item) : Bool :=
  match it with
  | .lookahead lk => synLookKindOk lk
  | .butNot _ (.sym (.nt m args)) => m == .ReservedWord && args.isEmpty
  | .butNot _ _ => false
  | .phrase _ | .onlyIf _ => false
  | _ => true

private def synLookAndExclCert : Bool :=
  ((List.range 32).all fun ci =>
    (glData.alts (cxOfIdx ci) .syntactic .ReservedWord).isEmpty) &&
  ((rulesForGrammar .syntactic).all fun r =>
    (writtenAlts r).all fun a => a.rhs.all synRhsItemCert)

set_option maxRecDepth 2000 in
private theorem synLookAndExclCert_true : synLookAndExclCert = true := by decide

/-! ## Section 2: `NoCoverSub` for Code-Point Grammars and `.lex` Nodes -/

def NoCoverSub (nd : Node) : Prop :=
  ∀ x, (x = nd ∨ x ∈ seqList (Impl.nodeDescendants nd)) →
    isCoverNtIdx (Impl.nodeNt x) = false

theorem noCoverSub_of_kid {nd c : Node} (h : NoCoverSub nd) (hc : c ∈ (kidsOf nd).toList) :
    NoCoverSub c := by
  unfold NoCoverSub
  intro x hx
  exact h x (Or.inr ((mem_descendants nd x).mpr ⟨c, hc, hx⟩))

theorem noCoverSub_of_desc {nd d : Node} (h : NoCoverSub nd)
    (hd : d ∈ seqList (Impl.nodeDescendants nd)) :
    NoCoverSub d := by
  have hgen : ∀ (f : Nat) (m : Node), m.height ≤ f → NoCoverSub m →
      ∀ d ∈ seqList (Impl.nodeDescendants m), NoCoverSub d := by
    intro f
    induction f with
    | zero => intro m hf; obtain ⟨g, hg⟩ := height_pos m; omega
    | succ f ih =>
      intro m hf hm d hdMem
      obtain ⟨c, hc, hdc⟩ := (mem_descendants m d).mp hdMem
      have hcSub := noCoverSub_of_kid hm hc
      rcases hdc with rfl | hdC
      · exact hcSub
      · exact ih c (by have := height_kid hc; omega) hcSub d hdC
  exact hgen nd.height nd (Nat.le_refl _) h d hd

private theorem treeSize_mem_le {c : Tree} :
    ∀ {kids : List Tree}, c ∈ kids → treeSize c ≤ treeSize.treeListSize kids
  | [], h => nomatch h
  | k :: ks, h => by
    dsimp only [treeSize.treeListSize]
    rcases List.mem_cons.mp h with rfl | hm
    · omega
    · have := treeSize_mem_le hm; omega

private theorem code_step_no_cover {cx : Ctx} {P : CodePrims} {g : GrammarId}
    (hg : g ∈ codeGrammars) {neg : NT → List Param → Nat → Nat → Prop} {inp : List Nat} :
    ∀ (sz : Nat),
      (∀ {m ps i j t}, treeSize t ≤ sz →
        Step (codeAlphabet P) neg inp Ecma.Spec.gl cx g m ps i j t →
        ∀ {st0 : Nat} {text : List Nat} {span : Nat → Nat → Nat × Nat} {nd : Node},
          Ecma.Model.NodeRel Impl st0 text span nd t → NoCoverSub nd) ∧
      (∀ {s ps k is i j mask ts}, treeSize.treeListSize ts ≤ sz →
        Ecma.Grammar.Seq (codeAlphabet P) neg inp Ecma.Spec.gl cx g s ps k is i j mask ts →
        ∀ c ∈ ts.filter (fun x => !x.isLeaf),
          ∃ m' ps' a b, Step (codeAlphabet P) neg inp Ecma.Spec.gl cx g m' ps' a b c) := by
  intro sz
  induction sz using Nat.strongRecOn with
  | ind sz ih =>
    have hseqL : ∀ {s ps k is i j mask ts}, treeSize.treeListSize ts ≤ sz →
        Ecma.Grammar.Seq (codeAlphabet P) neg inp Ecma.Spec.gl cx g s ps k is i j mask ts →
        ∀ c ∈ ts.filter (fun x => !x.isLeaf),
          ∃ m' ps' a b, Step (codeAlphabet P) neg inp Ecma.Spec.gl cx g m' ps' a b c := by
      intro s ps k is
      induction is generalizing k with
      | nil => intro _ _ _ _ _ hs c hc; cases hs; simp at hc
      | cons _ _ ihr =>
        intro i j mask ts hsz hs c hc
        cases hs with
        | absent hr | look _ hr | noLT _ hr | empty hr | onlyIf hr => exact ihr hsz hr c hc
        | term _ hr | butNotT _ _ hr | phrase _ hr =>
          dsimp only [treeSize.treeListSize, treeSize] at hsz
          simp only [List.filter_cons, Tree.isLeaf, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hc
          exact ihr (by omega) hr c hc
        | @nt _ _ _ m0 args0 _ _ _ h _ _ t0 _ hs0 _ hr =>
          dsimp only [treeSize.treeListSize] at hsz
          rw [List.filter_cons] at hc
          by_cases hnl : (!t0.isLeaf) = true
          · simp only [hnl, ↓reduceIte, List.mem_cons] at hc
            rcases hc with rfl | hrest
            · exact ⟨m0, applyArgs ps args0, i, h, hs0⟩
            · exact ihr (by omega) hr c hrest
          · simp only [hnl, Bool.false_eq_true, ↓reduceIte] at hc
            exact ihr (by omega) hr c hc
        | @butNotN _ _ _ m0 args0 _ _ _ h _ _ t0 _ hs0 _ hr =>
          dsimp only [treeSize.treeListSize] at hsz
          rw [List.filter_cons] at hc
          by_cases hnl : (!t0.isLeaf) = true
          · simp only [hnl, ↓reduceIte, List.mem_cons] at hc
            rcases hc with rfl | hrest
            · exact ⟨m0, applyArgs ps args0, i, h, hs0⟩
            · exact ihr (by omega) hr c hrest
          · simp only [hnl, Bool.false_eq_true, ↓reduceIte] at hc
            exact ihr (by omega) hr c hc
    refine ⟨?_, hseqL⟩
    intro m ps i j t hsz hst st0 text span nd hrel
    cases hst with
    | lex _ _ hleaf => nomatch hleaf
    | @node _ _ _ _ _ kids id s hsMem _ _ hseq =>
      dsimp only [treeSize] at hsz
      have hrootF : isCoverNtIdx m.ctorIdx = false := by
        cases hc : isCoverNtIdx m.ctorIdx with
        | false => rfl
        | true =>
          have hnil := code_alts_cover_empty (cx := cx) hg hc
          rw [hnil] at hsMem; nomatch hsMem
      obtain ⟨hnt, _, _, _, _, _, _, _, hkget, hkids⟩ := nodeRel_node_inv hrel
      unfold NoCoverSub
      intro x hx
      rcases hx with rfl | hdesc
      · rwa [hnt]
      · obtain ⟨cNd, hcMem, hxc⟩ := (mem_descendants nd x).mp hdesc
        rw [← nodeKids_eq] at hcMem
        obtain ⟨idx, hidxLt, rfl⟩ := List.getElem_of_mem hcMem
        have hidxSz : idx < (Impl.nodeKids nd).size := by rwa [← Array.length_toList]
        have hgetC : Impl.seqGet (Impl.nodeKids nd) (Impl.ofNat idx) = some (Impl.nodeKids nd)[idx] := by
          rw [impl_seqGet_nat, Array.getElem?_eq_getElem hidxSz]
        have hsomeC : (Impl.seqGet (Impl.nodeKids nd) (Impl.ofNat idx)).isSome = true := by
          rw [hgetC]; rfl
        have hidxT : idx < (kids.filter (fun y => !y.isLeaf)).length := by
          have hk0 := (hkget idx).symm
          rw [hsomeC, decide_eq_true_iff] at hk0
          exact hk0
        let tc := (kids.filter (fun y => !y.isLeaf))[idx]'hidxT
        have hrelC := hkids idx tc _ (List.getElem?_eq_getElem hidxT) hgetC
        have htcMem : tc ∈ kids.filter (fun y => !y.isLeaf) := List.getElem_mem hidxT
        obtain ⟨mC, psC, aC, bC, hstC⟩ := (ih _ (by omega)).2 (Nat.le_refl _) hseq tc htcMem
        have hszC := treeSize_mem_le (List.mem_filter.mp htcMem).1
        exact (ih (treeSize tc) (by omega)).1 (Nat.le_refl _) hstC hrelC x hxc

theorem noCoverSub_of_code_derives {cx : Ctx} {P : CodePrims} {g : GrammarId}
    (hg : g ∈ codeGrammars) {inp : List Nat} {m : NT} {ps : List Param} {i j : Nat} {t : Tree}
    (hd : Derives Ecma.Spec.gl cx g (codeAlphabet P) inp m ps i j t)
    {st0 : Nat} {text : List Nat} {span : Nat → Nat → Nat × Nat} {nd : Node}
    (hrel : Ecma.Model.NodeRel Impl st0 text span nd t) :
    NoCoverSub nd := by
  obtain ⟨K, hK⟩ := hd
  have hs := hK (max K 1) (Nat.le_max_left K 1)
  obtain ⟨k0, hk0⟩ : ∃ k0, max K 1 = k0 + 1 := ⟨max K 1 - 1, by omega⟩
  rw [hk0] at hs
  exact (code_step_no_cover hg (treeSize t)).1 (Nat.le_refl _) hs hrel

/-! ## Section 3: Lexical Slice Bijection on `[lo, hi]` Ending in `')'` (`0x29`) -/

def shiftCodeTree (lo : Nat) : Tree → Tree
  | .leaf a b => .leaf (a - lo) (b - lo)
  | .lex k t => .lex k (shiftCodeTree lo t)
  | .node n id ps a b ks => .node n id ps (a - lo) (b - lo) (ks.map (shiftCodeTree lo))

def unshiftCodeTree (lo : Nat) : Tree → Tree
  | .leaf a b => .leaf (lo + a) (lo + b)
  | .lex k t => .lex k (unshiftCodeTree lo t)
  | .node n id ps a b ks => .node n id ps (lo + a) (lo + b) (ks.map (unshiftCodeTree lo))

@[simp] private theorem shiftCodeTree_leaf (lo a b : Nat) :
    shiftCodeTree lo (.leaf a b) = .leaf (a - lo) (b - lo) := by rw [shiftCodeTree]
@[simp] private theorem shiftCodeTree_lex (lo k : Nat) (t : Tree) :
    shiftCodeTree lo (.lex k t) = .lex k (shiftCodeTree lo t) := by rw [shiftCodeTree]
@[simp] private theorem shiftCodeTree_node (lo : Nat) (n : NT) (id : Nat) (ps : List Param) (a b : Nat) (ks : List Tree) :
    shiftCodeTree lo (.node n id ps a b ks) = .node n id ps (a - lo) (b - lo) (ks.map (shiftCodeTree lo)) := by rw [shiftCodeTree]

@[simp] private theorem unshiftCodeTree_leaf (lo a b : Nat) :
    unshiftCodeTree lo (.leaf a b) = .leaf (lo + a) (lo + b) := by rw [unshiftCodeTree]
@[simp] private theorem unshiftCodeTree_lex (lo k : Nat) (t : Tree) :
    unshiftCodeTree lo (.lex k t) = .lex k (unshiftCodeTree lo t) := by rw [unshiftCodeTree]
@[simp] private theorem unshiftCodeTree_node (lo : Nat) (n : NT) (id : Nat) (ps : List Param) (a b : Nat) (ks : List Tree) :
    unshiftCodeTree lo (.node n id ps a b ks) = .node n id ps (lo + a) (lo + b) (ks.map (unshiftCodeTree lo)) := by rw [unshiftCodeTree]

private theorem shiftCodeTree_nt? (lo : Nat) : ∀ t : Tree, (shiftCodeTree lo t).nt? = t.nt?
  | .leaf _ _ => by rw [shiftCodeTree_leaf]; rfl
  | .lex _ t => by rw [shiftCodeTree_lex]; exact shiftCodeTree_nt? lo t
  | .node _ _ _ _ _ _ => by rw [shiftCodeTree_node]; rfl

private theorem slice_of_slice {α : Type} (xs : List α) {lo hi a b : Nat}
    (ha : lo ≤ a) (hb : b ≤ hi) :
    slice (slice xs lo hi) (a - lo) (b - lo) = slice xs a b := by
  by_cases hab : a ≤ b
  · unfold slice
    rw [List.drop_take, List.drop_drop, List.take_take]
    have h1 : lo + (a - lo) = a := by omega
    have h2 : min (b - lo - (a - lo)) (hi - lo - (a - lo)) = b - a := by omega
    rw [h1, h2]
  · unfold slice
    have h1 : b - lo - (a - lo) = 0 := by omega
    have h2 : b - a = 0 := by omega
    rw [h1, h2, List.take_zero, List.take_zero]

private theorem slice_unshift {α : Type} (xs : List α) {lo hi a' b' : Nat}
    (hb : b' ≤ hi - lo) :
    slice xs (lo + a') (lo + b') = slice (slice xs lo hi) a' b' := by
  by_cases hab : a' ≤ b'
  · by_cases hlh : lo ≤ hi
    · have h := slice_of_slice xs (lo := lo) (hi := hi) (a := lo + a') (b := lo + b') (by omega) (by omega)
      simpa only [Nat.add_sub_cancel_left] using h.symm
    · have hb0 : b' = 0 := by omega
      have ha0 : a' = 0 := by omega
      subst ha0; subst hb0
      unfold slice
      simp
  · unfold slice
    have h1 : lo + b' - (lo + a') = 0 := by omega
    have h2 : b' - a' = 0 := by omega
    rw [h1, h2, List.take_zero, List.take_zero]

private theorem slice_length_eq {α : Type} (xs : List α) {lo hi : Nat}
    (hlh : lo ≤ hi) (hhi : hi ≤ xs.length) :
    (slice xs lo hi).length = hi - lo := by
  unfold slice; simp; omega

private theorem slice_getElem? {α : Type} (xs : List α) {lo hi k : Nat}
    (hk : k < hi - lo) :
    (slice xs lo hi)[k]? = xs[lo + k]? := by
  unfold slice
  rw [List.getElem?_take_of_lt hk, List.getElem?_drop]

private theorem slice_nonempty_imp_lt {α : Type} {xs : List α} {a b : Nat}
    (hne : slice xs a b ≠ []) : a < b ∧ a < xs.length := by
  by_cases h1 : b ≤ a
  · exfalso; apply hne; unfold slice; rw [Nat.sub_eq_zero_of_le h1]; simp
  · by_cases h2 : xs.length ≤ a
    · exfalso; apply hne; unfold slice; rw [List.drop_eq_nil_of_le h2]; simp
    · exact ⟨by omega, by omega⟩

private theorem code_term_nonempty {P : CodePrims} {s : Src} {k : Nat} {x : Terminal} {w : List Nat}
    (h1 : termNonEmpty x = true)
    (ht : (codeAlphabet P).term s k x w) : w ≠ [] := by
  dsimp only [codeAlphabet] at ht
  cases x with
  | text str _ =>
    dsimp only [termNonEmpty] at h1 ht
    rw [ht]
    intro hnil
    have hnilL : str.toList = [] := by cases h : str.toList <;> simp [h] at hnil ⊢
    have hemp : str.isEmpty = true := by
      rw [String.isEmpty_iff]; exact String.ext_iff.mpr hnilL
    rw [hemp] at h1; cases h1
  | cp cn =>
    dsimp only at ht
    cases hcp : cn.codePoint with
    | some v => rw [hcp] at ht; rw [ht]; exact List.cons_ne_nil _ _
    | none => rw [hcp] at ht; obtain ⟨c, rfl, _⟩ := ht; exact List.cons_ne_nil _ _

private theorem code_step_bounds (hok : parseTablesOk = true) {cx : Ctx} {P : CodePrims} {g : GrammarId}
    {neg : NT → List Param → Nat → Nat → Prop} {inp : List Nat} :
    ∀ (sz : Nat),
      (∀ {m ps a b t}, treeSize t ≤ sz →
        Step (codeAlphabet P) neg inp Ecma.Spec.gl cx g m ps a b t →
        a ≤ b ∧ t.span = (a, b) ∧ (∀ idx sub, t ≠ .lex idx sub)) ∧
      (∀ {s ps k is a b mask ts}, treeSize.treeListSize ts ≤ sz →
        (∀ it ∈ is, itemTermNonEmpty it = true) →
        Ecma.Grammar.Seq (codeAlphabet P) neg inp Ecma.Spec.gl cx g s ps k is a b mask ts →
        a ≤ b) := by
  intro sz
  induction sz using Nat.strongRecOn with
  | ind sz ih =>
    have hst : ∀ {m ps a b t}, treeSize t ≤ sz →
        Step (codeAlphabet P) neg inp Ecma.Spec.gl cx g m ps a b t →
        a ≤ b ∧ t.span = (a, b) ∧ (∀ idx sub, t ≠ .lex idx sub) := by
      intro m ps a b t hsz hs
      cases hs with
      | lex _ _ hl => nomatch hl
      | node s hsMem _ _ hseq =>
        dsimp only [treeSize] at hsz
        exact ⟨(ih _ (by omega)).2 (Nat.le_refl _)
          (fun it hit => item_term_nonempty_of_alts hok hsMem hit) hseq, rfl, fun _ _ h => by cases h⟩
    refine ⟨hst, ?_⟩
    intro s ps k is
    induction is generalizing k with
    | nil => intro _ _ _ _ _ _ hs; cases hs; exact Nat.le_refl _
    | cons y ys ihr =>
      intro a b mask ts hsz hne hs
      have hneY := hne y (List.mem_cons_self ..)
      have hneYs : ∀ it ∈ ys, itemTermNonEmpty it = true :=
        fun it hit => hne it (List.mem_cons_of_mem _ hit)
      cases hs with
      | absent hr | look _ hr | noLT _ hr | empty hr | onlyIf hr => exact ihr hsz hneYs hr
      | @term _ _ _ x _ _ _ h _ _ _ ht hr =>
        dsimp only [treeSize.treeListSize, treeSize] at hsz
        have hlt := (slice_nonempty_imp_lt (code_term_nonempty (itemTermNonEmpty_sym hneY) ht)).1
        exact Nat.le_trans (Nat.le_of_lt hlt) (ihr (by omega) hneYs hr)
      | @butNotT _ _ _ x _ _ _ h _ _ _ ht _ hr =>
        dsimp only [treeSize.treeListSize, treeSize] at hsz
        have hlt := (slice_nonempty_imp_lt (code_term_nonempty (itemTermNonEmpty_butNot hneY) ht)).1
        exact Nat.le_trans (Nat.le_of_lt hlt) (ihr (by omega) hneYs hr)
      | @phrase _ _ _ _ _ _ h _ _ _ hp hr =>
        dsimp only [treeSize.treeListSize, treeSize] at hsz
        obtain ⟨_, hw, _⟩ := hp
        have hlt := (slice_nonempty_imp_lt (by rw [hw]; exact List.cons_ne_nil _ _)).1
        exact Nat.le_trans (Nat.le_of_lt hlt) (ihr (by omega) hneYs hr)
      | nt hs0 _ hr | butNotN hs0 _ hr =>
        dsimp only [treeSize.treeListSize] at hsz
        exact Nat.le_trans ((hst (by omega) hs0).1) (ihr (by omega) hneYs hr)

private theorem slice_last_eq_getElem? {inp : List Nat} {a b : Nat}
    (hb : b ≤ inp.length) {xs : List Nat} {c : Nat}
    (hsc : slice inp a b = xs ++ [c]) :
    a < b ∧ inp[b - 1]? = some c := by
  have hne : slice inp a b ≠ [] := by rw [hsc]; simp
  obtain ⟨hlt, _⟩ := slice_nonempty_imp_lt hne
  have hlen : (slice inp a b).length = b - a := slice_length_eq inp (Nat.le_of_lt hlt) hb
  have hlen2 : (xs ++ [c]).length = xs.length + 1 := by simp
  have hba : xs.length = b - a - 1 := by rw [hsc, hlen2] at hlen; omega
  have hget := slice_getElem? inp (lo := a) (hi := b) (k := xs.length) (by omega)
  rw [hsc, List.getElem?_append_right (Nat.le_refl _), Nat.sub_self] at hget
  simp only [List.getElem?_cons_zero] at hget
  have hidx : a + xs.length = b - 1 := by omega
  rw [hidx] at hget
  exact ⟨hlt, hget.symm⟩

private theorem char_toNat_ne_close_paren {ch : Char} (hne : ch ≠ ')') :
    ch.toNat ≠ 0x29 := by
  intro heq
  exact hne (char_eq_of_toNat_eq (c := ch) (d := ')') heq)

private theorem lexCertCx_mem (cx : Ctx) :
    (if Lex.html cx then cxHtmlTrue else cxHtmlFalse) ∈ [cxHtmlFalse, cxHtmlTrue] := by
  cases Lex.html cx <;> simp

private theorem lex_ends_non_close_paren (hok : parseTablesOk = true) {cx : Ctx} {P : CodePrims}
    {neg : NT → List Param → Nat → Nat → Prop} {inp : List Nat} :
    ∀ (sz : Nat) {m : NT} {ps : List Param} {a b : Nat} {t : Tree},
      treeSize t ≤ sz →
      b ≤ inp.length →
      lexEndsNonCloseParenNTs.contains m = true →
      Step (codeAlphabet P) neg inp Ecma.Spec.gl cx .lexical m ps a b t →
      a < b ∧ inp[b - 1]? ≠ some 0x29 := by
  intro sz
  induction sz using Nat.strongRecOn with
  | ind sz ih =>
    intro m ps a b t hsz hb hm hs
    have hcx2 := List.all_eq_true.mp (Bool.and_eq_true_iff.mp lexLookCert_true).1
      (if Lex.html cx then cxHtmlTrue else cxHtmlFalse) (lexCertCx_mem cx)
    have hcert1 := (Bool.and_eq_true_iff.mp hcx2).1
    have hmOk := List.all_eq_true.mp hcert1 m (List.contains_iff_mem.mp hm)
    simp only [Bool.and_eq_true] at hmOk
    cases hs with
    | lex _ _ hl => nomatch hl
    | node s hsMem _ _ hseq =>
      dsimp only [treeSize] at hsz
      have hsG := hsMem; rw [alts_lexical_eq cx m] at hsG
      have hsOk := List.all_eq_true.mp hmOk.2 s hsG
      unfold rhsEndsNonCloseParen at hsOk
      generalize hrhs : s.alt.rhs = rhs0 at hsOk hseq
      cases rhs0 with
      | nil => simp at hsOk
      | cons i1 r1 =>
        cases r1 with
        | nil =>
          cases i1 with
          | sym sym1 o1 =>
            cases o1 with
            | true => cases sym1 <;> simp at hsOk
            | false =>
              cases sym1 with
              | t tx1 =>
                cases tx1 with
                | cp _ => simp at hsOk
                | text str b0 =>
                  dsimp only at hsOk
                  cases hlast : str.toList.getLast? with
                  | none => rw [hlast] at hsOk; cases hsOk
                  | some ch =>
                    rw [hlast] at hsOk
                    simp only [Bool.and_eq_true, bne_iff_ne] at hsOk
                    cases hseq with
                    | term ht hnil =>
                      cases hnil
                      have hneL : str.toList ≠ [] := fun h0 => by simp [h0] at hlast
                      have hgetL : str.toList.getLast hneL = ch := by
                        rw [List.getLast?_eq_some_getLast hneL] at hlast
                        exact Option.some.inj hlast
                      have hcat : str.toList = str.toList.dropLast ++ [ch] := by
                        rw [← hgetL]; exact (List.dropLast_concat_getLast hneL).symm
                      have hmap : slice inp a b = str.toList.dropLast.map Char.toNat ++ [ch.toNat] := by
                        dsimp only [codeAlphabet] at ht
                        have hcatMap := congrArg (List.map Char.toNat) hcat
                        simp only [List.map_append, List.map_cons, List.map_nil] at hcatMap
                        exact ht.trans hcatMap
                      obtain ⟨hlt, hget⟩ := slice_last_eq_getElem? hb hmap
                      refine ⟨hlt, ?_⟩
                      rw [hget]; intro heq; exact char_toNat_ne_close_paren hsOk.1 (Option.some.inj heq)
              | nt m1 args1 =>
                dsimp only at hsOk
                cases hseq with
                | @nt _ _ _ _ _ _ _ _ _ _ _ t1 _ hs1 _ hnil =>
                  cases hnil
                  dsimp only [treeSize.treeListSize] at hsz
                  exact ih (treeSize t1) (by omega) (Nat.le_refl _) hb hsOk hs1
          | butNot sym1 ex1 =>
            cases sym1 with
            | t _ => simp at hsOk
            | nt m1 args1 =>
              dsimp only at hsOk
              cases hseq with
              | @butNotN _ _ _ _ _ _ _ _ _ _ _ t1 _ hs1 _ hnil =>
                cases hnil
                dsimp only [treeSize.treeListSize] at hsz
                exact ih (treeSize t1) (by omega) (Nat.le_refl _) hb hsOk hs1
          | _ => simp at hsOk
        | cons i2 r2 =>
          cases r2 with
          | nil =>
            cases i1 with
            | sym sym1 o1 =>
              cases o1 with
              | true => cases sym1 <;> cases i2 <;> simp at hsOk
              | false =>
                cases sym1 with
                | t _ => cases i2 <;> simp at hsOk
                | nt m1 args1 =>
                  cases i2 with
                  | onlyIf ph =>
                    dsimp only at hsOk
                    cases hseq with
                    | @nt _ _ _ _ _ _ _ _ _ _ _ t1 _ hs1 _ hr1 =>
                      cases hr1 with
                      | onlyIf hnil =>
                        cases hnil
                        dsimp only [treeSize.treeListSize] at hsz
                        exact ih (treeSize t1) (by omega) (Nat.le_refl _) hb hsOk hs1
                  | sym sym2 o2 =>
                    cases o2 with
                    | true => cases sym2 <;> simp at hsOk
                    | false =>
                      cases sym2 with
                      | t _ => simp at hsOk
                      | nt m2 args2 =>
                        dsimp only at hsOk
                        cases hseq with
                        | @nt _ _ _ _ _ _ _ _ _ _ _ t1 _ hs1 _ hr1 =>
                          cases hr1 with
                          | @nt _ _ _ _ _ _ _ _ _ _ _ t2 _ hs2 _ hnil =>
                            cases hnil
                            dsimp only [treeSize.treeListSize] at hsz
                            have hle1 := (code_step_bounds hok (treeSize t1)).1 (Nat.le_refl _) hs1 |>.1
                            obtain ⟨hlt2, hne2⟩ := ih (treeSize t2) (by omega) (Nat.le_refl _) hb hsOk hs2
                            exact ⟨by omega, hne2⟩
                  | _ => simp at hsOk
            | _ => simp at hsOk
          | cons i3 r3 =>
            cases r3 with
            | cons _ _ =>
              cases i1 with
              | sym s1 o1 =>
                cases s1 <;> cases o1 <;> cases i2 <;> simp at hsOk
              | _ => simp at hsOk
            | nil =>
              cases i1 with
              | sym s1 o1 =>
                cases o1 with
                | true => cases s1 <;> simp at hsOk
                | false =>
                  cases s1 with
                  | t _ => simp at hsOk
                  | nt _ _ =>
                    cases i2 with
                    | sym s2 o2 =>
                      cases o2 with
                      | true => cases s2 <;> simp at hsOk
                      | false =>
                        cases s2 with
                        | t _ => simp at hsOk
                        | nt _ _ =>
                          cases i3 with
                          | sym s3 o3 =>
                            cases o3 with
                            | true => cases s3 <;> simp at hsOk
                            | false =>
                              cases s3 with
                              | t _ => simp at hsOk
                              | nt m3 _ =>
                                dsimp only at hsOk
                                cases hseq with
                                | @nt _ _ _ _ _ _ _ _ _ _ _ t1 _ hs1 _ hr1 =>
                                  cases hr1 with
                                  | @nt _ _ _ _ _ _ _ _ _ _ _ t2 _ hs2 _ hr2 =>
                                    cases hr2 with
                                    | @nt _ _ _ _ _ _ _ _ _ _ _ t3 _ hs3 _ hnil =>
                                      cases hnil
                                      dsimp only [treeSize.treeListSize] at hsz
                                      have hle1 := (code_step_bounds hok (treeSize t1)).1 (Nat.le_refl _) hs1 |>.1
                                      have hle2 := (code_step_bounds hok (treeSize t2)).1 (Nat.le_refl _) hs2 |>.1
                                      obtain ⟨hlt3, hne3⟩ := ih (treeSize t3) (by omega) (Nat.le_refl _) hb hsOk hs3
                                      exact ⟨by omega, hne3⟩
                          | _ => simp at hsOk
                    | _ => simp at hsOk
              | _ => simp at hsOk

private theorem oneCpTerm_iff {P : CodePrims} {s : Src} {x : Terminal}
    (hokX : oneCpTermOk x = true) {inp : List Nat} {pos : Nat} (hpos : pos < inp.length) :
    StartsWith (codeAlphabet P) inp s [.t x] pos ↔
      ∃ c, inp[pos]? = some c ∧ (codeAlphabet P).term s 0 x [c] := by
  dsimp only [StartsWith, codeAlphabet]
  unfold oneCpTermOk at hokX
  constructor
  · rintro ⟨h, hlt, hhLe, ht, _⟩
    have hwLen : (slice inp pos h).length = 1 := by
      cases x with
      | text str _ => dsimp only at ht hokX; rw [ht, List.length_map]; exact beq_iff_eq.mp hokX
      | cp cn =>
        dsimp only at ht hokX
        cases hcp : cn.codePoint with
        | none => rw [hcp] at hokX; cases hokX
        | some v => rw [hcp] at ht; rw [ht]; rfl
    have hslLen := slice_length_eq inp (Nat.le_of_lt hlt) hhLe
    have hhEq : h = pos + 1 := by omega
    subst hhEq
    have hget := slice_getElem? inp (lo := pos) (hi := pos + 1) (k := 0) (by omega)
    simp only [Nat.add_zero] at hget
    cases hsc : slice inp pos (pos + 1) with
    | nil => rw [hsc] at hwLen; cases hwLen
    | cons c tl =>
      rw [hsc] at hwLen hget ht
      have htl : tl = [] := by cases tl <;> simp at hwLen ⊢
      subst htl
      exact ⟨c, hget.symm, ht⟩
  · rintro ⟨c, hget, ht⟩
    refine ⟨pos + 1, by omega, by omega, ?_, trivial⟩
    have hsc : slice inp pos (pos + 1) = [c] := by
      apply List.ext_getElem
      · rw [slice_length_eq inp (by omega) (by omega)]; simp
      · intro idx h1 h2
        have hg := slice_getElem? inp (lo := pos) (hi := pos + 1) (k := idx) (by
          rw [slice_length_eq inp (by omega) (by omega)] at h1; exact h1)
        have hidx0 : idx = 0 := by simp at h2; omega
        subst hidx0; simp only [Nat.add_zero] at hg; rw [hget] at hg
        simp only [List.getElem?_eq_getElem h1] at hg
        exact Option.some.inj hg
    rwa [hsc]

private theorem digit_derivesAt_succ_iff (hok : parseTablesOk = true) {cx : Ctx} {P : CodePrims}
    {d : NT} (hd : (d == .DecimalDigit || d == .OctalDigit || d == .HexDigit) = true)
    {inp : List Nat} {pos : Nat} (hpos : pos < inp.length) (k0 : Nat) :
    (∃ h t0, DerivesAt Ecma.Spec.gl cx .lexical (codeAlphabet P) inp (k0 + 1) d [] pos h t0) ↔
      ∃ s ∈ Ecma.Spec.gl.alts cx .lexical d, ∃ str ch,
        s.alt.rhs = [.sym (.t (.text str false)) false] ∧
        str.toList = [ch] ∧
        inp[pos]? = some ch.toNat := by
  have hcx2 := List.all_eq_true.mp (Bool.and_eq_true_iff.mp lexLookCert_true).1
    (if Lex.html cx then cxHtmlTrue else cxHtmlFalse) (lexCertCx_mem cx)
  have hcert2 := (Bool.and_eq_true_iff.mp hcx2).2
  have hdMem : d ∈ [NT.DecimalDigit, .OctalDigit, .HexDigit] := by
    simp only [Bool.or_eq_true, beq_iff_eq] at hd
    rcases hd with (rfl | rfl) | rfl <;> decide
  have hdAlts := List.all_eq_true.mp hcert2 d hdMem
  constructor
  · rintro ⟨h, t0, hst⟩
    dsimp only [DerivesAt] at hst
    cases hst with
    | lex _ _ hl => nomatch hl
    | node s hsMem _ _ hseq =>
      have hsM' := hsMem; rw [alts_lexical_eq cx d] at hsM'
      have hsOk := List.all_eq_true.mp hdAlts s hsM'
      generalize hrhs : s.alt.rhs = rhs0 at hsOk hseq
      cases rhs0 with
      | nil => simp at hsOk
      | cons i1 r1 =>
        cases r1 with
        | cons _ _ =>
          cases i1 with
          | sym s1 o1 => cases s1 <;> cases o1 <;> (try rename_i tx _; cases tx <;> rename_i b0; try cases b0) <;> simp at hsOk
          | _ => simp at hsOk
        | nil =>
          cases i1 with
          | sym s1 o1 =>
            cases o1 with
            | true => cases s1 <;> simp at hsOk
            | false =>
              cases s1 with
              | nt _ _ => simp at hsOk
              | t tx1 =>
                cases tx1 with
                | cp _ => simp at hsOk
                | text str b0 =>
                  cases b0 with
                  | true => simp at hsOk
                  | false =>
                    dsimp only at hsOk
                    simp only [Bool.and_eq_true, beq_iff_eq] at hsOk
                    cases hstrL : str.toList with
                    | nil => rw [hstrL] at hsOk; cases hsOk.1
                    | cons ch tl =>
                      rw [hstrL] at hsOk
                      have htl : tl = [] := by cases tl <;> simp at hsOk ⊢
                      subst htl
                      cases hseq with
                      | term ht hnil =>
                        cases hnil
                        dsimp only [codeAlphabet] at ht
                        rw [hstrL] at ht
                        have hne : slice inp pos h ≠ [] := by rw [ht]; exact List.cons_ne_nil _ _
                        have hlt := (slice_nonempty_imp_lt hne).1
                        have hg := slice_getElem? inp (lo := pos) (hi := h) (k := 0) (by omega)
                        simp only [Nat.add_zero] at hg
                        rw [ht] at hg
                        exact ⟨s, hsMem, str, ch, hrhs, hstrL, hg.symm⟩
          | _ => simp at hsOk
  · rintro ⟨s, hsMem, str, ch, hrhs, hstrL, hget⟩
    have hsM' := hsMem; rw [alts_lexical_eq cx d] at hsM'
    have hsOk := List.all_eq_true.mp hdAlts s hsM'
    rw [hrhs] at hsOk
    simp only [Bool.and_eq_true, List.isEmpty_iff] at hsOk
    obtain ⟨_, hopts⟩ := alt_lhs_and_opts hok hsMem
    have hopts0 : s.alt.opts = 0 := by rw [hopts, hrhs]; rfl
    have hm0 : ([] : List Bool) ∈ masks s.alt.opts := by rw [hopts0]; simp [masks]
    obtain ⟨_, id0, _, hpid, _⟩ := prodIdOf_spec hok hsMem hm0
    have hsc : slice inp pos (pos + 1) = [ch.toNat] := by
      apply List.ext_getElem
      · rw [slice_length_eq inp (by omega) (by omega)]; simp
      · intro idx h1 h2
        have hg := slice_getElem? inp (lo := pos) (hi := pos + 1) (k := idx) (by
          rw [slice_length_eq inp (by omega) (by omega)] at h1; exact h1)
        have hidx0 : idx = 0 := by simp at h2; omega
        subst hidx0; simp only [Nat.add_zero] at hg; rw [hget] at hg
        simp only [List.getElem?_eq_getElem h1] at hg
        exact Option.some.inj hg
    refine ⟨pos + 1, .node d id0 [] pos (pos + 1) [.leaf pos (pos + 1)], ?_⟩
    dsimp only [DerivesAt]
    refine .node s hsMem (by rw [hsOk.2]; rfl) hpid ?_
    rw [hrhs]
    refine .term ?_ .nil
    dsimp only [codeAlphabet]
    rw [hsc, hstrL]; rfl

private theorem lex_lookOk_slice_iff (hok : parseTablesOk = true) {cx : Ctx}
    {fullSrc : List Nat} {lo hi : Nat} (_hlh : lo < hi) (hhi : hi ≤ fullSrc.length)
    {s : Src} {lk : Lookahead} (hlkOk : lexLookKindOk lk = true)
    {pos : Nat} (hlo : lo ≤ pos) (hltHi : pos < hi) (k : Nat) :
    LookOk (codeAlphabet Engine.Model.codePrims)
      (fun n ps i j => ∃ t, DerivesAt Ecma.Spec.gl cx .lexical (codeAlphabet Engine.Model.codePrims) fullSrc k n ps i j t)
      fullSrc s lk pos ↔
    LookOk (codeAlphabet Engine.Model.codePrims)
      (fun n ps i j => ∃ t, DerivesAt Ecma.Spec.gl cx .lexical (codeAlphabet Engine.Model.codePrims) (slice fullSrc lo hi) k n ps i j t)
      (slice fullSrc lo hi) s lk (pos - lo) := by
  let src := slice fullSrc lo hi
  have hsrcLen : src.length = hi - lo := slice_length_eq fullSrc (by omega) hhi
  have hpFull : pos < fullSrc.length := by omega
  have hpSub : pos - lo < src.length := by omega
  have hgetEq : src[pos - lo]? = fullSrc[pos]? := by
    have := slice_getElem? fullSrc (lo := lo) (hi := hi) (k := pos - lo) (by omega)
    rwa [show lo + (pos - lo) = pos from by omega] at this
  have honeEq : ∀ x, oneCpTermOk x = true →
      (StartsWith (codeAlphabet Engine.Model.codePrims) fullSrc s [.t x] pos ↔
        StartsWith (codeAlphabet Engine.Model.codePrims) src s [.t x] (pos - lo)) := by
    intro x hx
    rw [oneCpTerm_iff hx hpFull, oneCpTerm_iff hx hpSub, hgetEq]
  have hseq1 : ∀ q : List LookItem, (match q with | [.t x] => oneCpTermOk x | _ => false) = true →
      (StartsWith (codeAlphabet Engine.Model.codePrims) fullSrc s q pos ↔
        StartsWith (codeAlphabet Engine.Model.codePrims) src s q (pos - lo)) := by
    intro q hq
    cases q with
    | nil => cases hq
    | cons li1 qtl =>
      cases qtl with
      | cons _ _ => cases li1 <;> cases hq
      | nil =>
        cases li1 with
        | noLT => cases hq
        | t x => exact honeEq x hq
  unfold lexLookKindOk at hlkOk
  cases lk with
  | eq q =>
    cases q with
    | nil => cases hlkOk
    | cons li1 qtl =>
      cases qtl with
      | cons _ _ => cases li1 <;> cases hlkOk
      | nil => cases li1 with | noLT => cases hlkOk | t x => exact honeEq x hlkOk
  | ne q =>
    cases q with
    | nil => cases hlkOk
    | cons li1 qtl =>
      cases qtl with
      | cons _ _ => cases li1 <;> cases hlkOk
      | nil => cases li1 with | noLT => cases hlkOk | t x => exact not_congr (honeEq x hlkOk)
  | mem qs =>
    dsimp only [LookOk]
    exact exists_congr fun q => and_congr_right fun hq => hseq1 q (List.all_eq_true.mp hlkOk q hq)
  | notMem qs =>
    dsimp only [LookOk]
    exact forall_congr' fun q => imp_congr_right fun hq => not_congr (hseq1 q (List.all_eq_true.mp hlkOk q hq))
  | notMemNT d =>
    dsimp only [LookOk] at hlkOk ⊢
    apply not_congr
    cases k with
    | zero =>
      simp [DerivesAt]
    | succ k0 =>
      rw [digit_derivesAt_succ_iff hok hlkOk hpFull k0,
          digit_derivesAt_succ_iff hok hlkOk hpSub k0, hgetEq]

private theorem condOk_codePrims_shift {fullSrc : List Nat} {lo hi : Nat}
    {is : List Item} {t : Tree}
    (ha : lo ≤ t.span.1) (hb : t.span.2 ≤ hi)
    (hnlex : ∀ idx sub, t ≠ .lex idx sub) :
    CondOk (codeAlphabet Engine.Model.codePrims) (slice fullSrc lo hi) is (shiftCodeTree lo t) ↔
      CondOk (codeAlphabet Engine.Model.codePrims) fullSrc is t := by
  cases is with
  | nil => exact Iff.rfl
  | cons hd _ =>
    cases hd with
    | onlyIf ph =>
      have hsp : (shiftCodeTree lo t).span = (t.span.1 - lo, t.span.2 - lo) := by
        cases t with
        | leaf _ _ => rw [shiftCodeTree_leaf]; rfl
        | node _ _ _ _ _ _ => rw [shiftCodeTree_node]; rfl
        | lex idx sub => exact absurd rfl (hnlex idx sub)
      dsimp only [CondOk, codeAlphabet]
      unfold Engine.Model.codePrims
      dsimp only
      rw [hsp, slice_of_slice fullSrc ha hb]
    | _ => exact Iff.rfl

private theorem condOk_codePrims_unshift {fullSrc : List Nat} {lo hi : Nat}
    {is : List Item} {t' : Tree}
    (hb : t'.span.2 ≤ hi - lo)
    (hnlex : ∀ idx sub, t' ≠ .lex idx sub) :
    CondOk (codeAlphabet Engine.Model.codePrims) fullSrc is (unshiftCodeTree lo t') ↔
      CondOk (codeAlphabet Engine.Model.codePrims) (slice fullSrc lo hi) is t' := by
  cases is with
  | nil => exact Iff.rfl
  | cons hd _ =>
    cases hd with
    | onlyIf ph =>
      have hsp : (unshiftCodeTree lo t').span = (lo + t'.span.1, lo + t'.span.2) := by
        cases t' with
        | leaf _ _ => rw [unshiftCodeTree_leaf]; rfl
        | node _ _ _ _ _ _ => rw [unshiftCodeTree_node]; rfl
        | lex idx sub => exact absurd rfl (hnlex idx sub)
      dsimp only [CondOk, codeAlphabet]
      unfold Engine.Model.codePrims
      dsimp only
      rw [hsp, slice_unshift fullSrc hb]
    | _ => exact Iff.rfl

private theorem lex_derivesAt_slice_bijection (hok : parseTablesOk = true) {cx : Ctx}
    {fullSrc : List Nat} {lo hi : Nat} (hlh : lo < hi) (hhi : hi ≤ fullSrc.length)
    (hclose : fullSrc[hi - 1]? = some 0x29) :
    let src := slice fullSrc lo hi
    let P := Engine.Model.codePrims
    ∀ (k : Nat),
      (∀ {m ps a b t}, lo ≤ a → b ≤ hi →
        DerivesAt Ecma.Spec.gl cx .lexical (codeAlphabet P) fullSrc k m ps a b t →
        DerivesAt Ecma.Spec.gl cx .lexical (codeAlphabet P) src k m ps (a - lo) (b - lo) (shiftCodeTree lo t)) ∧
      (∀ {m ps a' b' t'}, b' ≤ hi - lo →
        DerivesAt Ecma.Spec.gl cx .lexical (codeAlphabet P) src k m ps a' b' t' →
        DerivesAt Ecma.Spec.gl cx .lexical (codeAlphabet P) fullSrc k m ps (lo + a') (lo + b') (unshiftCodeTree lo t')) := by
  intro src P k
  have hsrcLen : src.length = hi - lo := slice_length_eq fullSrc (by omega) hhi
  have hcloseSub : src[hi - lo - 1]? = some 0x29 := by
    have hg := slice_getElem? fullSrc (lo := lo) (hi := hi) (k := hi - lo - 1) (by omega)
    rw [show lo + (hi - lo - 1) = hi - 1 from by omega, hclose] at hg
    exact hg
  have hcert3 := (Bool.and_eq_true_iff.mp lexLookCert_true).2
  induction k with
  | zero => exact ⟨(fun _ _ h => nomatch h), (fun _ h => nomatch h)⟩
  | succ k0 ihk =>
    let negFull := fun n ps i j => ∃ t, DerivesAt Ecma.Spec.gl cx .lexical (codeAlphabet P) fullSrc k0 n ps i j t
    let negSub := fun n ps i j => ∃ t, DerivesAt Ecma.Spec.gl cx .lexical (codeAlphabet P) src k0 n ps i j t
    have hexclIff : ∀ {s kIdx ps a h ex}, lo ≤ a → a ≤ h → h ≤ hi →
        (Excluded (codeAlphabet P) negFull fullSrc s kIdx ps a h ex ↔
          Excluded (codeAlphabet P) negSub src s kIdx ps (a - lo) (h - lo) ex) := by
      intro s kIdx ps a h ex ha hah hh
      have hsymIff : ∀ y : Sym,
          (match y with | .t x => (codeAlphabet P).term s kIdx x (slice fullSrc a h) | .nt m' args' => negFull m' (applyArgs ps args') a h) ↔
          (match y with | .t x => (codeAlphabet P).term s kIdx x (slice src (a - lo) (h - lo)) | .nt m' args' => negSub m' (applyArgs ps args') (a - lo) (h - lo)) := by
        intro y; cases y with
        | t x => rw [slice_of_slice fullSrc ha hh]
        | nt m' args' =>
          constructor
          · rintro ⟨t0, hd0⟩; exact ⟨_, ihk.1 ha hh hd0⟩
          · rintro ⟨t0', hd0'⟩
            have hdFull := ihk.2 (by omega) hd0'
            have h1 : lo + (a - lo) = a := by omega
            have h2 : lo + (h - lo) = h := by omega
            rw [h1, h2] at hdFull
            exact ⟨_, hdFull⟩
      cases ex with
      | sym y => exact hsymIff y
      | oneOf ys _ => exact exists_congr fun y => and_congr_right fun _ => hsymIff y
    have hmutFwd : ∀ (sz : Nat),
        (∀ {m ps a b t}, treeSize t ≤ sz → lo ≤ a → b ≤ hi →
          Step (codeAlphabet P) negFull fullSrc Ecma.Spec.gl cx .lexical m ps a b t →
          Step (codeAlphabet P) negSub src Ecma.Spec.gl cx .lexical m ps (a - lo) (b - lo) (shiftCodeTree lo t)) ∧
        (∀ {s ps kIdx is a b mask ts} {safe : Bool}, treeSize.treeListSize ts ≤ sz →
          lo ≤ a → b ≤ hi →
          (∀ it ∈ is, itemTermNonEmpty it = true) →
          lexRhsLookScan safe is = true →
          (safe = true → lo < a ∧ fullSrc[a - 1]? ≠ some 0x29) →
          Ecma.Grammar.Seq (codeAlphabet P) negFull fullSrc Ecma.Spec.gl cx .lexical s ps kIdx is a b mask ts →
          Ecma.Grammar.Seq (codeAlphabet P) negSub src Ecma.Spec.gl cx .lexical s ps kIdx is (a - lo) (b - lo) mask (ts.map (shiftCodeTree lo))) := by
      intro sz
      induction sz using Nat.strongRecOn with
      | ind sz ih =>
        have hst : ∀ {m ps a b t}, treeSize t ≤ sz → lo ≤ a → b ≤ hi →
            Step (codeAlphabet P) negFull fullSrc Ecma.Spec.gl cx .lexical m ps a b t →
            Step (codeAlphabet P) negSub src Ecma.Spec.gl cx .lexical m ps (a - lo) (b - lo) (shiftCodeTree lo t) := by
          intro m ps a b t hsz ha hb hs
          cases hs with
          | lex _ _ hl => nomatch hl
          | node s hsMem hgrd hpid hseq =>
            dsimp only [treeSize] at hsz
            have hsG := hsMem; rw [← glData_eq] at hsG
            obtain ⟨hrMem, haMem⟩ := mem_rulesForGrammar_of_alts rfl hsG
            have hscanOk := List.all_eq_true.mp (List.all_eq_true.mp hcert3 s.rule hrMem) s.alt haMem
            rw [shiftCodeTree_node]
            exact .node s hsMem hgrd hpid
              ((ih _ (by omega)).2 (Nat.le_refl _) ha hb
                (fun it hit => item_term_nonempty_of_alts hok hsMem hit) hscanOk (fun hf => by cases hf) hseq)
        refine ⟨hst, ?_⟩
        intro s ps kIdx is
        induction is generalizing kIdx with
        | nil =>
          intro a b mask ts safe _ _ _ _ _ _ hs
          cases hs; exact .nil
        | cons it rest ihr =>
          intro a b mask ts safe hsz ha hb hne hscan hsafe hs
          have hneIt := hne it (List.mem_cons_self ..)
          have hneRest : ∀ x ∈ rest, itemTermNonEmpty x = true :=
            fun x hx => hne x (List.mem_cons_of_mem _ hx)
          cases hs with
          | @absent _ _ _ sym0 _ _ _ _ _ hr =>
            have hscanR : lexRhsLookScan false rest = true := by
              cases sym0 with
              | nt _ _ => unfold lexRhsLookScan at hscan; exact hscan
              | t tx =>
                cases tx with
                | text _ _ => unfold lexRhsLookScan at hscan; exact hscan
                | cp cn => cases cn <;> (unfold lexRhsLookScan at hscan; exact hscan)
            exact .absent (ihr hsz ha hb hneRest hscanR (fun hf => by cases hf) hr)
          | noLT _ hr =>
            have hscanR : lexRhsLookScan false rest = true := by
              unfold lexRhsLookScan at hscan; exact hscan
            exact .noLT trivial (ihr hsz ha hb hneRest hscanR (fun hf => by cases hf) hr)
          | empty hr =>
            unfold lexRhsLookScan at hscan
            exact .empty (ihr hsz ha hb hneRest hscan hsafe hr)
          | onlyIf hr =>
            unfold lexRhsLookScan at hscan
            exact .onlyIf (ihr hsz ha hb hneRest hscan hsafe hr)
          | @look _ _ _ lk _ _ _ _ _ hlk hr =>
            unfold lexRhsLookScan at hscan
            simp only [Bool.and_eq_true] at hscan
            obtain ⟨⟨hsafeT, hlkOk⟩, hscanR⟩ := hscan
            obtain ⟨hloLtA, hneClose⟩ := hsafe hsafeT
            have hab := (code_step_bounds hok (treeSize.treeListSize ts)).2 (Nat.le_refl _) hneRest hr
            have haLtHi : a < hi := by
              by_cases heq : a = hi
              · subst heq; exact absurd hclose hneClose
              · omega
            have hlk' := (lex_lookOk_slice_iff hok hlh hhi hlkOk ha haLtHi k0).mp hlk
            exact .look hlk' (ihr hsz ha hb hneRest hscanR hsafe hr)
          | @phrase _ _ _ ph _ _ h _ _ _ hph hr =>
            dsimp only [treeSize.treeListSize, treeSize] at hsz
            obtain ⟨c, hw, hpc⟩ := hph
            have hlt := (slice_nonempty_imp_lt (by rw [hw]; exact List.cons_ne_nil _ _)).1
            have hhb := (code_step_bounds hok (treeSize.treeListSize _)).2 (Nat.le_refl _) hneRest hr
            have hph' : (codeAlphabet P).phrase ph (slice src (a - lo) (h - lo)) := by
              rw [slice_of_slice fullSrc ha (by omega)]; exact ⟨c, hw, hpc⟩
            have hscanR : lexRhsLookScan false rest = true := by
              unfold lexRhsLookScan at hscan; exact hscan
            rw [List.map_cons, shiftCodeTree_leaf]
            exact .phrase hph' (ihr (by omega) (by omega) hb hneRest hscanR (fun hf => by cases hf) hr)
          | @butNotT _ _ _ x ex _ _ h _ _ _ ht hex hr =>
            dsimp only [treeSize.treeListSize, treeSize] at hsz
            have hlt := (slice_nonempty_imp_lt (code_term_nonempty (itemTermNonEmpty_butNot hneIt) ht)).1
            have hhb := (code_step_bounds hok (treeSize.treeListSize _)).2 (Nat.le_refl _) hneRest hr
            have ht' : (codeAlphabet P).term s kIdx x (slice src (a - lo) (h - lo)) := by
              rwa [slice_of_slice fullSrc ha (by omega)]
            have hex' : ¬ Excluded (codeAlphabet P) negSub src s kIdx ps (a - lo) (h - lo) ex :=
              fun hx => hex ((hexclIff ha (Nat.le_of_lt hlt) (by omega)).mpr hx)
            have hscanR : lexRhsLookScan false rest = true := by
              unfold lexRhsLookScan at hscan; exact hscan
            rw [List.map_cons, shiftCodeTree_leaf]
            exact .butNotT ht' hex' (ihr (by omega) (by omega) hb hneRest hscanR (fun hf => by cases hf) hr)
          | @butNotN _ _ _ m0 args0 ex _ _ h _ _ t0 _ hs0 hex hr =>
            dsimp only [treeSize.treeListSize] at hsz
            obtain ⟨hah, _, _⟩ := (code_step_bounds hok (treeSize t0)).1 (Nat.le_refl _) hs0
            have hhb := (code_step_bounds hok (treeSize.treeListSize _)).2 (Nat.le_refl _) hneRest hr
            have hs0' := hst (by omega) ha (by omega) hs0
            have hex' : ¬ Excluded (codeAlphabet P) negSub src s kIdx ps (a - lo) (h - lo) ex :=
              fun hx => hex ((hexclIff ha hah (by omega)).mpr hx)
            have hscanR : lexRhsLookScan false rest = true := by
              unfold lexRhsLookScan at hscan; exact hscan
            rw [List.map_cons]
            exact .butNotN hs0' hex' (ihr (by omega) (by omega) hb hneRest hscanR (fun hf => by cases hf) hr)
          | @term _ _ _ x o _ _ h _ _ _ ht hr =>
            dsimp only [treeSize.treeListSize, treeSize] at hsz
            have hlt := (slice_nonempty_imp_lt (code_term_nonempty (itemTermNonEmpty_sym hneIt) ht)).1
            have hhb := (code_step_bounds hok (treeSize.treeListSize _)).2 (Nat.le_refl _) hneRest hr
            have ht' : (codeAlphabet P).term s kIdx x (slice src (a - lo) (h - lo)) := by
              rwa [slice_of_slice fullSrc ha (by omega)]
            rw [List.map_cons, shiftCodeTree_leaf]
            cases o with
            | true =>
              have hscanR : lexRhsLookScan false rest = true := by
                cases x with
                | text _ _ => unfold lexRhsLookScan at hscan; exact hscan
                | cp cn => cases cn <;> (unfold lexRhsLookScan at hscan; exact hscan)
              exact .term ht' (ihr (by omega) (by omega) hb hneRest hscanR (fun hf => by cases hf) hr)
            | false =>
              cases x with
              | text str b0 =>
                let safe' := match str.toList.getLast? with | some c => c != ')' && str != "" | none => false
                have hscanR : lexRhsLookScan safe' rest = true := by
                  unfold lexRhsLookScan at hscan; exact hscan
                have hsafe' : safe' = true → lo < h ∧ fullSrc[h - 1]? ≠ some 0x29 := by
                  intro hsT
                  dsimp only [safe'] at hsT
                  cases hlast : str.toList.getLast? with
                  | none => rw [hlast] at hsT; cases hsT
                  | some ch =>
                    rw [hlast] at hsT
                    simp only [Bool.and_eq_true, bne_iff_ne] at hsT
                    have hneL : str.toList ≠ [] := fun h0 => by simp [h0] at hlast
                    have hgetL : str.toList.getLast hneL = ch := by
                      rw [List.getLast?_eq_some_getLast hneL] at hlast; exact Option.some.inj hlast
                    have hcat : str.toList = str.toList.dropLast ++ [ch] := by
                      rw [← hgetL]; exact (List.dropLast_concat_getLast hneL).symm
                    have hmap : slice fullSrc a h = str.toList.dropLast.map Char.toNat ++ [ch.toNat] := by
                      dsimp only [codeAlphabet] at ht
                      have hcatMap := congrArg (List.map Char.toNat) hcat
                      simp only [List.map_append, List.map_cons, List.map_nil] at hcatMap
                      exact ht.trans hcatMap
                    obtain ⟨_, hget⟩ := slice_last_eq_getElem? (by omega) hmap
                    refine ⟨by omega, ?_⟩
                    rw [hget]; intro heq; exact char_toNat_ne_close_paren hsT.1 (Option.some.inj heq)
                exact .term ht' (ihr (by omega) (by omega) hb hneRest hscanR hsafe' hr)
              | cp cn =>
                by_cases hcr : cn = .CR
                · subst hcr
                  have hscanR : lexRhsLookScan true rest = true := by
                    unfold lexRhsLookScan at hscan; exact hscan
                  have hsafe' : true = true → lo < h ∧ fullSrc[h - 1]? ≠ some 0x29 := by
                    intro _
                    have hmap : slice fullSrc a h = ([] : List Nat) ++ [0x0D] := by
                      dsimp only [codeAlphabet, CodePointName.codePoint] at ht; simpa using ht
                    obtain ⟨_, hget⟩ := slice_last_eq_getElem? (by omega) hmap
                    exact ⟨by omega, by rw [hget]; decide⟩
                  exact .term ht' (ihr (by omega) (by omega) hb hneRest hscanR hsafe' hr)
                · have hscanR : lexRhsLookScan false rest = true := by
                    cases cn <;> first | exact absurd rfl hcr | (unfold lexRhsLookScan at hscan; exact hscan)
                  exact .term ht' (ihr (by omega) (by omega) hb hneRest hscanR (fun hf => by cases hf) hr)
          | @nt _ _ _ m0 args0 o _ _ h _ _ t0 _ hs0 hcd hr =>
            dsimp only [treeSize.treeListSize] at hsz
            obtain ⟨hah, hsp0, hnlex0⟩ := (code_step_bounds hok (treeSize t0)).1 (Nat.le_refl _) hs0
            have hhb := (code_step_bounds hok (treeSize.treeListSize _)).2 (Nat.le_refl _) hneRest hr
            have hs0' := hst (by omega) ha (by omega) hs0
            have hcd' := (condOk_codePrims_shift (hi := hi) (by rw [hsp0]; exact ha) (by rw [hsp0]; omega) hnlex0).mpr hcd
            rw [List.map_cons]
            cases o with
            | true =>
              have hscanR : lexRhsLookScan false rest = true := by
                unfold lexRhsLookScan at hscan; exact hscan
              exact .nt hs0' hcd' (ihr (by omega) (by omega) hb hneRest hscanR (fun hf => by cases hf) hr)
            | false =>
              have hscanR : lexRhsLookScan (lexEndsNonCloseParenNTs.contains m0) rest = true := by
                unfold lexRhsLookScan at hscan; exact hscan
              have hsafe' : lexEndsNonCloseParenNTs.contains m0 = true → lo < h ∧ fullSrc[h - 1]? ≠ some 0x29 := by
                intro hm0
                obtain ⟨hlt0, hne0⟩ := lex_ends_non_close_paren hok (treeSize t0) (Nat.le_refl _) (by omega) hm0 hs0
                exact ⟨by omega, hne0⟩
              exact .nt hs0' hcd' (ihr (by omega) (by omega) hb hneRest hscanR hsafe' hr)
    have hmutBwd : ∀ (sz : Nat),
        (∀ {m ps a' b' t'}, treeSize t' ≤ sz → b' ≤ hi - lo →
          Step (codeAlphabet P) negSub src Ecma.Spec.gl cx .lexical m ps a' b' t' →
          Step (codeAlphabet P) negFull fullSrc Ecma.Spec.gl cx .lexical m ps (lo + a') (lo + b') (unshiftCodeTree lo t')) ∧
        (∀ {s ps kIdx is a' b' mask ts'} {safe : Bool}, treeSize.treeListSize ts' ≤ sz →
          b' ≤ hi - lo →
          (∀ it ∈ is, itemTermNonEmpty it = true) →
          lexRhsLookScan safe is = true →
          (safe = true → 0 < a' ∧ src[a' - 1]? ≠ some 0x29) →
          Ecma.Grammar.Seq (codeAlphabet P) negSub src Ecma.Spec.gl cx .lexical s ps kIdx is a' b' mask ts' →
          Ecma.Grammar.Seq (codeAlphabet P) negFull fullSrc Ecma.Spec.gl cx .lexical s ps kIdx is (lo + a') (lo + b') mask (ts'.map (unshiftCodeTree lo))) := by
      intro sz
      induction sz using Nat.strongRecOn with
      | ind sz ih =>
        have hst : ∀ {m ps a' b' t'}, treeSize t' ≤ sz → b' ≤ hi - lo →
            Step (codeAlphabet P) negSub src Ecma.Spec.gl cx .lexical m ps a' b' t' →
            Step (codeAlphabet P) negFull fullSrc Ecma.Spec.gl cx .lexical m ps (lo + a') (lo + b') (unshiftCodeTree lo t') := by
          intro m ps a' b' t' hsz hb' hs
          cases hs with
          | lex _ _ hl => nomatch hl
          | node s hsMem hgrd hpid hseq =>
            dsimp only [treeSize] at hsz
            have hsG := hsMem; rw [← glData_eq] at hsG
            obtain ⟨hrMem, haMem⟩ := mem_rulesForGrammar_of_alts rfl hsG
            have hscanOk := List.all_eq_true.mp (List.all_eq_true.mp hcert3 s.rule hrMem) s.alt haMem
            rw [unshiftCodeTree_node]
            exact .node s hsMem hgrd hpid
              ((ih _ (by omega)).2 (Nat.le_refl _) hb'
                (fun it hit => item_term_nonempty_of_alts hok hsMem hit) hscanOk (fun hf => by cases hf) hseq)
        refine ⟨hst, ?_⟩
        intro s ps kIdx is
        induction is generalizing kIdx with
        | nil =>
          intro a' b' mask ts' safe _ _ _ _ _ hs
          cases hs; exact .nil
        | cons it rest ihr =>
          intro a' b' mask ts' safe hsz hb' hne hscan hsafe hs
          have hneIt := hne it (List.mem_cons_self ..)
          have hneRest : ∀ x ∈ rest, itemTermNonEmpty x = true :=
            fun x hx => hne x (List.mem_cons_of_mem _ hx)
          cases hs with
          | @absent _ _ _ sym0 _ _ _ _ _ hr =>
            have hscanR : lexRhsLookScan false rest = true := by
              cases sym0 with
              | nt _ _ => unfold lexRhsLookScan at hscan; exact hscan
              | t tx =>
                cases tx with
                | text _ _ => unfold lexRhsLookScan at hscan; exact hscan
                | cp cn => cases cn <;> (unfold lexRhsLookScan at hscan; exact hscan)
            exact .absent (ihr hsz hb' hneRest hscanR (fun hf => by cases hf) hr)
          | noLT _ hr =>
            have hscanR : lexRhsLookScan false rest = true := by
              unfold lexRhsLookScan at hscan; exact hscan
            exact .noLT trivial (ihr hsz hb' hneRest hscanR (fun hf => by cases hf) hr)
          | empty hr =>
            unfold lexRhsLookScan at hscan
            exact .empty (ihr hsz hb' hneRest hscan hsafe hr)
          | onlyIf hr =>
            unfold lexRhsLookScan at hscan
            exact .onlyIf (ihr hsz hb' hneRest hscan hsafe hr)
          | @look _ _ _ lk _ _ _ _ _ hlk hr =>
            unfold lexRhsLookScan at hscan
            simp only [Bool.and_eq_true] at hscan
            obtain ⟨⟨hsafeT, hlkOk⟩, hscanR⟩ := hscan
            obtain ⟨hposA, hneClose⟩ := hsafe hsafeT
            have hab' := (code_step_bounds hok (treeSize.treeListSize ts')).2 (Nat.le_refl _) hneRest hr
            have haLt : a' < hi - lo := by
              by_cases heq : a' = hi - lo
              · subst heq; exact absurd hcloseSub hneClose
              · omega
            have hlkFull : LookOk (codeAlphabet P) negFull fullSrc s lk (lo + a') := by
              have hiff := lex_lookOk_slice_iff (cx := cx) (s := s) hok hlh hhi hlkOk (pos := lo + a') (by omega) (by omega) k0
              rw [Nat.add_sub_cancel_left] at hiff
              exact hiff.mpr hlk
            exact .look hlkFull (ihr hsz hb' hneRest hscanR hsafe hr)
          | @phrase _ _ _ ph _ _ h' _ _ _ hph hr =>
            dsimp only [treeSize.treeListSize, treeSize] at hsz
            obtain ⟨c, hw, hpc⟩ := hph
            have hhb' := (code_step_bounds hok (treeSize.treeListSize _)).2 (Nat.le_refl _) hneRest hr
            have hphFull : (codeAlphabet P).phrase ph (slice fullSrc (lo + a') (lo + h')) := by
              rw [slice_unshift fullSrc (hi := hi) (by omega)]; exact ⟨c, hw, hpc⟩
            have hscanR : lexRhsLookScan false rest = true := by
              unfold lexRhsLookScan at hscan; exact hscan
            rw [List.map_cons, unshiftCodeTree_leaf]
            exact .phrase hphFull (ihr (by omega) hb' hneRest hscanR (fun hf => by cases hf) hr)
          | @butNotT _ _ _ x ex _ _ h' _ _ _ ht hex hr =>
            dsimp only [treeSize.treeListSize, treeSize] at hsz
            have hlt' := (slice_nonempty_imp_lt (code_term_nonempty (itemTermNonEmpty_butNot hneIt) ht)).1
            have hhb' := (code_step_bounds hok (treeSize.treeListSize _)).2 (Nat.le_refl _) hneRest hr
            have htFull : (codeAlphabet P).term s kIdx x (slice fullSrc (lo + a') (lo + h')) := by
              rwa [slice_unshift fullSrc (hi := hi) (by omega)]
            have hexFull : ¬ Excluded (codeAlphabet P) negFull fullSrc s kIdx ps (lo + a') (lo + h') ex := by
              intro hx
              have hx' := (hexclIff (a := lo + a') (h := lo + h') (by omega) (by omega) (by omega)).mp hx
              simp only [Nat.add_sub_cancel_left] at hx'
              exact hex hx'
            have hscanR : lexRhsLookScan false rest = true := by
              unfold lexRhsLookScan at hscan; exact hscan
            rw [List.map_cons, unshiftCodeTree_leaf]
            exact .butNotT htFull hexFull (ihr (by omega) hb' hneRest hscanR (fun hf => by cases hf) hr)
          | @butNotN _ _ _ m0 args0 ex _ _ h' _ _ t0' _ hs0 hex hr =>
            dsimp only [treeSize.treeListSize] at hsz
            obtain ⟨hah', _, _⟩ := (code_step_bounds hok (treeSize t0')).1 (Nat.le_refl _) hs0
            have hhb' := (code_step_bounds hok (treeSize.treeListSize _)).2 (Nat.le_refl _) hneRest hr
            have hs0Full := hst (by omega) (by omega) hs0
            have hexFull : ¬ Excluded (codeAlphabet P) negFull fullSrc s kIdx ps (lo + a') (lo + h') ex := by
              intro hx
              have hx' := (hexclIff (a := lo + a') (h := lo + h') (by omega) (by omega) (by omega)).mp hx
              simp only [Nat.add_sub_cancel_left] at hx'
              exact hex hx'
            have hscanR : lexRhsLookScan false rest = true := by
              unfold lexRhsLookScan at hscan; exact hscan
            rw [List.map_cons]
            exact .butNotN hs0Full hexFull (ihr (by omega) hb' hneRest hscanR (fun hf => by cases hf) hr)
          | @term _ _ _ x o _ _ h' _ _ _ ht hr =>
            dsimp only [treeSize.treeListSize, treeSize] at hsz
            have hlt' := (slice_nonempty_imp_lt (code_term_nonempty (itemTermNonEmpty_sym hneIt) ht)).1
            have hhb' := (code_step_bounds hok (treeSize.treeListSize _)).2 (Nat.le_refl _) hneRest hr
            have htFull : (codeAlphabet P).term s kIdx x (slice fullSrc (lo + a') (lo + h')) := by
              rwa [slice_unshift fullSrc (hi := hi) (by omega)]
            rw [List.map_cons, unshiftCodeTree_leaf]
            cases o with
            | true =>
              have hscanR : lexRhsLookScan false rest = true := by
                cases x with
                | text _ _ => unfold lexRhsLookScan at hscan; exact hscan
                | cp cn => cases cn <;> (unfold lexRhsLookScan at hscan; exact hscan)
              exact .term htFull (ihr (by omega) hb' hneRest hscanR (fun hf => by cases hf) hr)
            | false =>
              cases x with
              | text str b0 =>
                let safe' := match str.toList.getLast? with | some c => c != ')' && str != "" | none => false
                have hscanR : lexRhsLookScan safe' rest = true := by
                  unfold lexRhsLookScan at hscan; exact hscan
                have hsafe' : safe' = true → 0 < h' ∧ src[h' - 1]? ≠ some 0x29 := by
                  intro hsT
                  dsimp only [safe'] at hsT
                  cases hlast : str.toList.getLast? with
                  | none => rw [hlast] at hsT; cases hsT
                  | some ch =>
                    rw [hlast] at hsT
                    simp only [Bool.and_eq_true, bne_iff_ne] at hsT
                    have hneL : str.toList ≠ [] := fun h0 => by simp [h0] at hlast
                    have hgetL : str.toList.getLast hneL = ch := by
                      rw [List.getLast?_eq_some_getLast hneL] at hlast; exact Option.some.inj hlast
                    have hcat : str.toList = str.toList.dropLast ++ [ch] := by
                      rw [← hgetL]; exact (List.dropLast_concat_getLast hneL).symm
                    have hmap : slice src a' h' = str.toList.dropLast.map Char.toNat ++ [ch.toNat] := by
                      dsimp only [codeAlphabet] at ht
                      have hcatMap := congrArg (List.map Char.toNat) hcat
                      simp only [List.map_append, List.map_cons, List.map_nil] at hcatMap
                      exact ht.trans hcatMap
                    obtain ⟨_, hget⟩ := slice_last_eq_getElem? (by omega) hmap
                    refine ⟨by omega, ?_⟩
                    rw [hget]; intro heq; exact char_toNat_ne_close_paren hsT.1 (Option.some.inj heq)
                exact .term htFull (ihr (by omega) hb' hneRest hscanR hsafe' hr)
              | cp cn =>
                by_cases hcr : cn = .CR
                · subst hcr
                  have hscanR : lexRhsLookScan true rest = true := by
                    unfold lexRhsLookScan at hscan; exact hscan
                  have hsafe' : true = true → 0 < h' ∧ src[h' - 1]? ≠ some 0x29 := by
                    intro _
                    have hmap : slice src a' h' = ([] : List Nat) ++ [0x0D] := by
                      dsimp only [codeAlphabet, CodePointName.codePoint] at ht; simpa using ht
                    obtain ⟨_, hget⟩ := slice_last_eq_getElem? (by omega) hmap
                    exact ⟨by omega, by rw [hget]; decide⟩
                  exact .term htFull (ihr (by omega) hb' hneRest hscanR hsafe' hr)
                · have hscanR : lexRhsLookScan false rest = true := by
                    cases cn <;> first | exact absurd rfl hcr | (unfold lexRhsLookScan at hscan; exact hscan)
                  exact .term htFull (ihr (by omega) hb' hneRest hscanR (fun hf => by cases hf) hr)
          | @nt _ _ _ m0 args0 o _ _ h' _ _ t0' _ hs0 hcd hr =>
            dsimp only [treeSize.treeListSize] at hsz
            obtain ⟨_, _, hnlex0⟩ := (code_step_bounds hok (treeSize t0')).1 (Nat.le_refl _) hs0
            have hhb' := (code_step_bounds hok (treeSize.treeListSize _)).2 (Nat.le_refl _) hneRest hr
            have hs0Full := hst (by omega) (by omega) hs0
            have hcdFull := (condOk_codePrims_unshift (hi := hi) (by
              have ⟨_, hsp', _⟩ := (code_step_bounds hok (treeSize t0')).1 (Nat.le_refl _) hs0
              rw [hsp']; omega) hnlex0).mpr hcd
            rw [List.map_cons]
            cases o with
            | true =>
              have hscanR : lexRhsLookScan false rest = true := by
                unfold lexRhsLookScan at hscan; exact hscan
              exact .nt hs0Full hcdFull (ihr (by omega) hb' hneRest hscanR (fun hf => by cases hf) hr)
            | false =>
              have hscanR : lexRhsLookScan (lexEndsNonCloseParenNTs.contains m0) rest = true := by
                unfold lexRhsLookScan at hscan; exact hscan
              have hsafe' : lexEndsNonCloseParenNTs.contains m0 = true → 0 < h' ∧ src[h' - 1]? ≠ some 0x29 := by
                intro hm0
                obtain ⟨hlt0, hne0⟩ := lex_ends_non_close_paren hok (treeSize t0') (Nat.le_refl _) (by omega) hm0 hs0
                exact ⟨by omega, hne0⟩
              exact .nt hs0Full hcdFull (ihr (by omega) hb' hneRest hscanR hsafe' hr)
    exact ⟨fun ha hb hs => (hmutFwd (treeSize _)).1 (Nat.le_refl _) ha hb hs,
           fun hb' hs => (hmutBwd (treeSize _)).1 (Nat.le_refl _) hb' hs⟩

private theorem lex_derives_slice_fwd (hok : parseTablesOk = true) {cx : Ctx}
    {fullSrc : List Nat} {lo hi : Nat} (hlh : lo < hi) (hhi : hi ≤ fullSrc.length)
    (hclose : fullSrc[hi - 1]? = some 0x29)
    {m : NT} {ps : List Param} {a b : Nat} {t : Tree}
    (ha : lo ≤ a) (hb : b ≤ hi)
    (hd : Derives Ecma.Spec.gl cx .lexical (codeAlphabet Engine.Model.codePrims) fullSrc m ps a b t) :
    Derives Ecma.Spec.gl cx .lexical (codeAlphabet Engine.Model.codePrims) (slice fullSrc lo hi)
      m ps (a - lo) (b - lo) (shiftCodeTree lo t) := by
  obtain ⟨K, hK⟩ := hd
  exact ⟨K, fun k hk => (lex_derivesAt_slice_bijection hok hlh hhi hclose k).1 ha hb (hK k hk)⟩

private theorem lex_derives_slice_bwd (hok : parseTablesOk = true) {cx : Ctx}
    {fullSrc : List Nat} {lo hi : Nat} (hlh : lo < hi) (hhi : hi ≤ fullSrc.length)
    (hclose : fullSrc[hi - 1]? = some 0x29)
    {m : NT} {ps : List Param} {a' b' : Nat} {t' : Tree}
    (hb' : b' ≤ hi - lo)
    (hd : Derives Ecma.Spec.gl cx .lexical (codeAlphabet Engine.Model.codePrims) (slice fullSrc lo hi)
      m ps a' b' t') :
    Derives Ecma.Spec.gl cx .lexical (codeAlphabet Engine.Model.codePrims) fullSrc
      m ps (lo + a') (lo + b') (unshiftCodeTree lo t') := by
  obtain ⟨K, hK⟩ := hd
  exact ⟨K, fun k hk => (lex_derivesAt_slice_bijection hok hlh hhi hclose k).2 hb' (hK k hk)⟩


/-! ## Section 4: Lexical First-Char Lemmas, Element/Token Slicing, and `Scans` Restriction -/

private theorem lex_step_first_char_props (hok : parseTablesOk = true) {cx : Ctx}
    {neg : NT → List Param → Nat → Nat → Prop} {inp : List Nat} :
    ∀ (sz : Nat) {m : NT} {ps : List Param} {a b : Nat} {t : Tree},
      treeSize t ≤ sz →
      b ≤ inp.length →
      noSlashBraceLexNTs.contains m = true →
      Step (codeAlphabet Engine.Model.codePrims) neg inp Ecma.Spec.gl cx .lexical m ps a b t →
      a < b ∧ inp[a]? ≠ some 0x2F ∧ inp[a]? ≠ some 0x7D := by
  intro sz
  induction sz using Nat.strongRecOn with
  | ind sz ih =>
    intro m ps a b t hsz hb hm hs
    have hcx2 := List.all_eq_true.mp lexFirstCharCert_true
      (if Lex.html cx then cxHtmlTrue else cxHtmlFalse) (lexCertCx_mem cx)
    have hmOk := List.all_eq_true.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp hcx2).1).1 m
      (List.contains_iff_mem.mp hm)
    simp only [Bool.and_eq_true] at hmOk
    cases hs with
    | lex _ _ hl => nomatch hl
    | node s hsMem _ _ hseq =>
      dsimp only [treeSize] at hsz
      have hsG := hsMem; rw [alts_lexical_eq cx m] at hsG
      have hsOk := List.all_eq_true.mp hmOk.2 s hsG
      have hneAll : ∀ it ∈ s.alt.rhs, itemTermNonEmpty it = true :=
        fun it hit => item_term_nonempty_of_alts hok hsMem hit
      unfold rhsNoSlashBraceStart at hsOk
      generalize hrhs : s.alt.rhs = rhs0 at hsOk hseq hneAll
      cases rhs0 with
      | nil => cases hsOk
      | cons it rest =>
        have hneRest : ∀ x ∈ rest, itemTermNonEmpty x = true :=
          fun x hx => hneAll x (List.mem_cons_of_mem _ hx)
        cases it with
        | sym sym0 o =>
          cases sym0 with
          | t tx =>
            cases o with
            | true => cases tx <;> cases hsOk
            | false =>
              cases tx with
              | cp _ => cases hsOk
              | text str b0 =>
                dsimp only at hsOk
                cases hchL : str.toList with
                | nil => rw [hchL] at hsOk; cases hsOk
                | cons ch chTl =>
                  rw [hchL] at hsOk
                  simp only [Bool.and_eq_true, bne_iff_ne] at hsOk
                  cases hseq with
                  | @term _ _ _ _ _ _ _ h _ _ _ ht hr =>
                    dsimp only [treeSize.treeListSize, treeSize] at hsz
                    have hhb := (code_step_bounds hok (treeSize.treeListSize _)).2 (Nat.le_refl _) hneRest hr
                    dsimp only [codeAlphabet] at ht
                    rw [hchL, List.map_cons] at ht
                    have hlt := (slice_nonempty_imp_lt (by rw [ht]; exact List.cons_ne_nil _ _)).1
                    have hg := slice_getElem? inp (lo := a) (hi := h) (k := 0) (by omega)
                    rw [ht, Nat.add_zero] at hg
                    simp only [List.getElem?_cons_zero] at hg
                    refine ⟨by omega, ?_, ?_⟩
                    · rw [← hg]; intro heq; exact hsOk.1 (char_eq_of_toNat_eq (c := ch) (d := '/') (Option.some.inj heq))
                    · rw [← hg]; intro heq; exact hsOk.2 (char_eq_of_toNat_eq (c := ch) (d := '}') (Option.some.inj heq))
          | nt m1 args1 =>
            cases o with
            | true => cases hsOk
            | false =>
              cases hseq with
              | @nt _ _ _ _ _ _ _ _ h _ _ t1 _ hs1 _ hr =>
                dsimp only [treeSize.treeListSize] at hsz
                have hhb := (code_step_bounds hok (treeSize.treeListSize _)).2 (Nat.le_refl _) hneRest hr
                obtain ⟨hlt1, hn1, hn2⟩ := ih (treeSize t1) (by omega) (Nat.le_refl _) (by omega) hsOk hs1
                exact ⟨by omega, hn1, hn2⟩
        | butNot sym0 ex0 =>
          cases sym0 with
          | t tx =>
            cases tx with
            | cp _ => cases hsOk
            | text str b0 =>
              dsimp only at hsOk
              cases hchL : str.toList with
              | nil => rw [hchL] at hsOk; cases hsOk
              | cons ch chTl =>
                rw [hchL] at hsOk
                simp only [Bool.and_eq_true, bne_iff_ne] at hsOk
                cases hseq with
                | @butNotT _ _ _ _ _ _ _ h _ _ _ ht _ hr =>
                  dsimp only [treeSize.treeListSize, treeSize] at hsz
                  have hhb := (code_step_bounds hok (treeSize.treeListSize _)).2 (Nat.le_refl _) hneRest hr
                  dsimp only [codeAlphabet] at ht
                  rw [hchL, List.map_cons] at ht
                  have hlt := (slice_nonempty_imp_lt (by rw [ht]; exact List.cons_ne_nil _ _)).1
                  have hg := slice_getElem? inp (lo := a) (hi := h) (k := 0) (by omega)
                  rw [ht, Nat.add_zero] at hg
                  simp only [List.getElem?_cons_zero] at hg
                  refine ⟨by omega, ?_, ?_⟩
                  · rw [← hg]; intro heq; exact hsOk.1 (char_eq_of_toNat_eq (c := ch) (d := '/') (Option.some.inj heq))
                  · rw [← hg]; intro heq; exact hsOk.2 (char_eq_of_toNat_eq (c := ch) (d := '}') (Option.some.inj heq))
          | nt m1 args1 =>
            cases hseq with
            | @butNotN _ _ _ _ _ _ _ _ h _ _ t1 _ hs1 _ hr =>
              dsimp only [treeSize.treeListSize] at hsz
              have hhb := (code_step_bounds hok (treeSize.treeListSize _)).2 (Nat.le_refl _) hneRest hr
              obtain ⟨hlt1, hn1, hn2⟩ := ih (treeSize t1) (by omega) (Nat.le_refl _) (by omega) hsOk hs1
              exact ⟨by omega, hn1, hn2⟩
        | phrase ph =>
          cases ph with
          | idStart =>
            cases hseq with
            | @phrase _ _ _ _ _ _ h _ _ _ hp hr =>
              dsimp only [treeSize.treeListSize, treeSize] at hsz
              have hhb := (code_step_bounds hok (treeSize.treeListSize _)).2 (Nat.le_refl _) hneRest hr
              obtain ⟨c, hw, hidS⟩ := hp
              dsimp only [Engine.Model.codePrims] at hidS
              have hlt := (slice_nonempty_imp_lt (by rw [hw]; exact List.cons_ne_nil _ _)).1
              have hg := slice_getElem? inp (lo := a) (hi := h) (k := 0) (by omega)
              rw [hw, Nat.add_zero] at hg
              simp only [List.getElem?_cons_zero] at hg
              obtain ⟨hn2f, hn7d⟩ := idStart_not_slash_or_brace
              refine ⟨by omega, ?_, ?_⟩
              · rw [← hg]; intro heq; injection heq with hcEq; subst hcEq; rw [hn2f] at hidS; cases hidS
              · rw [← hg]; intro heq; injection heq with hcEq; subst hcEq; rw [hn7d] at hidS; cases hidS
          | _ => cases hsOk
        | _ => cases hsOk

private theorem lex_derives_starts_slash (hok : parseTablesOk = true) {cx : Ctx} {inp : List Nat}
    {m : NT} (hm : m = .DivPunctuator ∨ m = .RegularExpressionLiteral)
    {a b : Nat} (hb : b ≤ inp.length) {t : Tree}
    (hd : Derives Ecma.Spec.gl cx .lexical (codeAlphabet Engine.Model.codePrims) inp m [] a b t) :
    inp[a]? = some 0x2F := by
  have hcx2 := List.all_eq_true.mp lexFirstCharCert_true
    (if Lex.html cx then cxHtmlTrue else cxHtmlFalse) (lexCertCx_mem cx)
  have hmMem : m ∈ [NT.DivPunctuator, .RegularExpressionLiteral] := by
    rcases hm with rfl | rfl <;> decide
  have hmOk := List.all_eq_true.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp hcx2).1).2 m hmMem
  obtain ⟨K, hK⟩ := hd
  have hs := hK (max K 1) (Nat.le_max_left K 1)
  obtain ⟨k0, hk0⟩ : ∃ k0, max K 1 = k0 + 1 := ⟨max K 1 - 1, by omega⟩
  rw [hk0] at hs
  cases hs with
  | lex _ _ hl => nomatch hl
  | node s hsMem _ _ hseq =>
    have hsG := hsMem; rw [alts_lexical_eq cx m] at hsG
    have hsOk := List.all_eq_true.mp hmOk s hsG
    have hneAll : ∀ it ∈ s.alt.rhs, itemTermNonEmpty it = true :=
      fun it hit => item_term_nonempty_of_alts hok hsMem hit
    unfold rhsStartsChar at hsOk
    generalize hrhs : s.alt.rhs = rhs0 at hsOk hseq hneAll
    cases rhs0 with
    | nil => simp at hsOk
    | cons it rest =>
      cases it with
      | sym s0 o0 =>
        cases o0 with
        | true => cases s0 <;> simp at hsOk
        | false =>
          cases s0 with
          | nt _ _ => simp at hsOk
          | t tx0 =>
            cases tx0 with
            | cp _ => simp at hsOk
            | text str b0 =>
              dsimp only at hsOk
              cases hchL : str.toList with
              | nil => rw [hchL] at hsOk; cases hsOk
              | cons ch chTl =>
                rw [hchL, beq_iff_eq] at hsOk
                subst hsOk
                cases hseq with
                | @term _ _ _ _ _ _ _ h _ _ _ ht hr =>
                  have hhb := (code_step_bounds hok (treeSize.treeListSize _)).2 (Nat.le_refl _)
                    (fun x hx => hneAll x (List.mem_cons_of_mem _ hx)) hr
                  dsimp only [codeAlphabet] at ht
                  rw [hchL, List.map_cons] at ht
                  have hlt := (slice_nonempty_imp_lt (by rw [ht]; exact List.cons_ne_nil _ _)).1
                  have hg := slice_getElem? inp (lo := a) (hi := h) (k := 0) (by omega)
                  rw [ht, Nat.add_zero] at hg
                  exact hg.symm
      | _ => simp at hsOk

private theorem lex_derives_starts_brace (hok : parseTablesOk = true) {cx : Ctx} {inp : List Nat}
    {m : NT} (hm : m = .RightBracePunctuator ∨ m = .TemplateMiddle ∨ m = .TemplateTail)
    {a b : Nat} (hb : b ≤ inp.length) {t : Tree}
    (hd : Derives Ecma.Spec.gl cx .lexical (codeAlphabet Engine.Model.codePrims) inp m [] a b t) :
    inp[a]? = some 0x7D := by
  have hcx2 := List.all_eq_true.mp lexFirstCharCert_true
    (if Lex.html cx then cxHtmlTrue else cxHtmlFalse) (lexCertCx_mem cx)
  have hmMem : m ∈ [NT.RightBracePunctuator, .TemplateMiddle, .TemplateTail] := by
    rcases hm with rfl | rfl | rfl <;> decide
  have hmOk := List.all_eq_true.mp (Bool.and_eq_true_iff.mp hcx2).2 m hmMem
  obtain ⟨K, hK⟩ := hd
  have hs := hK (max K 1) (Nat.le_max_left K 1)
  obtain ⟨k0, hk0⟩ : ∃ k0, max K 1 = k0 + 1 := ⟨max K 1 - 1, by omega⟩
  rw [hk0] at hs
  cases hs with
  | lex _ _ hl => nomatch hl
  | node s hsMem _ _ hseq =>
    have hsG := hsMem; rw [alts_lexical_eq cx m] at hsG
    have hsOk := List.all_eq_true.mp hmOk s hsG
    have hneAll : ∀ it ∈ s.alt.rhs, itemTermNonEmpty it = true :=
      fun it hit => item_term_nonempty_of_alts hok hsMem hit
    unfold rhsStartsChar at hsOk
    generalize hrhs : s.alt.rhs = rhs0 at hsOk hseq hneAll
    cases rhs0 with
    | nil => simp at hsOk
    | cons it rest =>
      cases it with
      | sym s0 o0 =>
        cases o0 with
        | true => cases s0 <;> simp at hsOk
        | false =>
          cases s0 with
          | nt _ _ => simp at hsOk
          | t tx0 =>
            cases tx0 with
            | cp _ => simp at hsOk
            | text str b0 =>
              dsimp only at hsOk
              cases hchL : str.toList with
              | nil => rw [hchL] at hsOk; cases hsOk
              | cons ch chTl =>
                rw [hchL, beq_iff_eq] at hsOk
                subst hsOk
                cases hseq with
                | @term _ _ _ _ _ _ _ h _ _ _ ht hr =>
                  have hhb := (code_step_bounds hok (treeSize.treeListSize _)).2 (Nat.le_refl _)
                    (fun x hx => hneAll x (List.mem_cons_of_mem _ hx)) hr
                  dsimp only [codeAlphabet] at ht
                  rw [hchL, List.map_cons] at ht
                  have hlt := (slice_nonempty_imp_lt (by rw [ht]; exact List.cons_ne_nil _ _)).1
                  have hg := slice_getElem? inp (lo := a) (hi := h) (k := 0) (by omega)
                  rw [ht, Nat.add_zero] at hg
                  exact hg.symm
      | _ => simp at hsOk

private theorem retag_hashbang_first_token (hok : parseTablesOk = true) {cx : Ctx}
    {src : List Nat} {b0 : Nat} (_hb0Pos : 0 < b0) (hb0Le : b0 ≤ src.length)
    {lg : NT} (hlg : lg = .InputElementDiv ∨ lg = .InputElementRegExp)
    (hno7d : src[0]? ≠ some 0x7D)
    (h2fImp : src[0]? = some 0x2F → lg = .InputElementRegExp)
    {tr0 : Tree}
    (hisTok0 : Element.isToken ⟨0, b0, .InputElementHashbangOrRegExp, tr0⟩ = true)
    (hder0 : Derives Ecma.Spec.gl cx .lexical (codeAlphabet Engine.Model.codePrims) src
      .InputElementHashbangOrRegExp [] 0 b0 tr0)
    (hmax0 : ∀ h, b0 < h → h ≤ src.length →
      ¬ ∃ t, Derives Ecma.Spec.gl cx .lexical (codeAlphabet Engine.Model.codePrims) src
        .InputElementHashbangOrRegExp [] 0 h t) :
    ∃ trLg,
      Element.isToken ⟨0, b0, lg, trLg⟩ = true ∧
      Derives Ecma.Spec.gl cx .lexical (codeAlphabet Engine.Model.codePrims) src lg [] 0 b0 trLg ∧
      (∀ h, b0 < h → h ≤ src.length →
        ¬ ∃ t, Derives Ecma.Spec.gl cx .lexical (codeAlphabet Engine.Model.codePrims) src lg [] 0 h t) ∧
      trLg.has .NumericLiteral 0 b0 = tr0.has .NumericLiteral 0 b0 := by
  let cs := src.toArray
  have hcsList : cs.toList = src := by simp [cs]
  have hcsSz : cs.size = src.length := by simp [cs]
  have hcs0 : src[0]? = cs[0]? := by rw [← hcsList]; simp
  have hlgGoal : isLexGoal lg = true := by rcases hlg with rfl | rfl <;> rfl
  have hhbGoal : isLexGoal .InputElementHashbangOrRegExp = true := rfl
  have hb0Cs : b0 ≤ cs.size := hcsSz ▸ hb0Le
  have hder0Cs : Derives Ecma.Spec.gl cx .lexical (codeAlphabet Engine.Model.codePrims) cs.toList
      .InputElementHashbangOrRegExp [] 0 b0 tr0 := hcsList ▸ hder0
  rcases unpackInputElement hok hhbGoal hb0Cs hder0Cs with ⟨hnT, _⟩ | ⟨_, cls, hclsHB, dtCls, hplCls, hhas0⟩
  · rw [hisTok0] at hnT; cases hnT
  · have hclsLg : cls ∈ Lex.classes lg := by
      unfold Lex.classes at hclsHB ⊢
      rw [List.mem_append] at hclsHB ⊢
      rcases hclsHB with hcom | hhbR
      · exact Or.inl hcom
      · simp only [List.mem_singleton] at hhbR
        subst hhbR
        have ⟨_, hclsLe, hderCls⟩ := lexPlain_to_derives hok (Nat.zero_le _) hplCls
        have h2f : src[0]? = some 0x2F :=
          hcsList ▸ lex_derives_starts_slash hok (Or.inr rfl) (hcsList ▸ hcsSz ▸ hclsLe) hderCls
        rw [h2fImp h2f]
        exact Or.inr (by decide)
    obtain ⟨trLg, hderLgCs, hisTokLg, hhasLg⟩ := packToken hok hlgGoal hclsLg (Nat.zero_le _) hplCls
    refine ⟨trLg, hisTokLg, hcsList ▸ hderLgCs, fun h hbh hhLe ⟨t', hdt'⟩ => ?_, hhasLg.trans hhas0.symm⟩
    have hhCs : h ≤ cs.size := hcsSz ▸ hhLe
    have hdt'Cs : Derives Ecma.Spec.gl cx .lexical (codeAlphabet Engine.Model.codePrims) cs.toList lg [] 0 h t' :=
      hcsList ▸ hdt'
    rcases unpackInputElement hok hlgGoal hhCs hdt'Cs with ⟨_, _, hnt⟩ | ⟨_, cls', hcls'Lg, dt', hpl', _⟩
    · have hexHB : ∃ trHB, Derives Ecma.Spec.gl cx .lexical (codeAlphabet Engine.Model.codePrims) cs.toList
          .InputElementHashbangOrRegExp [] 0 h trHB := by
        rcases hnt with ⟨_, _, hdW⟩ | ⟨_, _, hdL⟩ | ⟨_, _, hdC⟩ | ⟨hlgEq, _⟩ | ⟨hlgEq, _⟩
        · obtain ⟨tr, hdr, _, _, _⟩ := packNonToken hok hhbGoal (Nat.zero_le _) (Or.inl rfl) hdW
          exact ⟨tr, hdr⟩
        · obtain ⟨tr, hdr, _, _, _⟩ := packNonToken hok hhbGoal (Nat.zero_le _) (Or.inr (Or.inl rfl)) hdL
          exact ⟨tr, hdr⟩
        · obtain ⟨tr, hdr, _, _, _⟩ := packNonToken hok hhbGoal (Nat.zero_le _) (Or.inr (Or.inr (Or.inl rfl))) hdC
          exact ⟨tr, hdr⟩
        · rcases hlg with rfl | rfl <;> cases hlgEq
        · rcases hlg with rfl | rfl <;> cases hlgEq
      obtain ⟨trHB, hdrHB⟩ := hexHB
      exact hmax0 h hbh hhLe ⟨trHB, hcsList ▸ hdrHB⟩
    · have ⟨_, hh'Le, hderCls'⟩ := lexPlain_to_derives hok (Nat.zero_le _) hpl'
      have hcls'HB : cls' ∈ Lex.classes .InputElementHashbangOrRegExp := by
        unfold Lex.classes at hcls'Lg ⊢
        rw [List.mem_append] at hcls'Lg ⊢
        rcases hcls'Lg with hcom | hrest
        · exact Or.inl hcom
        · rcases hlg with rfl | rfl
          · simp only [List.mem_cons, List.not_mem_nil, or_false] at hrest
            rcases hrest with rfl | rfl
            · have h2f : src[0]? = some 0x2F :=
                hcsList ▸ lex_derives_starts_slash hok (Or.inl rfl) (hcsList ▸ hcsSz ▸ hh'Le) hderCls'
              exact nomatch (h2fImp h2f)
            · have h7d : src[0]? = some 0x7D :=
                hcsList ▸ lex_derives_starts_brace hok (Or.inl rfl) (hcsList ▸ hcsSz ▸ hh'Le) hderCls'
              exact absurd h7d hno7d
          · simp only [List.mem_cons, List.not_mem_nil, or_false] at hrest
            rcases hrest with rfl | rfl
            · have h7d : src[0]? = some 0x7D :=
                hcsList ▸ lex_derives_starts_brace hok (Or.inl rfl) (hcsList ▸ hcsSz ▸ hh'Le) hderCls'
              exact absurd h7d hno7d
            · exact Or.inr (by decide)
      obtain ⟨trHB, hdrHB, _, _⟩ := packToken hok hhbGoal hcls'HB (Nat.zero_le _) hpl'
      exact hmax0 h hbh hhLe ⟨trHB, hcsList ▸ hdrHB⟩

def shiftElem (lo : Nat) (e : Element) : Element :=
  ⟨e.i - lo, e.j - lo, e.goal, shiftCodeTree lo e.tree⟩

private theorem shiftElem_kind (lo : Nat) (e : Element) :
    (shiftElem lo e).kind = e.kind := by
  unfold shiftElem Element.kind
  cases e.tree with
  | leaf _ _ => rw [shiftCodeTree_leaf]
  | lex _ _ => rw [shiftCodeTree_lex]
  | node _ _ _ _ _ ks =>
    rw [shiftCodeTree_node]
    cases ks with
    | nil => rfl
    | cons k1 rest =>
      cases rest with
      | nil => dsimp only [List.map]; exact shiftCodeTree_nt? lo k1
      | cons _ _ => rfl

private theorem shiftElem_isToken (lo : Nat) (e : Element) :
    (shiftElem lo e).isToken = e.isToken := by
  unfold Element.isToken; rw [shiftElem_kind]

private theorem shiftElem_breaks {fullSrc : List Nat} {lo hi : Nat} {e : Element}
    (ha : lo ≤ e.i) (hb : e.j ≤ hi) :
    (shiftElem lo e).breaks (slice fullSrc lo hi) = e.breaks fullSrc := by
  unfold Element.breaks
  rw [shiftElem_kind]
  dsimp only [shiftElem]
  rw [slice_of_slice fullSrc ha hb]

private theorem list_attach_any_eq {α : Type} (xs : List α) (f : α → Bool) :
    (xs.attach.any fun ⟨x, _⟩ => f x) = xs.any f := by
  induction xs with
  | nil => rfl
  | cons x tl ih =>
    simp only [List.attach_cons, List.any_cons, List.any_map]
    congr 1

private theorem code_step_has_shift (hok : parseTablesOk = true) {cx : Ctx} {P : CodePrims} {g : GrammarId}
    {neg : NT → List Param → Nat → Nat → Prop} {inp : List Nat} {lo : Nat} :
    ∀ (sz : Nat),
      (∀ {m ps a0 b0 u}, treeSize u ≤ sz → lo ≤ a0 →
        Step (codeAlphabet P) neg inp Ecma.Spec.gl cx g m ps a0 b0 u →
        ∀ {i j : Nat}, lo ≤ i → lo ≤ j →
          (shiftCodeTree lo u).has .NumericLiteral (i - lo) (j - lo) = u.has .NumericLiteral i j) ∧
      (∀ {s ps k is a0 b0 mask ts}, treeSize.treeListSize ts ≤ sz → lo ≤ a0 →
        (∀ it ∈ is, itemTermNonEmpty it = true) →
        Ecma.Grammar.Seq (codeAlphabet P) neg inp Ecma.Spec.gl cx g s ps k is a0 b0 mask ts →
        ∀ {i j : Nat}, lo ≤ i → lo ≤ j →
          (ts.map (shiftCodeTree lo)).any (fun x => x.has .NumericLiteral (i - lo) (j - lo)) =
            ts.any (fun x => x.has .NumericLiteral i j)) := by
  intro sz
  induction sz using Nat.strongRecOn with
  | ind sz ih =>
    have hst : ∀ {m ps a0 b0 u}, treeSize u ≤ sz → lo ≤ a0 →
        Step (codeAlphabet P) neg inp Ecma.Spec.gl cx g m ps a0 b0 u →
        ∀ {i j : Nat}, lo ≤ i → lo ≤ j →
          (shiftCodeTree lo u).has .NumericLiteral (i - lo) (j - lo) = u.has .NumericLiteral i j := by
      intro m ps a0 b0 u hsz ha0 hs i j hi hj
      cases hs with
      | lex _ _ hl => nomatch hl
      | @node _ _ _ _ _ kids id s hsMem _ _ hseq =>
        dsimp only [treeSize] at hsz
        have hab0 := (code_step_bounds hok (treeSize.treeListSize kids)).2 (Nat.le_refl _)
          (fun it hit => item_term_nonempty_of_alts hok hsMem hit) hseq
        rw [shiftCodeTree_node, Tree.has, Tree.has, list_attach_any_eq, list_attach_any_eq]
        have heq1 : (a0 - lo == i - lo) = (a0 == i) := by
          apply Bool.eq_iff_iff.mpr; simp only [beq_iff_eq]; omega
        have heq2 : (b0 - lo == j - lo) = (b0 == j) := by
          apply Bool.eq_iff_iff.mpr; simp only [beq_iff_eq]; omega
        rw [heq1, heq2,
            (ih _ (by omega)).2 (Nat.le_refl _) ha0 (fun it hit => item_term_nonempty_of_alts hok hsMem hit) hseq hi hj]
    refine ⟨hst, ?_⟩
    intro s ps k is
    induction is generalizing k with
    | nil => intro _ _ _ _ _ _ _ hs _ _ _ _; cases hs; rfl
    | cons y ys ihr =>
      intro a0 b0 mask ts hsz ha0 hne hs i j hi hj
      have hneY := hne y (List.mem_cons_self ..)
      have hneYs : ∀ x ∈ ys, itemTermNonEmpty x = true :=
        fun x hx => hne x (List.mem_cons_of_mem _ hx)
      cases hs with
      | absent hr | look _ hr | noLT _ hr | empty hr | onlyIf hr =>
        exact ihr hsz ha0 hneYs hr hi hj
      | @term _ _ _ x _ _ _ h _ _ _ ht hr =>
        dsimp only [treeSize.treeListSize, treeSize] at hsz
        have hlt := (slice_nonempty_imp_lt (code_term_nonempty (itemTermNonEmpty_sym hneY) ht)).1
        simp only [List.map_cons, shiftCodeTree_leaf, List.any_cons, Tree.has, Bool.false_or]
        exact ihr (by omega) (by omega) hneYs hr hi hj
      | @butNotT _ _ _ x _ _ _ h _ _ _ ht _ hr =>
        dsimp only [treeSize.treeListSize, treeSize] at hsz
        have hlt := (slice_nonempty_imp_lt (code_term_nonempty (itemTermNonEmpty_butNot hneY) ht)).1
        simp only [List.map_cons, shiftCodeTree_leaf, List.any_cons, Tree.has, Bool.false_or]
        exact ihr (by omega) (by omega) hneYs hr hi hj
      | @phrase _ _ _ _ _ _ h _ _ _ hp hr =>
        dsimp only [treeSize.treeListSize, treeSize] at hsz
        obtain ⟨_, hw, _⟩ := hp
        have hlt := (slice_nonempty_imp_lt (by rw [hw]; exact List.cons_ne_nil _ _)).1
        simp only [List.map_cons, shiftCodeTree_leaf, List.any_cons, Tree.has, Bool.false_or]
        exact ihr (by omega) (by omega) hneYs hr hi hj
      | @nt _ _ _ _ _ _ _ _ h _ _ t0 _ hs0 _ hr =>
        dsimp only [treeSize.treeListSize] at hsz
        have hah := (code_step_bounds hok (treeSize t0)).1 (Nat.le_refl _) hs0 |>.1
        dsimp only [List.map, List.any]
        rw [hst (by omega) ha0 hs0 hi hj, ihr (by omega) (by omega) hneYs hr hi hj]
      | @butNotN _ _ _ _ _ _ _ _ h _ _ t0 _ hs0 _ hr =>
        dsimp only [treeSize.treeListSize] at hsz
        have hah := (code_step_bounds hok (treeSize t0)).1 (Nat.le_refl _) hs0 |>.1
        dsimp only [List.map, List.any]
        rw [hst (by omega) ha0 hs0 hi hj, ihr (by omega) (by omega) hneYs hr hi hj]

def clearHeadLT : List Token → List Token
  | [] => []
  | t0 :: rest => { t0 with lt := false } :: rest

private theorem clearHeadLT_length (ts : List Token) :
    (clearHeadLT ts).length = ts.length := by
  cases ts <;> rfl

private theorem clearHeadLT_getElem?_text_virt (ts : List Token) (k : Nat) :
    ((clearHeadLT ts)[k]?.map Token.text) = (ts[k]?.map Token.text) ∧
    ((clearHeadLT ts)[k]?.map Token.virt) = (ts[k]?.map Token.virt) := by
  cases ts with
  | nil => exact ⟨rfl, rfl⟩
  | cons t0 rest => cases k <;> simp [clearHeadLT]

private theorem clearHeadLT_getElem?_pos (ts : List Token) {k : Nat} (hk : 0 < k) :
    (clearHeadLT ts)[k]? = ts[k]? := by
  cases ts with
  | nil => rfl
  | cons t0 rest => obtain ⟨k0, rfl⟩ : ∃ k0, k = k0 + 1 := ⟨k - 1, by omega⟩; rfl

private theorem clearHeadLT_getElem?_zero {t0 : Token} {rest : List Token} :
    (clearHeadLT (t0 :: rest))[0]? = some { t0 with lt := false } := rfl

private theorem clearHeadLT_filter_isNone_of_head_real {t0 : Token} {rest : List Token}
    (ht0 : t0.virt = none) :
    (clearHeadLT (t0 :: rest)).filter (·.virt.isNone) =
      clearHeadLT ((t0 :: rest).filter (·.virt.isNone)) := by
  simp [clearHeadLT, ht0]

private theorem countP_isNone_eq_filter_len (ts : List Token) :
    ts.countP (·.virt.isNone) = (ts.filter (·.virt.isNone)).length := by
  rw [List.countP_eq_length_filter]

private theorem filter_idx_real_tok :
    ∀ (toks : List Token) {k : Nat} {tk : Token},
      toks[k]? = some tk → tk.virt = none →
      let r := (toks.take k).countP (·.virt.isNone)
      (toks.take (k + 1)).countP (·.virt.isNone) = r + 1 ∧
      (toks.filter (·.virt.isNone))[r]? = some tk ∧
      realIdx r toks = k := by
  intro toks
  induction toks with
  | nil => intro k _ hk; simp at hk
  | cons hd tl ih =>
    intro k tk hk hv
    cases k with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hk
      subst hk
      simp [hv, realIdx]
    | succ k0 =>
      simp only [List.getElem?_cons_succ] at hk
      obtain ⟨hc1, hflt, hridx⟩ := ih hk hv
      cases hhd : hd.virt with
      | none =>
        simp only [List.take_succ_cons, List.countP_cons, hhd, Option.isNone_none, ↓reduceIte,
          List.filter_cons]
        refine ⟨by omega, ?_, ?_⟩
        · rw [show (tl.take k0).countP (·.virt.isNone) + 1 = ((tl.take k0).countP (·.virt.isNone)).succ from rfl,
              List.getElem?_cons_succ]
          exact hflt
        · simp only [realIdx, hhd, Option.isNone_none, ↓reduceIte, hridx]; omega
      | some w =>
        simp only [List.take_succ_cons, List.countP_cons, hhd, Option.isNone_some, Bool.false_eq_true, ↓reduceIte,
          List.filter_cons]
        refine ⟨hc1, hflt, ?_⟩
        cases hr0 : (tl.take k0).countP (·.virt.isNone) with
        | zero => simp only [realIdx, hhd, Option.isNone_some, Bool.false_eq_true, ↓reduceIte, hr0 ▸ hridx]; omega
        | succ m => simp only [realIdx, hhd, Option.isNone_some, Bool.false_eq_true, ↓reduceIte, hr0 ▸ hridx]; omega

private theorem countP_take_mono (p : Token → Bool) (toks : List Token) {a b : Nat} (hab : a ≤ b) :
    (toks.take a).countP p ≤ (toks.take b).countP p := by
  have hsplit : toks.take b = toks.take a ++ (toks.drop a).take (b - a) := by
    rw [← List.take_append_drop a (toks.take b), List.take_take, Nat.min_eq_left hab,
        List.drop_take]
  rw [hsplit, List.countP_append]; omega

private theorem countP_clearHeadLT_slice (toks : List Token) {i j u : Nat}
    (_hij : i ≤ j) (_hj : j ≤ toks.length) (hu : u ≤ j - i) :
    ((clearHeadLT (slice toks i j)).take u).countP (·.virt.isNone) +
      (toks.take i).countP (·.virt.isNone) =
      (toks.take (i + u)).countP (·.virt.isNone) := by
  have hvirtEq : ∀ (xs : List Token) (n : Nat),
      ((clearHeadLT xs).take n).countP (·.virt.isNone) = (xs.take n).countP (·.virt.isNone) := by
    intro xs n
    cases xs with
    | nil => rfl
    | cons x0 xr =>
      cases n with
      | zero => rfl
      | succ n0 => simp [clearHeadLT, List.take_succ_cons, List.countP_cons]
  rw [hvirtEq]
  have hslTake : (slice toks i j).take u = (toks.drop i).take u := by
    unfold slice; rw [List.take_take, Nat.min_eq_left hu]
  rw [hslTake]
  have hsplit : toks.take (i + u) = toks.take i ++ (toks.drop i).take u := by
    have hiu : i ≤ i + u := by omega
    rw [← List.take_append_drop i (toks.take (i + u)), List.take_take, Nat.min_eq_left hiu,
        List.drop_take]
    simp
  rw [hsplit, List.countP_append]; omega

private theorem filter_slice_toks (toks : List Token) {i j : Nat}
    (hij : i ≤ j) (_hj : j ≤ toks.length) :
    (slice toks i j).filter (·.virt.isNone) =
      slice (toks.filter (·.virt.isNone))
        ((toks.take i).countP (·.virt.isNone))
        ((toks.take j).countP (·.virt.isNone)) := by
  have h1 : toks = toks.take i ++ (slice toks i j ++ toks.drop j) := by
    unfold slice
    have hdrop : toks.drop i = (toks.drop i).take (j - i) ++ (toks.drop i).drop (j - i) :=
      (List.take_append_drop (j - i) (toks.drop i)).symm
    rw [List.drop_drop, show i + (j - i) = j from by omega] at hdrop
    rw [← hdrop, List.take_append_drop]
  have h2 : toks.take j = toks.take i ++ slice toks i j := by
    unfold slice
    rw [← List.take_append_drop i (toks.take j), List.take_take, Nat.min_eq_left hij, List.drop_take]
  have hf1 : toks.filter (·.virt.isNone) =
      (toks.take i).filter (·.virt.isNone) ++
      ((slice toks i j).filter (·.virt.isNone) ++ (toks.drop j).filter (·.virt.isNone)) := by
    conv => lhs; rw [h1]
    simp [List.filter_append]
  have ha : (toks.take i).countP (·.virt.isNone) = ((toks.take i).filter (·.virt.isNone)).length :=
    List.countP_eq_length_filter ..
  have hb : (toks.take j).countP (·.virt.isNone) =
      ((toks.take i).filter (·.virt.isNone)).length + ((slice toks i j).filter (·.virt.isNone)).length := by
    rw [List.countP_eq_length_filter, h2, List.filter_append, List.length_append]
  change (slice toks i j).filter (·.virt.isNone) =
    ((toks.filter (·.virt.isNone)).drop ((toks.take i).countP (·.virt.isNone))).take
      ((toks.take j).countP (·.virt.isNone) - (toks.take i).countP (·.virt.isNone))
  rw [ha, hb, hf1, List.drop_append, Nat.sub_self, List.drop_length, List.nil_append, List.drop_zero]
  have hsub : ((toks.take i).filter (·.virt.isNone)).length + ((slice toks i j).filter (·.virt.isNone)).length -
      ((toks.take i).filter (·.virt.isNone)).length = ((slice toks i j).filter (·.virt.isNone)).length := by omega
  rw [hsub, List.take_append, Nat.sub_self, List.take_length, List.take_zero, List.append_nil]

private theorem tokensOf_map_es (src : List Nat) (els : List Element) :
    (tokensOf src els).length = (els.filter Element.isToken).length ∧
    ∀ (r : Nat), (tokensOf src els)[r]? =
      (els.zipIdx.filter (fun p => p.1.isToken))[r]?.map (fun (p : Element × Nat) =>
        let before := (els.take p.2).reverse.takeWhile (fun (x : Element) => !x.isToken)
        ({ text := slice src p.1.i p.1.j, lt := before.any (·.breaks src), virt := none } : Token)) := by
  unfold tokensOf
  have hfst : (els.zipIdx.filter (fun p => p.1.isToken)).map Prod.fst = els.filter Element.isToken := by
    have hgen : ∀ (l : List Element) (n : Nat),
        ((l.zipIdx n).filter (fun p => p.1.isToken)).map Prod.fst = l.filter Element.isToken := by
      intro l; induction l with
      | nil => intro _; rfl
      | cons e tl ih =>
        intro n; rw [List.zipIdx_cons, List.filter_cons, List.filter_cons]
        cases e.isToken <;> simp [ih (n + 1)]
    exact hgen els 0
  refine ⟨by rw [List.length_map, ← List.length_map (f := Prod.fst), hfst], fun r => by rw [List.getElem?_map]⟩

private theorem zipIdx_filter_isToken_props (els : List Element) :
    ((els.zipIdx.filter (fun p => p.1.isToken)).map Prod.fst = els.filter Element.isToken) ∧
    (∀ r ek, (els.zipIdx.filter (fun p => p.1.isToken))[r]? = some ek →
      ek.2 < els.length ∧ els[ek.2]? = some ek.1 ∧ ek.1.isToken = true ∧
      (els.take ek.2).filter Element.isToken = (els.filter Element.isToken).take r) := by
  have hgen : ∀ (l : List Element) (off : Nat),
      (((l.zipIdx off).filter (fun p => p.1.isToken)).map Prod.fst = l.filter Element.isToken) ∧
      (∀ r ek, ((l.zipIdx off).filter (fun p => p.1.isToken))[r]? = some ek →
        off ≤ ek.2 ∧ ek.2 < off + l.length ∧ l[ek.2 - off]? = some ek.1 ∧ ek.1.isToken = true ∧
        (l.take (ek.2 - off)).filter Element.isToken = (l.filter Element.isToken).take r) := by
    intro l
    induction l with
    | nil => intro off; exact ⟨rfl, fun r _ h => by simp at h⟩
    | cons e tl ih =>
      intro off
      obtain ⟨hfst, hget⟩ := ih (off + 1)
      refine ⟨by rw [List.zipIdx_cons, List.filter_cons, List.filter_cons]; cases e.isToken <;> simp [hfst], ?_⟩
      intro r ek hr
      rw [List.zipIdx_cons, List.filter_cons] at hr
      cases heT : e.isToken with
      | false =>
        simp only [heT, Bool.false_eq_true, ↓reduceIte] at hr
        obtain ⟨hle, hlt, hg, ht, htk⟩ := hget r ek hr
        have hsub : ek.2 - off = (ek.2 - (off + 1)) + 1 := by omega
        refine ⟨by omega, by simp [List.length_cons]; omega, ?_, ht, ?_⟩
        · rw [hsub, List.getElem?_cons_succ]; exact hg
        · rw [hsub, List.take_succ_cons, List.filter_cons_of_neg (by simp [heT]),
              List.filter_cons_of_neg (by simp [heT])]
          exact htk
      | true =>
        simp only [heT, ↓reduceIte] at hr
        cases r with
        | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hr
          subst hr
          simp [heT]
        | succ r0 =>
          simp only [List.getElem?_cons_succ] at hr
          obtain ⟨hle, hlt, hg, ht, htk⟩ := hget r0 ek hr
          have hsub : ek.2 - off = (ek.2 - (off + 1)) + 1 := by omega
          refine ⟨by omega, by simp [List.length_cons]; omega, ?_, ht, ?_⟩
          · rw [hsub, List.getElem?_cons_succ]; exact hg
          · rw [hsub, List.take_succ_cons, List.filter_cons_of_pos heT,
                List.filter_cons_of_pos heT, List.take_succ_cons, htk]
  obtain ⟨h1, h2⟩ := hgen els 0
  exact ⟨h1, fun r ek hr => by
    obtain ⟨_, hlt, hg, ht, htk⟩ := h2 r ek hr
    rw [Nat.zero_add] at hlt
    rw [Nat.sub_zero] at hg htk
    exact ⟨hlt, hg, ht, htk⟩⟩

private theorem scans_elem_ordered {cx : Ctx} {P : CodePrims} {src : List Nat} {els : List Element}
    (hsc : Scans Ecma.Spec.gl cx P src els) :
    (∀ (k : Nat) (e : Element), els[k]? = some e →
      e.i < e.j ∧ e.j ≤ src.length ∧
      (k = 0 → e.i = 0) ∧
      (∀ (k0 : Nat) (e0 : Element), k = k0 + 1 → els[k0]? = some e0 → e.i = e0.j)) ∧
    (∀ (k1 k2 : Nat) (e1 e2 : Element), k1 ≤ k2 → els[k1]? = some e1 → els[k2]? = some e2 →
      e1.i ≤ e2.i ∧ (k1 < k2 → e1.j ≤ e2.i)) := by
  obtain ⟨hzip, hlast, hall⟩ := hsc
  have hstep : ∀ k (hk : k < els.length),
      els[k].i = (if k == 0 then 0 else (els[k - 1]?.map (·.j)).getD 0) ∧
      els[k].i < els[k].j := by
    intro k hk
    have hmemZ : (els[k], k) ∈ els.zipIdx := by
      have hgen : ∀ (l : List Element) (off idx : Nat) (h : idx < l.length),
          (l[idx], off + idx) ∈ l.zipIdx off := by
        intro l; induction l with
        | nil => intro _ _ h; nomatch h
        | cons x xs ih =>
          intro off idx h
          cases idx with
          | zero => simp [List.zipIdx_cons]
          | succ m =>
            rw [List.zipIdx_cons]
            exact List.mem_cons_of_mem _ (by
              have hm := ih (off + 1) m (by simp at h; omega)
              rwa [show off + 1 + m = off + (m + 1) from by omega] at hm)
      simpa using hgen els 0 k hk
    have hzOk := beq_iff_eq.mp (List.all_eq_true.mp hzip _ hmemZ)
    exact ⟨hzOk, (hall els[k] (List.getElem_mem hk)).1⟩
  have hord : ∀ k1 k2 (hk1 : k1 < els.length) (hk2 : k2 < els.length), k1 ≤ k2 →
      els[k1].i ≤ els[k2].i ∧ (k1 < k2 → els[k1].j ≤ els[k2].i) := by
    intro k1 k2
    induction k2 with
    | zero =>
      intro hk1 hk2 hle
      obtain rfl : k1 = 0 := by omega
      exact ⟨Nat.le_refl _, fun h => by omega⟩
    | succ m ih =>
      intro hk1 hk2 hle
      have hmLt : m < els.length := by omega
      obtain ⟨hstepM1, _⟩ := hstep (m + 1) hk2
      have hm1Eq : els[m + 1].i = els[m].j := by
        simpa [List.getElem?_eq_getElem hmLt] using hstepM1
      have hmIj := (hstep m hmLt).2
      by_cases heq : k1 = m + 1
      · subst heq; exact ⟨Nat.le_refl _, fun h => by omega⟩
      · obtain ⟨hiLe, hjLe⟩ := ih (by omega) hmLt (by omega)
        refine ⟨by omega, fun _ => ?_⟩
        by_cases hk1m : k1 = m
        · subst hk1m; omega
        · have := hjLe (by omega); omega
  have hjBound : ∀ k (hk : k < els.length), els[k].j ≤ src.length := by
    intro k hk
    have hne : els ≠ [] := List.ne_nil_of_length_pos (by omega)
    have hlastIdx : els.length - 1 < els.length := by omega
    rw [List.getLast?_eq_some_getLast hne, List.getLast_eq_getElem hne] at hlast
    simp only [Option.map_some, Option.getD_some] at hlast
    by_cases heq : k = els.length - 1
    · subst heq; omega
    · have hjLe := (hord k (els.length - 1) hk hlastIdx (by omega)).2 (by omega)
      have hlastLt := (hstep (els.length - 1) hlastIdx).2
      omega
  refine ⟨fun k e hk => ?_, fun k1 k2 e1 e2 hle hk1 hk2 => ?_⟩
  · obtain ⟨hkLt, rfl⟩ := List.getElem?_eq_some_iff.mp hk
    obtain ⟨hstK, hijK⟩ := hstep k hkLt
    refine ⟨hijK, hjBound k hkLt, fun hk0 => by subst hk0; simpa using hstK, fun k0 e0 hkEq he0 => ?_⟩
    subst hkEq
    simpa [he0] using hstK
  · obtain ⟨hk1Lt, rfl⟩ := List.getElem?_eq_some_iff.mp hk1
    obtain ⟨hk2Lt, rfl⟩ := List.getElem?_eq_some_iff.mp hk2
    exact hord k1 k2 hk1Lt hk2Lt hle

/-! ## Section 5: Syntactic Helpers (`realStart`, `exprFirstSafe`, `shiftSynTree`, `checkNode`, `Relabel.shift`) -/

def shiftSynTree (off : Nat) : Tree → Tree
  | .leaf a b => .leaf (a - off) (b - off)
  | .lex k t => .lex (k - off) t
  | .node n id ps a b ks => .node n id ps (a - off) (b - off) (ks.map (shiftSynTree off))

@[simp] private theorem shiftSynTree_leaf (off a b : Nat) :
    shiftSynTree off (.leaf a b) = .leaf (a - off) (b - off) := by rw [shiftSynTree]

@[simp] private theorem shiftSynTree_lex (off k : Nat) (t : Tree) :
    shiftSynTree off (.lex k t) = .lex (k - off) t := by rw [shiftSynTree]

@[simp] private theorem shiftSynTree_node (off : Nat) (n : NT) (id : Nat) (ps : List Param)
    (a b : Nat) (ks : List Tree) :
    shiftSynTree off (.node n id ps a b ks) = .node n id ps (a - off) (b - off) (ks.map (shiftSynTree off)) := by
  rw [shiftSynTree]

private theorem shiftSynTree_isLeaf (off : Nat) (t : Tree) :
    (shiftSynTree off t).isLeaf = t.isLeaf := by
  cases t <;> simp [Tree.isLeaf]

private theorem shiftSynTree_nt? (off : Nat) (t : Tree) :
    (shiftSynTree off t).nt? = t.nt? := by
  cases t <;> simp [Tree.nt?]

private theorem syn_term_step_one {cx : Ctx} {P : CodePrims} {toks : List Token}
    {s : Src} {k : Nat} {x : Terminal} {a h : Nat}
    (ht : (tokenAlphabet Ecma.Spec.gl cx P).term s k x (slice toks a h)) :
    a < h ∧ (h ≤ toks.length → h = a + 1) ∧
    ∃ str b tok, x = .text str b ∧ toks[a]? = some tok ∧ tok.text = str.toList.map Char.toNat ∧
      (tokenAlphabet Ecma.Spec.gl cx P).term s k (.text str b) [tok] := by
  dsimp only [tokenAlphabet] at ht
  cases x with
  | cp _ => nomatch ht
  | text str b =>
    cases hsc : slice toks a h with
    | nil => rw [hsc] at ht; nomatch ht
    | cons tok rest =>
      rw [hsc] at ht
      cases rest with
      | cons _ _ => nomatch ht
      | nil =>
        have hlt := (slice_nonempty_imp_lt (by rw [hsc]; exact List.cons_ne_nil _ _)).1
        have hg := slice_getElem? toks (lo := a) (hi := h) (k := 0) (by omega)
        rw [hsc, Nat.add_zero] at hg
        simp only [List.getElem?_cons_zero] at hg
        refine ⟨hlt, fun hhLe => ?_, str, b, tok, rfl, hg.symm, ht.1, show (tokenAlphabet Ecma.Spec.gl cx P).term s k (.text str b) [tok] from ⟨ht.1, ht.2⟩⟩
        have hslLen := slice_length_eq toks (Nat.le_of_lt hlt) hhLe
        rw [hsc] at hslLen; simp at hslLen; omega

private theorem posSynStep_real_start {cx : Ctx} {P : CodePrims} {toks : List Token} :
    ∀ (sz : Nat),
      (∀ {m ps a b t}, treeSize t ≤ sz →
        realStartNTs.contains m = true →
        Strict.PosSynStep cx P toks m ps a b t →
        a < b ∧ ∃ tf, toks[a]? = some tf ∧ tf.virt = none) ∧
      (∀ {n s ps k is a b mask ts}, treeSize.treeListSize ts ≤ sz →
        s ∈ Ecma.Spec.gl.alts cx .syntactic n →
        (∀ idx < is.length, s.alt.rhs[k + idx]? = is[idx]?) →
        rhsHasRealStart cx realStartNTs is = true →
        Strict.PosSynSeq cx P toks s ps k is a b mask ts →
        a < b ∧ ∃ tf, toks[a]? = some tf ∧ tf.virt = none) := by
  have hcert := Bool.and_eq_true_iff.mp realStartCert_true
  have hallNTs := hcert.2
  intro sz
  induction sz using Nat.strongRecOn with
  | ind sz ih =>
    have hst : ∀ {m ps a b t}, treeSize t ≤ sz →
        realStartNTs.contains m = true →
        Strict.PosSynStep cx P toks m ps a b t →
        a < b ∧ ∃ tf, toks[a]? = some tf ∧ tf.virt = none := by
      intro m ps a b t hsz hm hs
      have hmCi := List.all_eq_true.mp
        (List.all_eq_true.mp hallNTs m (List.contains_iff_mem.mp hm))
        (cxIdx cx) (List.mem_range.mpr (cxIdx_lt cx))
      rw [cxOfIdx_cxIdx] at hmCi
      simp only [Bool.and_eq_true] at hmCi
      cases hs with
      | lex hnil _ _ =>
        rw [← glData_eq] at hnil; simp [hnil] at hmCi
      | node s hsMem _ _ hseq =>
        dsimp only [treeSize] at hsz
        have hsG := hsMem; rw [← glData_eq] at hsG
        have hsOk := List.all_eq_true.mp hmCi.2 s hsG
        exact (ih _ (by omega)).2 (Nat.le_refl _) hsMem (fun idx _ => by simp) hsOk hseq
    refine ⟨hst, ?_⟩
    intro n s ps k is
    induction is generalizing k with
    | nil => intro _ _ _ _ _ _ _ hokR _; cases hokR
    | cons it rest ihr =>
      intro a b mask ts hsz hsMem hidx hokR hseq
      have hitAt : s.alt.rhs[k]? = some it := by
        simpa using hidx 0 (by simp)
      have hidxR : ∀ idx < rest.length, s.alt.rhs[k + 1 + idx]? = rest[idx]? := by
        intro idx hlt
        have := hidx (idx + 1) (by simp; omega)
        rwa [show k + (idx + 1) = k + 1 + idx from by omega, List.getElem?_cons_succ] at this
      cases hseq with
      | look _ hr | noLT _ hr | empty hr | onlyIf hr =>
        unfold rhsHasRealStart at hokR
        exact ihr hsz hsMem hidxR hokR hr
      | phrase hp _ => nomatch hp
      | @absent _ _ _ sym0 _ _ _ _ _ hr =>
        unfold rhsHasRealStart at hokR
        cases sym0 with
        | t tx =>
          cases tx with
          | cp _ => cases hokR
          | text str b0 =>
            by_cases hcond : (str != ";" && str != "") = true
            · simp only [hcond, ↓reduceIte] at hokR
              exact ihr hsz hsMem hidxR hokR hr
            · simp only [hcond, Bool.false_eq_true, ↓reduceIte] at hokR
        | nt m1 args1 =>
          by_cases hcond : ((glData.alts cx .syntactic m1).isEmpty || realStartNTs.contains m1) = true
          · simp only [hcond, ↓reduceIte] at hokR
            exact ihr hsz hsMem hidxR hokR hr
          · simp only [hcond, Bool.false_eq_true, ↓reduceIte] at hokR
      | @term _ _ _ tx o _ _ h _ _ _ ht hr =>
        dsimp only [treeSize.treeListSize, treeSize] at hsz
        have hhb := Strict.posSynSeq_le hr
        obtain ⟨hlt, _, str, b0, tf, htxEq, hgetA, _, ht1⟩ := syn_term_step_one ht
        subst htxEq
        unfold rhsHasRealStart at hokR
        split at hokR
        · next hstrOk =>
          simp only [Bool.and_eq_true, bne_iff_ne] at hstrOk
          have hvNone := term_non_semi_not_virt hsMem (Or.inl ⟨o, hitAt⟩) hstrOk.1 ht1
          exact ⟨by omega, tf, hgetA, hvNone⟩
        · cases hokR
      | @butNotT _ _ _ tx ex _ _ h _ _ _ ht _ hr =>
        dsimp only [treeSize.treeListSize, treeSize] at hsz
        have hhb := Strict.posSynSeq_le hr
        obtain ⟨hlt, _, str, b0, tf, htxEq, hgetA, _, ht1⟩ := syn_term_step_one ht
        subst htxEq
        unfold rhsHasRealStart at hokR
        simp only [Bool.and_eq_true, bne_iff_ne] at hokR
        have hvNone := term_non_semi_not_virt hsMem (Or.inr ⟨ex, hitAt⟩) hokR.1 ht1
        exact ⟨by omega, tf, hgetA, hvNone⟩
      | @nt _ _ _ m1 args1 o _ _ h _ _ t1 _ hs1 _ hr =>
        dsimp only [treeSize.treeListSize] at hsz
        have hhb := Strict.posSynSeq_le hr
        unfold rhsHasRealStart at hokR
        split at hokR
        · next hm1Ok =>
          rcases Bool.or_eq_true_iff.mp hm1Ok with hemM1 | hmemM1
          · rw [List.isEmpty_iff, glData_eq] at hemM1
            cases hs1 with
            | node _ hsM1 _ _ _ => rw [hemM1] at hsM1; nomatch hsM1
            | @lex _ _ _ _ eTok _ hgetA hleaf =>
              exact ⟨by omega, eTok, hgetA, hleaf.1⟩
          · obtain ⟨hlt1, htf⟩ := hst (by omega) hmemM1 hs1
            exact ⟨by omega, htf⟩
        · cases hokR
      | @butNotN _ _ _ m1 args1 ex _ _ h _ _ t1 _ hs1 _ hr =>
        dsimp only [treeSize.treeListSize] at hsz
        have hhb := Strict.posSynSeq_le hr
        unfold rhsHasRealStart at hokR
        rcases Bool.or_eq_true_iff.mp hokR with hemM1 | hmemM1
        · rw [List.isEmpty_iff, glData_eq] at hemM1
          cases hs1 with
          | node _ hsM1 _ _ _ => rw [hemM1] at hsM1; nomatch hsM1
          | @lex _ _ _ _ eTok _ hgetA hleaf =>
            exact ⟨by omega, eTok, hgetA, hleaf.1⟩
        · obtain ⟨hlt1, htf⟩ := hst (by omega) hmemM1 hs1
          exact ⟨by omega, htf⟩

private theorem posSynStep_expr_first_safe (hok : parseTablesOk = true) {cx : Ctx} {toks : List Token} :
    ∀ (sz : Nat),
      (∀ {m ps a b t}, treeSize t ≤ sz →
        exprFirstSafeNTs.contains m = true →
        Strict.PosSynStep cx Engine.Model.codePrims toks m ps a b t →
        ∃ lg tok0,
          a < b ∧ toks[a]? = some tok0 ∧ tok0.virt = none ∧
          t.goalAt a = some lg ∧
          (lg = .InputElementDiv ∨ lg = .InputElementRegExp) ∧
          tok0.text[0]? ≠ some 0x7D ∧
          (tok0.text[0]? = some 0x2F → lg = .InputElementRegExp)) ∧
      (∀ {n s ps k is a b mask ts}, treeSize.treeListSize ts ≤ sz →
        s ∈ Ecma.Spec.gl.alts cx .syntactic n →
        (∀ idx < is.length, s.alt.rhs[k + idx]? = is[idx]?) →
        rhsFirstExprSafe cx is = true →
        Strict.PosSynSeq cx Engine.Model.codePrims toks s ps k is a b mask ts →
        ∃ lg tok0,
          a < b ∧ toks[a]? = some tok0 ∧ tok0.virt = none ∧
          Tree.goalAt.inKids a ts = some lg ∧
          (lg = .InputElementDiv ∨ lg = .InputElementRegExp) ∧
          tok0.text[0]? ≠ some 0x7D ∧
          (tok0.text[0]? = some 0x2F → lg = .InputElementRegExp)) := by
  intro sz
  induction sz using Nat.strongRecOn with
  | ind sz ih =>
    have hst : ∀ {m ps a b t}, treeSize t ≤ sz →
        exprFirstSafeNTs.contains m = true →
        Strict.PosSynStep cx Engine.Model.codePrims toks m ps a b t →
        ∃ lg tok0,
          a < b ∧ toks[a]? = some tok0 ∧ tok0.virt = none ∧
          t.goalAt a = some lg ∧
          (lg = .InputElementDiv ∨ lg = .InputElementRegExp) ∧
          tok0.text[0]? ≠ some 0x7D ∧
          (tok0.text[0]? = some 0x2F → lg = .InputElementRegExp) := by
      intro m ps a b t hsz hm hs
      have hmCi := List.all_eq_true.mp
        (List.all_eq_true.mp exprFirstSafeCert_true m (List.contains_iff_mem.mp hm))
        (cxIdx cx) (List.mem_range.mpr (cxIdx_lt cx))
      rw [cxOfIdx_cxIdx] at hmCi
      simp only [Bool.and_eq_true] at hmCi
      cases hs with
      | lex hnil _ _ =>
        rw [← glData_eq] at hnil; simp [hnil] at hmCi
      | node s hsMem _ _ hseq =>
        dsimp only [treeSize] at hsz
        have hsG := hsMem; rw [← glData_eq] at hsG
        have hsOk := List.all_eq_true.mp hmCi.2 s hsG
        exact (ih _ (by omega)).2 (Nat.le_refl _) hsMem (fun idx _ => by simp) hsOk hseq
    refine ⟨hst, ?_⟩
    intro n s ps k is
    induction is generalizing k with
    | nil => intro _ _ _ _ _ _ _ hokR _; cases hokR
    | cons it rest ihr =>
      intro a b mask ts hsz hsMem hidx hokR hseq
      have hitAt : s.alt.rhs[k]? = some it := by simpa using hidx 0 (by simp)
      have hidxR : ∀ idx < rest.length, s.alt.rhs[k + 1 + idx]? = rest[idx]? := by
        intro idx hlt
        have := hidx (idx + 1) (by simp; omega)
        rwa [show k + (idx + 1) = k + 1 + idx from by omega, List.getElem?_cons_succ] at this
      cases hseq with
      | look _ hr | noLT _ hr | empty hr | onlyIf hr =>
        unfold rhsFirstExprSafe at hokR
        exact ihr hsz hsMem hidxR hokR hr
      | @absent _ _ _ sym0 _ _ _ _ _ _ =>
        unfold rhsFirstExprSafe at hokR
        cases sym0 with
        | t tx => cases tx <;> cases hokR
        | nt _ _ => cases hokR
      | phrase hp _ => nomatch hp
      | @butNotT _ _ _ tx _ _ _ _ _ _ _ _ _ _ =>
        unfold rhsFirstExprSafe at hokR
        cases tx <;> cases hokR
      | @term _ _ _ tx o _ _ h _ _ _ ht hr =>
        dsimp only [treeSize.treeListSize, treeSize] at hsz
        have hhb := Strict.posSynSeq_le hr
        obtain ⟨hlt, _, str, b0, tok0, htxEq, hgetA, htxtEq, ht1⟩ := syn_term_step_one ht
        subst htxEq
        cases o with
        | true => unfold rhsFirstExprSafe at hokR; cases hokR
        | false =>
          unfold rhsFirstExprSafe at hokR
          cases hchL : str.toList with
          | nil => rw [hchL] at hokR; cases hokR
          | cons ch chTl =>
            rw [hchL] at hokR
            simp only [Bool.and_eq_true, bne_iff_ne] at hokR
            have hvNone := term_non_semi_not_virt hsMem (Or.inl ⟨false, hitAt⟩) hokR.2 ht1
            refine ⟨.InputElementDiv, tok0, by omega, hgetA, hvNone, ?_, Or.inl rfl, ?_, ?_⟩
            · dsimp only [Tree.goalAt.inKids]
              unfold Tree.goalAt
              simp [hlt]
            · rw [htxtEq, hchL, List.map_cons, List.getElem?_cons_zero]
              intro heq; exact hokR.1.2 (char_eq_of_toNat_eq (c := ch) (d := '}') (Option.some.inj heq))
            · rw [htxtEq, hchL, List.map_cons, List.getElem?_cons_zero]
              intro heq; exfalso; exact hokR.1.1 (char_eq_of_toNat_eq (c := ch) (d := '/') (Option.some.inj heq))
      | @nt _ _ _ m1 args1 o _ _ h _ _ t1 restTs hs1 _ hr =>
        dsimp only [treeSize.treeListSize] at hsz
        have hhb := Strict.posSynSeq_le hr
        cases o with
        | true => unfold rhsFirstExprSafe at hokR; cases hokR
        | false =>
          unfold rhsFirstExprSafe at hokR
          split at hokR
          · next hemM1 =>
            have hemG : Ecma.Spec.gl.alts cx .syntactic m1 = [] := by
              rw [← glData_eq]; exact List.isEmpty_iff.mp hemM1
            cases hs1 with
            | node _ hsM1 _ _ _ => rw [hemG] at hsM1; nomatch hsM1
            | @lex _ _ _ subLex tok0 _ hgetA hleaf =>
              obtain ⟨hvNone, hderLex⟩ := hleaf
              have ⟨K, hK⟩ := hderLex
              have hsL := hK (max K 1) (Nat.le_max_left K 1)
              obtain ⟨k0, hk0⟩ : ∃ k0, max K 1 = k0 + 1 := ⟨max K 1 - 1, by omega⟩
              rw [hk0] at hsL
              have hntLex : subLex.nt? = some m1 := by
                dsimp only [DerivesAt] at hsL
                generalize hlen0 : tok0.text.length = len0 at hsL
                cases hsL with
                | lex _ _ hl => nomatch hl
                | node _ _ _ _ _ => rfl
              have hgoalLex : Tree.goalAt.inKids a (Tree.lex a subLex :: restTs) = some (lexicalGoalOf m1) := by
                dsimp only [Tree.goalAt.inKids]
                unfold Tree.goalAt
                simp [hntLex]
              rcases Bool.or_eq_true_iff.mp hokR with hm1RE | hm1Com
              · rw [beq_iff_eq] at hm1RE; subst hm1RE
                have h2f := lex_derives_starts_slash hok (Or.inr rfl) (Nat.le_refl _) hderLex
                exact ⟨.InputElementRegExp, tok0, by omega, hgetA, hvNone, hgoalLex,
                  Or.inr rfl, by rw [h2f]; decide, fun _ => rfl⟩
              · have hm1NoSB : noSlashBraceLexNTs.contains m1 = true := by
                  have hmemC := List.contains_iff_mem.mp hm1Com
                  dsimp only [commonSafeLexNTs] at hmemC
                  simp only [List.mem_cons, List.not_mem_nil, or_false] at hmemC
                  rcases hmemC with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
                obtain ⟨_, hn2f, hn7d⟩ := lex_step_first_char_props hok (treeSize subLex) (Nat.le_refl _)
                  (Nat.le_refl _) hm1NoSB hsL
                have hlgDiv : lexicalGoalOf m1 = .InputElementDiv := by
                  have hmemC := List.contains_iff_mem.mp hm1Com
                  dsimp only [commonSafeLexNTs] at hmemC
                  simp only [List.mem_cons, List.not_mem_nil, or_false] at hmemC
                  rcases hmemC with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
                exact ⟨.InputElementDiv, tok0, by omega, hgetA, hvNone,
                  hlgDiv ▸ hgoalLex, Or.inl rfl, hn7d, fun h => absurd h hn2f⟩
          · obtain ⟨lg, tok0, hlt1, hgetA, hvNone, hg1, hlgOr, hn7d, h2fImp⟩ :=
              hst (by omega) hokR hs1
            refine ⟨lg, tok0, by omega, hgetA, hvNone, ?_, hlgOr, hn7d, h2fImp⟩
            dsimp only [Tree.goalAt.inKids]; rw [hg1]
      | @butNotN _ _ _ m1 args1 ex _ _ h _ _ t1 restTs hs1 _ hr =>
        dsimp only [treeSize.treeListSize] at hsz
        have hhb := Strict.posSynSeq_le hr
        unfold rhsFirstExprSafe at hokR
        split at hokR
        · next hemM1 =>
          have hemG : Ecma.Spec.gl.alts cx .syntactic m1 = [] := by
            rw [← glData_eq]; exact List.isEmpty_iff.mp hemM1
          cases hs1 with
          | node _ hsM1 _ _ _ => rw [hemG] at hsM1; nomatch hsM1
          | @lex _ _ _ subLex tok0 _ hgetA hleaf =>
            obtain ⟨hvNone, hderLex⟩ := hleaf
            have ⟨K, hK⟩ := hderLex
            have hsL := hK (max K 1) (Nat.le_max_left K 1)
            obtain ⟨k0, hk0⟩ : ∃ k0, max K 1 = k0 + 1 := ⟨max K 1 - 1, by omega⟩
            rw [hk0] at hsL
            have hntLex : subLex.nt? = some m1 := by
              dsimp only [DerivesAt] at hsL
              generalize hlen0 : tok0.text.length = len0 at hsL
              cases hsL with
              | lex _ _ hl => nomatch hl
              | node _ _ _ _ _ => rfl
            have hgoalLex : Tree.goalAt.inKids a (Tree.lex a subLex :: restTs) = some (lexicalGoalOf m1) := by
              dsimp only [Tree.goalAt.inKids]
              unfold Tree.goalAt
              simp [hntLex]
            rcases Bool.or_eq_true_iff.mp hokR with hm1RE | hm1Com
            · rw [beq_iff_eq] at hm1RE; subst hm1RE
              have h2f := lex_derives_starts_slash hok (Or.inr rfl) (Nat.le_refl _) hderLex
              exact ⟨.InputElementRegExp, tok0, by omega, hgetA, hvNone, hgoalLex,
                Or.inr rfl, by rw [h2f]; decide, fun _ => rfl⟩
            · have hm1NoSB : noSlashBraceLexNTs.contains m1 = true := by
                have hmemC := List.contains_iff_mem.mp hm1Com
                dsimp only [commonSafeLexNTs] at hmemC
                simp only [List.mem_cons, List.not_mem_nil, or_false] at hmemC
                rcases hmemC with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
              obtain ⟨_, hn2f, hn7d⟩ := lex_step_first_char_props hok (treeSize subLex) (Nat.le_refl _)
                (Nat.le_refl _) hm1NoSB hsL
              have hlgDiv : lexicalGoalOf m1 = .InputElementDiv := by
                have hmemC := List.contains_iff_mem.mp hm1Com
                dsimp only [commonSafeLexNTs] at hmemC
                simp only [List.mem_cons, List.not_mem_nil, or_false] at hmemC
                rcases hmemC with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
              exact ⟨.InputElementDiv, tok0, by omega, hgetA, hvNone,
                hlgDiv ▸ hgoalLex, Or.inl rfl, hn7d, fun h => absurd h hn2f⟩
        · obtain ⟨lg, tok0, hlt1, hgetA, hvNone, hg1, hlgOr, hn7d, h2fImp⟩ :=
            hst (by omega) hokR hs1
          refine ⟨lg, tok0, by omega, hgetA, hvNone, ?_, hlgOr, hn7d, h2fImp⟩
          dsimp only [Tree.goalAt.inKids]; rw [hg1]

private theorem pastVirt_le_real {toks : List Token} {p r : Nat}
    (hpr : p ≤ r) {tok : Token} (hget : toks[r]? = some tok) (hv : tok.virt = none) :
    pastVirt toks p ≤ r ∧
    ∃ tr, toks[pastVirt toks p]? = some tr ∧ tr.virt = none := by
  unfold pastVirt
  have hgen : ∀ (l : List Token) (idx : Nat), l[idx]? = some tok → tok.virt = none →
      (l.takeWhile (·.virt.isSome)).length ≤ idx ∧
      ∃ tr, l[(l.takeWhile (·.virt.isSome)).length]? = some tr ∧ tr.virt = none := by
    intro l
    induction l with
    | nil => intro idx h; simp at h
    | cons hd tl ih =>
      intro idx h hv0
      cases idx with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at h
        subst h
        simp [hv0]
      | succ m =>
        simp only [List.getElem?_cons_succ] at h
        rw [List.takeWhile_cons]
        cases hhd : hd.virt with
        | none =>
          simp [hhd]
        | some w =>
          simp only [Option.isSome_some, ↓reduceIte, List.length_cons]
          obtain ⟨hle, tr, htr, htrV⟩ := ih m h hv0
          exact ⟨by omega, tr, by simpa using htr, htrV⟩
  have hdGet : (toks.drop p)[r - p]? = some tok := by
    rw [List.getElem?_drop, show p + (r - p) = r from by omega]; exact hget
  obtain ⟨hle, tr, htr, htrV⟩ := hgen (toks.drop p) (r - p) hdGet hv
  rw [List.getElem?_drop] at htr
  exact ⟨by omega, tr, htr, htrV⟩

private theorem pastVirt_clearHeadLT_slice {toks : List Token} {i j p : Nat}
    (_hij : i < j) (_hj : j ≤ toks.length) (_hip : i ≤ p) (hp : p ≤ j - 1)
    {tokClose : Token} (hclose : toks[j - 1]? = some tokClose) (hcv : tokClose.virt = none) :
    let toksSub := clearHeadLT (slice toks i j)
    pastVirt toks p ≤ j - 1 ∧
    pastVirt toksSub (p - i) = pastVirt toks p - i := by
  intro toksSub
  obtain ⟨hle, _⟩ := pastVirt_le_real hp hclose hcv
  refine ⟨hle, ?_⟩
  unfold pastVirt
  have hvirtDrop : ((toksSub.drop (p - i)).takeWhile (·.virt.isSome)).length =
      (((slice toks i j).drop (p - i)).takeWhile (·.virt.isSome)).length := by
    have : ((toksSub.drop (p - i)).map (·.virt.isSome)) =
        (((slice toks i j).drop (p - i)).map (·.virt.isSome)) := by
      apply List.ext_getElem
      · simp [toksSub, clearHeadLT_length]
      · intro idx h1 h2
        simp only [List.getElem_map, List.getElem_drop]
        have h := (clearHeadLT_getElem?_text_virt (slice toks i j) (p - i + idx)).2
        have hidx1 : p - i + idx < toksSub.length := by rw [List.length_map, List.length_drop] at h1; omega
        have hidx2 : p - i + idx < (slice toks i j).length := by rw [List.length_map, List.length_drop] at h2; omega
        have hg1 := List.getElem?_eq_getElem hidx1
        have hg2 := List.getElem?_eq_getElem hidx2
        rw [hg1, hg2] at h
        simp only [Option.map_some, Option.some.injEq] at h
        rw [h]
    have htwLen : ∀ (l1 l2 : List Token), l1.map (·.virt.isSome) = l2.map (·.virt.isSome) →
        (l1.takeWhile (·.virt.isSome)).length = (l2.takeWhile (·.virt.isSome)).length := by
      intro l1
      induction l1 with
      | nil => intro l2 hm; cases l2 <;> simp at hm ⊢
      | cons a1 r1 ih1 =>
        intro l2 hm
        cases l2 with
        | nil => simp at hm
        | cons a2 r2 =>
          simp only [List.map_cons, List.cons.injEq] at hm
          rw [List.takeWhile_cons, List.takeWhile_cons, hm.1]
          cases a2.virt.isSome <;> simp [ih1 r2 hm.2]
    exact htwLen _ _ this
  rw [hvirtDrop]
  have hdropSlice : (slice toks i j).drop (p - i) = (toks.drop p).take (j - p) := by
    unfold slice
    rw [List.drop_take, List.drop_drop, show i + (p - i) = p from by omega,
        show j - i - (p - i) = j - p from by omega]
  rw [hdropSlice]
  -- Since `(toks.drop p)[j - 1 - p]? = some tokClose` with `virt = none`, `takeWhile` stops at `≤ j - 1 - p < j - p`:
  have htwTake : ∀ (l : List Token) (m idx : Nat), idx < m → l[idx]? = some tokClose → tokClose.virt = none →
      ((l.take m).takeWhile (·.virt.isSome)).length = (l.takeWhile (·.virt.isSome)).length := by
    intro l
    induction l with
    | nil => intro _ _ _ h; simp at h
    | cons hd tl ih =>
      intro m idx hlt hg hv0
      cases m with
      | zero => omega
      | succ m0 =>
        rw [List.take_succ_cons, List.takeWhile_cons, List.takeWhile_cons]
        cases idx with
        | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hg
          subst hg; simp [hv0]
        | succ idx0 =>
          simp only [List.getElem?_cons_succ] at hg
          cases hd.virt.isSome <;> simp [ih m0 idx0 (by omega) hg hv0]
  have hdClose : (toks.drop p)[j - 1 - p]? = some tokClose := by
    rw [List.getElem?_drop, show p + (j - 1 - p) = j - 1 from by omega]; exact hclose
  rw [htwTake (toks.drop p) (j - p) (j - 1 - p) (by omega) hdClose hcv]
  omega

private theorem syn_startsWith_one_tok_iff {cx : Ctx} {P : CodePrims} {inp : List Token}
    {s : Src} {str : String} {rest : List LookItem} {pos : Nat}
    {tr : Token} (hget : inp[pastVirt inp pos]? = some tr) (hv : tr.virt = none) :
    StartsWith (tokenAlphabet Ecma.Spec.gl cx P) inp s (.t (.text str false) :: rest) pos ↔
      tr.text = str.toList.map Char.toNat ∧
      StartsWith (tokenAlphabet Ecma.Spec.gl cx P) inp s rest (pastVirt inp pos + 1) := by
  dsimp only [StartsWith, tokenAlphabet]
  have hltLen : pastVirt inp pos < inp.length := (List.getElem?_eq_some_iff.mp hget).1
  constructor
  · rintro ⟨h, hlt, hhLe, ht, hrest⟩
    obtain ⟨_, hhEq, _, _, tok0, htxEq, hg0, htxt0, _⟩ :=
      syn_term_step_one (cx := cx) (P := P) (toks := inp) (s := s) (k := 0) (x := .text str false) ht
    injection htxEq with hstrEq _; subst hstrEq
    have hh1 := hhEq hhLe
    subst hh1
    rw [hget] at hg0; injection hg0 with heq; subst heq
    exact ⟨htxt0, hrest⟩
  · rintro ⟨htxt, hrest⟩
    refine ⟨pastVirt inp pos + 1, by omega, by omega, ?_, hrest⟩
    have hsc : slice inp (pastVirt inp pos) (pastVirt inp pos + 1) = [tr] := by
      apply List.ext_getElem
      · rw [slice_length_eq inp (by omega) (by omega)]; simp
      · intro idx h1 h2
        have hg := slice_getElem? inp (lo := pastVirt inp pos) (hi := pastVirt inp pos + 1) (k := idx) (by
          rw [slice_length_eq inp (by omega) (by omega)] at h1; exact h1)
        have hidx0 : idx = 0 := by simp at h2; omega
        subst hidx0
        simp only [Nat.add_zero, hget, List.getElem?_eq_getElem h1] at hg
        exact Option.some.inj hg
    rw [hsc]
    exact ⟨htxt, by simp [hv]⟩

private theorem syn_lookOk_shift_iff {cx : Ctx} {P : CodePrims} {toks : List Token}
    {i j p : Nat} (hij : i < j) (hj : j ≤ toks.length) (hip : i ≤ p) (hp : p ≤ j - 1)
    {tokClose : Token} (hclose : toks[j - 1]? = some tokClose)
    (hcv : tokClose.virt = none) (hctxt : tokClose.text = [0x29])
    {s : Src} {lk : Lookahead} (hlkOk : synLookKindOk lk = true)
    {neg1 neg2 : NT → List Param → Nat → Nat → Prop} :
    LookOk (tokenAlphabet Ecma.Spec.gl cx P) neg1 toks s lk p ↔
      LookOk (tokenAlphabet Ecma.Spec.gl cx P) neg2 (clearHeadLT (slice toks i j)) s lk (p - i) := by
  let toksSub := clearHeadLT (slice toks i j)
  have hseqEq : ∀ q : List LookItem, synLookSeqOk q = true →
      (StartsWith (tokenAlphabet Ecma.Spec.gl cx P) toks s q p ↔
        StartsWith (tokenAlphabet Ecma.Spec.gl cx P) toksSub s q (p - i)) := by
    intro q hqOk
    obtain ⟨hr1Le, hr1Sub⟩ := pastVirt_clearHeadLT_slice hij hj hip hp hclose hcv
    obtain ⟨_, tr1, hget1, hv1⟩ := pastVirt_le_real hp hclose hcv
    have hipR1 : i ≤ pastVirt toks p := by unfold pastVirt; omega
    have hget1Sub : ∃ tr1', toksSub[pastVirt toksSub (p - i)]? = some tr1' ∧
        tr1'.text = tr1.text ∧ tr1'.virt = none := by
      rw [hr1Sub]
      have hslGet := slice_getElem? toks (lo := i) (hi := j) (k := pastVirt toks p - i) (by omega)
      rw [show i + (pastVirt toks p - i) = pastVirt toks p from by omega, hget1] at hslGet
      obtain ⟨htxtC, hvC⟩ := clearHeadLT_getElem?_text_virt (slice toks i j) (pastVirt toks p - i)
      rw [hslGet, Option.map_some] at htxtC hvC
      cases hgC : toksSub[pastVirt toks p - i]? with
      | none => dsimp only [toksSub] at hgC; rw [hgC] at htxtC; cases htxtC
      | some tr1' =>
        dsimp only [toksSub] at hgC; rw [hgC] at htxtC hvC
        simp only [Option.map_some, Option.some.injEq] at htxtC hvC
        exact ⟨tr1', rfl, htxtC, hvC.trans hv1⟩
    obtain ⟨tr1', hget1', htxt1Eq, hv1'⟩ := hget1Sub
    have hnotClose : ∀ str : String, (str != ")") = true → [0x29] ≠ str.toList.map Char.toNat := by
      intro str hne heq
      rw [bne_iff_ne] at hne; apply hne
      cases hL : str.toList with
      | nil => rw [hL] at heq; cases heq
      | cons ch tl =>
        rw [hL, List.map_cons] at heq
        injection heq with hcEq htlEq
        have htlNil : tl = [] := by cases tl <;> simp at htlEq ⊢
        subst htlNil
        have hch : ch = ')' := char_eq_of_toNat_eq (c := ch) (d := ')') hcEq.symm
        subst hch
        exact String.ext_iff.mpr hL
    unfold synLookSeqOk at hqOk
    cases q with
    | nil => cases hqOk
    | cons l1 q1 =>
      cases l1 with
      | noLT => cases hqOk
      | t tx1 =>
        cases tx1 with
        | cp _ => cases hqOk
        | text s1 b1 =>
          cases b1 with
          | true => cases q1 with | nil => cases hqOk | cons l2 q2 => cases l2 <;> cases q2 <;> cases hqOk
          | false =>
            cases q1 with
            | nil =>
              rw [syn_startsWith_one_tok_iff hget1 hv1, syn_startsWith_one_tok_iff hget1' hv1', htxt1Eq]
              rfl
            | cons l2 q2 =>
              cases l2 with
              | t tx2 =>
                cases tx2 with
                | cp _ => cases q2 <;> cases hqOk
                | text s2 b2 =>
                  cases b2 with
                  | true => cases q2 <;> cases hqOk
                  | false =>
                    cases q2 with
                    | cons _ _ => cases hqOk
                    | nil =>
                      dsimp only at hqOk
                      simp only [Bool.and_eq_true] at hqOk
                      rw [syn_startsWith_one_tok_iff hget1 hv1, syn_startsWith_one_tok_iff hget1' hv1', htxt1Eq]
                      by_cases hm1 : tr1.text = s1.toList.map Char.toNat
                      · simp only [hm1, true_and]
                        have hr1Lt : pastVirt toks p < j - 1 := by
                          by_cases heq : pastVirt toks p = j - 1
                          · exfalso; rw [heq] at hget1; rw [hclose] at hget1
                            injection hget1 with htrEq; subst htrEq
                            exact hnotClose s1 hqOk.1.1.1.1.1 (hctxt.symm.trans hm1)
                          · omega
                        obtain ⟨hr2Le, hr2Sub⟩ := pastVirt_clearHeadLT_slice (p := pastVirt toks p + 1) hij hj (by omega) (by omega) hclose hcv
                        obtain ⟨_, tr2, hget2, hv2⟩ := pastVirt_le_real (p := pastVirt toks p + 1) (by omega) hclose hcv
                        have hposR2 : 0 < pastVirt toks (pastVirt toks p + 1) - i := by unfold pastVirt; omega
                        have hget2Sub : toksSub[pastVirt toksSub (pastVirt toksSub (p - i) + 1)]? = some tr2 := by
                          dsimp only [toksSub]
                          rw [hr1Sub, show pastVirt toks p - i + 1 = (pastVirt toks p + 1) - i from by omega, hr2Sub]
                          rw [clearHeadLT_getElem?_pos _ hposR2, slice_getElem? toks (by omega),
                              show i + (pastVirt toks (pastVirt toks p + 1) - i) = pastVirt toks (pastVirt toks p + 1) from by omega]
                          exact hget2
                        rw [syn_startsWith_one_tok_iff hget2 hv2, syn_startsWith_one_tok_iff hget2Sub hv2]
                        rfl
                      · simp [hm1]
              | noLT =>
                cases q2 with
                | nil => cases hqOk
                | cons l3 q3 =>
                  cases l3 with
                  | noLT => cases q3 <;> cases hqOk
                  | t tx3 =>
                    cases tx3 with
                    | cp _ => cases q3 <;> cases hqOk
                    | text s2 b2 =>
                      cases b2 with
                      | true => cases q3 <;> cases hqOk
                      | false =>
                        cases q3 with
                        | cons _ _ => cases hqOk
                        | nil =>
                          dsimp only at hqOk
                          simp only [Bool.and_eq_true] at hqOk
                          rw [syn_startsWith_one_tok_iff hget1 hv1, syn_startsWith_one_tok_iff hget1' hv1', htxt1Eq]
                          by_cases hm1 : tr1.text = s1.toList.map Char.toNat
                          · simp only [hm1, true_and]
                            have hr1Lt : pastVirt toks p < j - 1 := by
                              by_cases heq : pastVirt toks p = j - 1
                              · exfalso; rw [heq] at hget1; rw [hclose] at hget1
                                injection hget1 with htrEq; subst htrEq
                                exact hnotClose s1 hqOk.1.1.1.1.1 (hctxt.symm.trans hm1)
                              · omega
                            obtain ⟨hr2Le, hr2Sub⟩ := pastVirt_clearHeadLT_slice (p := pastVirt toks p + 1) hij hj (by omega) (by omega) hclose hcv
                            obtain ⟨_, tr2, hget2, hv2⟩ := pastVirt_le_real (p := pastVirt toks p + 1) (by omega) hclose hcv
                            have hposR2 : 0 < pastVirt toks (pastVirt toks p + 1) - i := by unfold pastVirt; omega
                            have hget2Sub : toksSub[pastVirt toksSub (pastVirt toksSub (p - i) + 1)]? = some tr2 := by
                              dsimp only [toksSub]
                              rw [hr1Sub, show pastVirt toks p - i + 1 = (pastVirt toks p + 1) - i from by omega, hr2Sub]
                              rw [clearHeadLT_getElem?_pos _ hposR2, slice_getElem? toks (by omega),
                                  show i + (pastVirt toks (pastVirt toks p + 1) - i) = pastVirt toks (pastVirt toks p + 1) from by omega]
                              exact hget2
                            change ((tokenAlphabet Ecma.Spec.gl cx P).noLT toks (pastVirt toks (pastVirt toks p + 1)) ∧
                                StartsWith (tokenAlphabet Ecma.Spec.gl cx P) toks s [.t (.text s2 false)] (pastVirt toks p + 1)) ↔
                              ((tokenAlphabet Ecma.Spec.gl cx P).noLT toksSub (pastVirt toksSub (pastVirt toksSub (p - i) + 1)) ∧
                                StartsWith (tokenAlphabet Ecma.Spec.gl cx P) toksSub s [.t (.text s2 false)] (pastVirt toksSub (p - i) + 1))
                            have hnoLTEq : (tokenAlphabet Ecma.Spec.gl cx P).noLT toks (pastVirt toks (pastVirt toks p + 1)) ↔
                                (tokenAlphabet Ecma.Spec.gl cx P).noLT toksSub (pastVirt toksSub (pastVirt toksSub (p - i) + 1)) := by
                              dsimp only [tokenAlphabet]
                              rw [hget2, hget2Sub]
                            rw [hnoLTEq, syn_startsWith_one_tok_iff hget2 hv2, syn_startsWith_one_tok_iff hget2Sub hv2]
                            rfl
                          · simp [hm1]
  unfold synLookKindOk at hlkOk
  cases lk with
  | eq _ | mem _ | notMemNT _ => cases hlkOk
  | ne q => exact not_congr (hseqEq q hlkOk)
  | notMem qs =>
    dsimp only [LookOk]
    exact forall_congr' fun q => imp_congr_right fun hq => not_congr (hseqEq q (List.all_eq_true.mp hlkOk q hq))

private theorem reservedWord_derivesAt_succ_iff {cx : Ctx} {P : CodePrims}
    {inp : List Token} {p h : Nat} (k0 : Nat) :
    (∃ t0, DerivesAt Ecma.Spec.gl cx .syntactic (tokenAlphabet Ecma.Spec.gl cx P) inp (k0 + 1) .ReservedWord [] p h t0) ↔
      h = p + 1 ∧ ∃ tok sub,
        inp[p]? = some tok ∧ tok.virt = none ∧
        Derives Ecma.Spec.gl cx .lexical (codeAlphabet P) tok.text .ReservedWord [] 0 tok.text.length sub := by
  have hrwEmptyG := List.all_eq_true.mp (Bool.and_eq_true_iff.mp synLookAndExclCert_true).1
    (cxIdx cx) (List.mem_range.mpr (cxIdx_lt cx))
  rw [cxOfIdx_cxIdx, List.isEmpty_iff, glData_eq] at hrwEmptyG
  constructor
  · rintro ⟨t0, hst⟩
    dsimp only [DerivesAt] at hst
    cases hst with
    | node _ hsMem _ _ _ => rw [hrwEmptyG] at hsMem; nomatch hsMem
    | @lex _ _ _ sub tok _ hg hleaf => exact ⟨rfl, tok, sub, hg, hleaf.1, hleaf.2⟩
  · rintro ⟨rfl, tok, sub, hg, hv, hder⟩
    exact ⟨.lex p sub, .lex hrwEmptyG hg ⟨hv, hder⟩⟩

private theorem syn_term_shift {cx : Ctx} {P : CodePrims} {toks : List Token}
    {i j a h : Nat} (hij : i ≤ j) (hj : j ≤ toks.length) (hia : i ≤ a) (hh : h ≤ j)
    {s : Src} {k : Nat} {x : Terminal}
    (ht : (tokenAlphabet Ecma.Spec.gl cx P).term s k x (slice toks a h)) :
    a < h ∧ h = a + 1 ∧
    (tokenAlphabet Ecma.Spec.gl cx P).term s k x (slice (clearHeadLT (slice toks i j)) (a - i) (h - i)) := by
  let toksSub := clearHeadLT (slice toks i j)
  obtain ⟨hlt, hhEq, str, b, tok, rfl, hgetA, _, ht1⟩ := syn_term_step_one ht
  have hh1 := hhEq (by omega)
  subst hh1
  have hsubLen : toksSub.length = j - i := by
    dsimp only [toksSub]; rw [clearHeadLT_length, slice_length_eq toks hij hj]
  have hslGet := slice_getElem? toks (lo := i) (hi := j) (k := a - i) (by omega)
  rw [show i + (a - i) = a from by omega, hgetA] at hslGet
  obtain ⟨htxtC, hvC⟩ := clearHeadLT_getElem?_text_virt (slice toks i j) (a - i)
  rw [hslGet, Option.map_some] at htxtC hvC
  cases hgSub : toksSub[a - i]? with
  | none => dsimp only [toksSub] at hgSub; rw [hgSub] at htxtC; cases htxtC
  | some tok' =>
    dsimp only [toksSub] at hgSub
    have hgSub' := hgSub
    rw [hgSub'] at htxtC hvC
    simp only [Option.map_some, Option.some.injEq] at htxtC hvC
    have hscSub : slice toksSub (a - i) (a + 1 - i) = [tok'] := by
      have h1 : a + 1 - i = (a - i) + 1 := by omega
      rw [h1]
      apply List.ext_getElem
      · rw [slice_length_eq toksSub (by omega) (by omega)]; simp
      · intro idx hlen1 hlen2
        have hg0 := slice_getElem? toksSub (lo := a - i) (hi := (a - i) + 1) (k := idx) (by
          rw [slice_length_eq toksSub (by omega) (by omega)] at hlen1; exact hlen1)
        have hidx0 : idx = 0 := by simp at hlen2; omega
        subst hidx0
        rw [Nat.add_zero, List.getElem?_eq_getElem hlen1] at hg0
        exact Option.some.inj (hg0.trans hgSub)
    refine ⟨by omega, rfl, ?_⟩
    rw [hscSub]
    dsimp only [tokenAlphabet] at ht1 ⊢
    rw [htxtC, hvC]; exact ht1

private theorem syn_derivesAt_shift_inner (_hok : parseTablesOk = true) {cx : Ctx} {P : CodePrims}
    {toks : List Token} {i j : Nat} (hij : i < j) (hj : j ≤ toks.length)
    {tokClose : Token} (hclose : toks[j - 1]? = some tokClose)
    (hcv : tokClose.virt = none) (hctxt : tokClose.text = [0x29]) :
    let toksSub := clearHeadLT (slice toks i j)
    ∀ (k : Nat) (sz : Nat),
      (∀ {m ps a b t}, treeSize t ≤ sz → i ≤ a → b ≤ j - 1 →
        DerivesAt Ecma.Spec.gl cx .syntactic (tokenAlphabet Ecma.Spec.gl cx P) toks (k + 1) m ps a b t →
        DerivesAt Ecma.Spec.gl cx .syntactic (tokenAlphabet Ecma.Spec.gl cx P) toksSub (k + 1) m ps (a - i) (b - i) (shiftSynTree i t)) ∧
      (∀ {s ps kIdx is a b mask ts}, treeSize.treeListSize ts ≤ sz →
        i ≤ a → b ≤ j - 1 →
        (∀ it ∈ is, synRhsItemCert it = true) →
        Ecma.Grammar.Seq (tokenAlphabet Ecma.Spec.gl cx P)
          (fun n ps x y => ∃ t0, DerivesAt Ecma.Spec.gl cx .syntactic (tokenAlphabet Ecma.Spec.gl cx P) toks k n ps x y t0)
          toks Ecma.Spec.gl cx .syntactic s ps kIdx is a b mask ts →
        Ecma.Grammar.Seq (tokenAlphabet Ecma.Spec.gl cx P)
          (fun n ps x y => ∃ t0, DerivesAt Ecma.Spec.gl cx .syntactic (tokenAlphabet Ecma.Spec.gl cx P) toksSub k n ps x y t0)
          toksSub Ecma.Spec.gl cx .syntactic s ps kIdx is (a - i) (b - i) mask (ts.map (shiftSynTree i))) := by
  intro toksSub k sz
  have hsubLen : toksSub.length = j - i := by
    dsimp only [toksSub]; rw [clearHeadLT_length, slice_length_eq toks (Nat.le_of_lt hij) hj]
  have hcert2 := (Bool.and_eq_true_iff.mp synLookAndExclCert_true).2
  have hrwExcl : ∀ {s kIdx ps a h}, i ≤ a → h = a + 1 → h ≤ j - 1 →
      ¬ Excluded (tokenAlphabet Ecma.Spec.gl cx P)
          (fun n ps x y => ∃ t0, DerivesAt Ecma.Spec.gl cx .syntactic (tokenAlphabet Ecma.Spec.gl cx P) toks k n ps x y t0)
          toks s kIdx ps a h (.sym (.nt .ReservedWord [])) →
      ¬ Excluded (tokenAlphabet Ecma.Spec.gl cx P)
          (fun n ps x y => ∃ t0, DerivesAt Ecma.Spec.gl cx .syntactic (tokenAlphabet Ecma.Spec.gl cx P) toksSub k n ps x y t0)
          toksSub s kIdx ps (a - i) (h - i) (.sym (.nt .ReservedWord [])) := by
    intro s kIdx ps a h hia hhEq hhLe hex hxSub
    simp only [Excluded, applyArgs, List.filterMap_nil] at hex hxSub
    cases k with
    | zero => obtain ⟨_, hf⟩ := hxSub; exact hf
    | succ k0 =>
      rw [reservedWord_derivesAt_succ_iff k0] at hxSub
      obtain ⟨_, tok', sub, hgSub, hv', hder⟩ := hxSub
      obtain ⟨htxtC, hvC⟩ := clearHeadLT_getElem?_text_virt (slice toks i j) (a - i)
      dsimp only [toksSub] at hgSub
      rw [hgSub, slice_getElem? toks (by omega), show i + (a - i) = a from by omega] at htxtC hvC
      cases hgA : toks[a]? with
      | none => rw [hgA] at htxtC; cases htxtC
      | some tokA =>
        rw [hgA] at htxtC hvC
        simp only [Option.map_some, Option.some.injEq] at htxtC hvC
        apply hex
        rw [reservedWord_derivesAt_succ_iff k0]
        exact ⟨hhEq, tokA, sub, hgA, hvC.symm.trans hv', htxtC ▸ hder⟩
  induction sz using Nat.strongRecOn with
  | ind sz ih =>
    have hst : ∀ {m ps a b t}, treeSize t ≤ sz → i ≤ a → b ≤ j - 1 →
        DerivesAt Ecma.Spec.gl cx .syntactic (tokenAlphabet Ecma.Spec.gl cx P) toks (k + 1) m ps a b t →
        DerivesAt Ecma.Spec.gl cx .syntactic (tokenAlphabet Ecma.Spec.gl cx P) toksSub (k + 1) m ps (a - i) (b - i) (shiftSynTree i t) := by
      intro m ps a b t hsz hia hb hs
      dsimp only [DerivesAt] at hs ⊢
      cases hs with
      | @lex _ _ _ subLex tokA hnil hgetA hleaf =>
        have hsubB : (a + 1) - i = (a - i) + 1 := by omega
        rw [hsubB, shiftSynTree_lex]
        obtain ⟨htxtC, hvC⟩ := clearHeadLT_getElem?_text_virt (slice toks i j) (a - i)
        rw [slice_getElem? toks (by omega), show i + (a - i) = a from by omega, hgetA, Option.map_some] at htxtC hvC
        cases hgSub : toksSub[a - i]? with
        | none => dsimp only [toksSub] at hgSub; rw [hgSub] at htxtC; cases htxtC
        | some tok' =>
          have hgSub' := hgSub; dsimp only [toksSub] at hgSub'
          rw [hgSub'] at htxtC hvC
          simp only [Option.map_some, Option.some.injEq] at htxtC hvC
          refine .lex hnil hgSub ⟨hvC.trans hleaf.1, ?_⟩
          dsimp only [tokenAlphabet] at hleaf
          rw [htxtC]; exact hleaf.2
      | node s hsMem hgrd hpid hseq =>
        dsimp only [treeSize] at hsz
        have hsG := hsMem; rw [← glData_eq] at hsG
        obtain ⟨hrMem, haMem⟩ := mem_rulesForGrammar_of_alts rfl hsG
        have hsCert := List.all_eq_true.mp (List.all_eq_true.mp hcert2 s.rule hrMem) s.alt haMem
        rw [shiftSynTree_node]
        exact .node s hsMem hgrd hpid
          ((ih _ (by omega)).2 (Nat.le_refl _) hia hb (fun it hit => List.all_eq_true.mp hsCert it hit) hseq)
    refine ⟨hst, ?_⟩
    intro s ps kIdx is
    induction is generalizing kIdx with
    | nil => intro _ _ _ _ _ _ _ _ hs; cases hs; exact .nil
    | cons it rest ihr =>
      intro a b mask ts hsz hia hb hcert hs
      have hitC := hcert it (List.mem_cons_self ..)
      have hrestC : ∀ x ∈ rest, synRhsItemCert x = true :=
        fun x hx => hcert x (List.mem_cons_of_mem _ hx)
      have hposSeq : ∀ {kI xs x y ms us},
          Ecma.Grammar.Seq (tokenAlphabet Ecma.Spec.gl cx P)
            (fun n ps u v => ∃ t0, DerivesAt Ecma.Spec.gl cx .syntactic (tokenAlphabet Ecma.Spec.gl cx P) toks k n ps u v t0)
            toks Ecma.Spec.gl cx .syntactic s ps kI xs x y ms us →
          Strict.PosSynSeq cx P toks s ps kI xs x y ms us :=
        fun h0 => (Strict.step_antitone_neg (fun _ _ _ _ f => False.elim f) (treeSize.treeListSize _)).2 (Nat.le_refl _) h0
      cases hs with
      | absent hr => exact .absent (ihr hsz hia hb hrestC hr)
      | empty hr => exact .empty (ihr hsz hia hb hrestC hr)
      | onlyIf _ => unfold synRhsItemCert at hitC; cases hitC
      | phrase _ _ => unfold synRhsItemCert at hitC; cases hitC
      | @noLT _ _ _ _ _ _ _ _ hnl hr =>
        refine .noLT ?_ (ihr hsz hia hb hrestC hr)
        dsimp only [tokenAlphabet] at hnl ⊢
        intro tok' hgSub
        by_cases haEq : a = i
        · subst haEq; rw [Nat.sub_self] at hgSub
          dsimp only [toksSub] at hgSub
          cases hsl0 : slice toks a j with
          | nil => rw [hsl0] at hgSub; cases hgSub
          | cons t0 tl0 =>
            rw [hsl0, clearHeadLT_getElem?_zero] at hgSub
            have heq := Option.some.inj hgSub
            rw [← heq]
        · have hpos : 0 < a - i := by omega
          have hab := Strict.posSynSeq_le (hposSeq hr)
          dsimp only [toksSub] at hgSub
          rw [clearHeadLT_getElem?_pos _ hpos, slice_getElem? toks (by omega),
              show i + (a - i) = a from by omega] at hgSub
          exact hnl tok' hgSub
      | @look _ _ _ lk _ _ _ _ _ hlk hr =>
        have hab := Strict.posSynSeq_le (hposSeq hr)
        unfold synRhsItemCert at hitC
        have hlk' : LookOk (tokenAlphabet Ecma.Spec.gl cx P)
            (fun n ps u v => ∃ t0, DerivesAt Ecma.Spec.gl cx .syntactic (tokenAlphabet Ecma.Spec.gl cx P) toksSub k n ps u v t0)
            toksSub s lk (a - i) :=
          (syn_lookOk_shift_iff hij hj hia (by omega) hclose hcv hctxt hitC).mp hlk
        exact .look hlk' (ihr hsz hia hb hrestC hr)
      | @term _ _ _ x o _ _ h _ _ _ ht hr =>
        dsimp only [treeSize.treeListSize, treeSize] at hsz
        have hhb := Strict.posSynSeq_le (hposSeq hr)
        obtain ⟨hlt, _, ht'⟩ := syn_term_shift (Nat.le_of_lt hij) hj hia (by omega) ht
        simp only [List.map_cons, shiftSynTree_leaf]
        exact .term ht' (ihr (ts := _) (a := h) (by omega) (by omega) hb hrestC hr)
      | @butNotT _ _ _ x ex _ _ h _ _ _ ht hex hr =>
        dsimp only [treeSize.treeListSize, treeSize] at hsz
        have hhb := Strict.posSynSeq_le (hposSeq hr)
        obtain ⟨hlt, hhEq, ht'⟩ := syn_term_shift (Nat.le_of_lt hij) hj hia (by omega) ht
        have hexEq : ex = .sym (.nt .ReservedWord []) := by
          unfold synRhsItemCert at hitC
          cases ex with
          | oneOf _ _ => cases hitC
          | sym sym0 =>
            cases sym0 with
            | t _ => cases hitC
            | nt mE argsE =>
              simp only [Bool.and_eq_true, beq_iff_eq, List.isEmpty_iff] at hitC
              rw [hitC.1, hitC.2]
        subst hexEq
        have hex' := hrwExcl hia hhEq (by omega) hex
        simp only [List.map_cons, shiftSynTree_leaf]
        exact .butNotT ht' hex' (ihr (ts := _) (a := h) (by omega) (by omega) hb hrestC hr)
      | @nt _ _ _ m0 args0 o _ _ h _ _ t0 _ hs0 hcd hr =>
        dsimp only [treeSize.treeListSize] at hsz
        have hs0Pos := (Strict.step_antitone_neg (fun _ _ _ _ f => False.elim f) (treeSize t0)).1 (Nat.le_refl _) hs0
        have hah := Strict.posSynStep_le hs0Pos
        have hhb := Strict.posSynSeq_le (hposSeq hr)
        have hs0' := hst (t := t0) (by omega) hia (by omega) hs0
        have hcd' : CondOk (tokenAlphabet Ecma.Spec.gl cx P) toksSub rest (shiftSynTree i t0) := by
          cases rest with
          | nil => trivial
          | cons hdR _ =>
            have hdC := hrestC hdR (List.mem_cons_self ..)
            unfold synRhsItemCert at hdC
            cases hdR with
            | onlyIf _ => cases hdC
            | sym _ _ | lookahead _ | noLT | empty | butNot _ _ | phrase _ => trivial
        dsimp only [List.map]
        exact .nt hs0' hcd' (ihr (ts := _) (a := h) (by omega) (by omega) hb hrestC hr)
      | @butNotN _ _ _ m0 args0 ex _ _ h _ _ t0 _ hs0 hex hr =>
        dsimp only [treeSize.treeListSize] at hsz
        have hhb := Strict.posSynSeq_le (hposSeq hr)
        have hs0Pos := (Strict.step_antitone_neg (fun _ _ _ _ f => False.elim f) (treeSize t0)).1 (Nat.le_refl _) hs0
        have hah := Strict.posSynStep_le hs0Pos
        have hexEq : ex = .sym (.nt .ReservedWord []) := by
          unfold synRhsItemCert at hitC
          cases ex with
          | oneOf _ _ => cases hitC
          | sym sym0 =>
            cases sym0 with
            | t _ => cases hitC
            | nt mE argsE =>
              simp only [Bool.and_eq_true, beq_iff_eq, List.isEmpty_iff] at hitC
              rw [hitC.1, hitC.2]
        subst hexEq
        have hs0' := hst (t := t0) (by omega) hia (by omega) hs0
        dsimp only [List.map]
        refine .butNotN hs0' (fun hxSub => ?_) (ihr (ts := _) (a := h) (by omega) (by omega) hb hrestC hr)
        simp only [Excluded, applyArgs, List.filterMap_nil] at hxSub
        cases k with
        | zero => obtain ⟨_, hf⟩ := hxSub; exact hf
        | succ k0 =>
          rw [reservedWord_derivesAt_succ_iff k0] at hxSub
          obtain ⟨hhSubEq, hxRest⟩ := hxSub
          exact hrwExcl hia (by omega) (by omega) hex (by
            simp only [Excluded, applyArgs, List.filterMap_nil]
            rw [reservedWord_derivesAt_succ_iff k0]
            exact ⟨hhSubEq, hxRest⟩)

/-! ## Section 6: `Arguments` Shift, `ForHeadersExplicit`, `goalAt`, `checkNode`, `Relabel.shift`, and `CoverLaws` -/

private theorem args_seq_split_close {cx : Ctx} {P : CodePrims} {toks : List Token}
    {neg : NT → List Param → Nat → Nat → Prop}
    {s : Src} {ps : List Param} {kIdx : Nat} {mid : List Item} {a j : Nat}
    {mask : List Bool} {ts : List Tree} (hj : j ≤ toks.length)
    (hnoLk : ∀ it ∈ mid, (match it with | .lookahead _ => false | _ => true) = true)
    (hsCert : ∀ it ∈ mid, synRhsItemCert it = true)
    (hseq : Ecma.Grammar.Seq (tokenAlphabet Ecma.Spec.gl cx P) neg toks Ecma.Spec.gl cx .syntactic
      s ps kIdx (mid ++ [.sym (.t (.text ")" false)) false]) a j mask ts) :
    ∃ tsMid,
      ts = tsMid ++ [.leaf (j - 1) j] ∧
      a ≤ j - 1 ∧ 0 < j ∧
      (∃ tokClose, toks[j - 1]? = some tokClose ∧
        tokClose.text = [0x29] ∧
        (tokenAlphabet Ecma.Spec.gl cx P).term s (kIdx + mid.length) (.text ")" false) (slice toks (j - 1) j)) ∧
      Ecma.Grammar.Seq (tokenAlphabet Ecma.Spec.gl cx P) neg toks Ecma.Spec.gl cx .syntactic
        s ps kIdx mid a (j - 1) mask tsMid := by
  induction mid generalizing kIdx a mask ts with
  | nil =>
    simp only [List.nil_append, List.length_nil, Nat.add_zero] at hseq ⊢
    cases hseq with
    | @term _ _ _ _ _ _ _ h1 _ _ _ ht hnil =>
      cases hnil
      obtain ⟨hlt, hh1Eq, _, _, tokClose, htxEq, hg, htxt, _⟩ := syn_term_step_one ht
      injection htxEq with hstrEq _; subst hstrEq
      simp at htxt
      have hjEq := hh1Eq hj
      have haEq : a = j - 1 := by omega
      subst haEq
      exact ⟨[], rfl, Nat.le_refl _, by omega, ⟨tokClose, hg, htxt, ht⟩, .nil⟩
  | cons it rest ih =>
    have hnoIt := hnoLk it (List.mem_cons_self ..)
    have hnoR : ∀ x ∈ rest, (match x with | .lookahead _ => false | _ => true) = true :=
      fun x hx => hnoLk x (List.mem_cons_of_mem _ hx)
    have hitC := hsCert it (List.mem_cons_self ..)
    have hsR : ∀ x ∈ rest, synRhsItemCert x = true :=
      fun x hx => hsCert x (List.mem_cons_of_mem _ hx)
    rw [List.cons_append] at hseq
    have hlenCons : kIdx + (it :: rest).length = (kIdx + 1) + rest.length := by simp; omega
    rw [hlenCons]
    cases hseq with
    | absent hr =>
      obtain ⟨tsM, htsEq, hle, hjPos, hcl, hseqM⟩ := ih hnoR hsR hr
      exact ⟨tsM, htsEq, hle, hjPos, hcl, .absent hseqM⟩
    | empty hr =>
      obtain ⟨tsM, htsEq, hle, hjPos, hcl, hseqM⟩ := ih hnoR hsR hr
      exact ⟨tsM, htsEq, hle, hjPos, hcl, .empty hseqM⟩
    | noLT hnl hr =>
      obtain ⟨tsM, htsEq, hle, hjPos, hcl, hseqM⟩ := ih hnoR hsR hr
      exact ⟨tsM, htsEq, hle, hjPos, hcl, .noLT hnl hseqM⟩
    | look _ _ => nomatch hnoIt
    | onlyIf _ => unfold synRhsItemCert at hitC; cases hitC
    | phrase _ _ => unfold synRhsItemCert at hitC; cases hitC
    | term ht hr =>
      obtain ⟨hlt, _, _⟩ := syn_term_step_one ht
      obtain ⟨tsM, htsEq, hle, hjPos, hcl, hseqM⟩ := ih hnoR hsR hr
      subst htsEq
      exact ⟨_ :: tsM, rfl, by omega, hjPos, hcl, .term ht hseqM⟩
    | butNotT ht hex hr =>
      obtain ⟨hlt, _, _⟩ := syn_term_step_one ht
      obtain ⟨tsM, htsEq, hle, hjPos, hcl, hseqM⟩ := ih hnoR hsR hr
      subst htsEq
      exact ⟨_ :: tsM, rfl, by omega, hjPos, hcl, .butNotT ht hex hseqM⟩
    | nt hs0 hcd hr =>
      have hs0Pos := (Strict.step_antitone_neg (fun _ _ _ _ f => False.elim f) (treeSize _)).1 (Nat.le_refl _) hs0
      have hah := Strict.posSynStep_le hs0Pos
      obtain ⟨tsM, htsEq, hle, hjPos, hcl, hseqM⟩ := ih hnoR hsR hr
      subst htsEq
      have hcd' : ∀ {t0}, CondOk (tokenAlphabet Ecma.Spec.gl cx P) toks (rest ++ [.sym (.t (.text ")" false)) false]) t0 →
          CondOk (tokenAlphabet Ecma.Spec.gl cx P) toks rest t0 := by
        intro t0 h0; cases rest with | nil => trivial | cons hdR _ => cases hdR <;> exact h0
      exact ⟨_ :: tsM, rfl, by omega, hjPos, hcl, .nt hs0 (hcd' hcd) hseqM⟩
    | butNotN hs0 hex hr =>
      have hs0Pos := (Strict.step_antitone_neg (fun _ _ _ _ f => False.elim f) (treeSize _)).1 (Nat.le_refl _) hs0
      have hah := Strict.posSynStep_le hs0Pos
      obtain ⟨tsM, htsEq, hle, hjPos, hcl, hseqM⟩ := ih hnoR hsR hr
      subst htsEq
      exact ⟨_ :: tsM, rfl, by omega, hjPos, hcl, .butNotN hs0 hex hseqM⟩

private theorem seq_append_close_paren {cx : Ctx} {P : CodePrims} {inp : List Token}
    {neg : NT → List Param → Nat → Nat → Prop}
    {s : Src} {ps : List Param} {kIdx : Nat} {mid : List Item} {a b c : Nat}
    {mask : List Bool} {tsMid : List Tree}
    (hseqM : Ecma.Grammar.Seq (tokenAlphabet Ecma.Spec.gl cx P) neg inp Ecma.Spec.gl cx .syntactic
      s ps kIdx mid a b mask tsMid)
    (htClose : (tokenAlphabet Ecma.Spec.gl cx P).term s (kIdx + mid.length) (.text ")" false) (slice inp b c)) :
    Ecma.Grammar.Seq (tokenAlphabet Ecma.Spec.gl cx P) neg inp Ecma.Spec.gl cx .syntactic
      s ps kIdx (mid ++ [.sym (.t (.text ")" false)) false]) a c mask (tsMid ++ [.leaf b c]) := by
  induction mid generalizing kIdx a mask tsMid with
  | nil =>
    cases hseqM
    exact Ecma.Grammar.Seq.term htClose .nil
  | cons it rest ih =>
    have hlenCons : kIdx + (it :: rest).length = (kIdx + 1) + rest.length := by simp; omega
    rw [hlenCons] at htClose
    cases hseqM with
    | absent hr => exact .absent (ih hr htClose)
    | empty hr => exact .empty (ih hr htClose)
    | onlyIf hr => exact .onlyIf (ih hr htClose)
    | noLT hnl hr => exact .noLT hnl (ih hr htClose)
    | look hlk hr => exact .look hlk (ih hr htClose)
    | phrase hp hr => exact .phrase hp (ih hr htClose)
    | term ht hr => exact .term ht (ih hr htClose)
    | butNotT ht hex hr => exact .butNotT ht hex (ih hr htClose)
    | @nt _ _ _ _ _ _ _ _ _ _ _ t0 _ hs0 hcd hr =>
      have hcd' : CondOk (tokenAlphabet Ecma.Spec.gl cx P) inp (rest ++ [.sym (.t (.text ")" false)) false]) t0 := by
        cases rest with
        | nil => trivial
        | cons hdR _ => cases hdR <;> exact hcd
      exact .nt hs0 hcd' (ih hr htClose)
    | butNotN hs0 hex hr => exact .butNotN hs0 hex (ih hr htClose)

private theorem argsAlt_decompose {cx : Ctx} {s : Src}
    (hs : s ∈ Ecma.Spec.gl.alts cx .syntactic .Arguments) :
    ∃ mid,
      s.alt.rhs = .sym (.t (.text "(" false)) false :: (mid ++ [.sym (.t (.text ")" false)) false]) ∧
      (∀ it ∈ mid, (match it with | .lookahead _ => false | _ => true) = true) ∧
      (∀ it ∈ s.alt.rhs, synRhsItemCert it = true) := by
  have hc1 := Bool.and_eq_true_iff.mp coverGoalsCert_true
  have hci := List.all_eq_true.mp hc1.2 (cxIdx cx) (List.mem_range.mpr (cxIdx_lt cx))
  rw [cxOfIdx_cxIdx] at hci
  have hsG := hs; rw [← glData_eq] at hsG
  have hargsOk := List.all_eq_true.mp (Bool.and_eq_true_iff.mp hci).2 s hsG
  have hcert2 := (Bool.and_eq_true_iff.mp synLookAndExclCert_true).2
  obtain ⟨hrMem, haMem⟩ := mem_rulesForGrammar_of_alts rfl hsG
  have hsCert := List.all_eq_true.mp (List.all_eq_true.mp hcert2 s.rule hrMem) s.alt haMem
  unfold argsAltOk at hargsOk
  generalize hrhs : s.alt.rhs = rhs0 at hargsOk
  cases rhs0 with
  | nil => cases hargsOk
  | cons firstItem rest =>
    simp only [Bool.and_eq_true] at hargsOk
    obtain ⟨hfirstOk, hrevOk⟩ := hargsOk
    have hfirstEq : firstItem = .sym (.t (.text "(" false)) false := by
      unfold isOpenParenItem at hfirstOk
      cases firstItem with
      | sym s1 o1 =>
        cases s1 with
        | nt _ _ => cases o1 <;> cases hfirstOk
        | t tx1 =>
          cases tx1 with
          | cp _ => cases o1 <;> cases hfirstOk
          | text str1 b1 =>
            cases b1 <;> cases o1 <;> try cases hfirstOk
            rw [beq_iff_eq.mp hfirstOk]
      | _ => cases hfirstOk
    subst hfirstEq
    cases hrev : rest.reverse with
    | nil => rw [hrev] at hrevOk; cases hrevOk
    | cons lastItem midRev =>
      rw [hrev] at hrevOk
      simp only [Bool.and_eq_true] at hrevOk
      obtain ⟨hlastOk, hmidOk⟩ := hrevOk
      have hlastEq : lastItem = .sym (.t (.text ")" false)) false := by
        unfold isCloseParenItem at hlastOk
        cases lastItem with
        | sym s2 o2 =>
          cases s2 with
          | nt _ _ => cases o2 <;> cases hlastOk
          | t tx2 =>
            cases tx2 with
            | cp _ => cases o2 <;> cases hlastOk
            | text str2 b2 =>
              cases b2 <;> cases o2 <;> try cases hlastOk
              rw [beq_iff_eq.mp hlastOk]
        | _ => cases hlastOk
      subst hlastEq
      have hrestEq : rest = midRev.reverse ++ [.sym (.t (.text ")" false)) false] := by
        have := congrArg List.reverse hrev
        simpa using this
      rw [hrhs] at hsCert
      refine ⟨midRev.reverse, by rw [hrestEq], fun it hit => ?_, fun it hit => List.all_eq_true.mp hsCert it hit⟩
      exact List.all_eq_true.mp hmidOk it (List.mem_reverse.mp hit)

private theorem arguments_pos_props {cx : Ctx} {P : CodePrims} {toks : List Token}
    {ps : List Param} {h1 j : Nat} {tArgs : Tree} (hj : j ≤ toks.length)
    (hst : Strict.PosSynStep cx P toks .Arguments ps h1 j tArgs) :
    h1 < j ∧
    (∃ tokClose, toks[j - 1]? = some tokClose ∧ tokClose.virt = none ∧ tokClose.text = [0x29]) ∧
    (∀ c, (match tArgs with | .node _ _ _ _ _ ks => c ∈ ks.filter (!·.isLeaf) | _ => False) →
      ∃ mC psC aC bC, h1 < aC ∧ aC ≤ bC ∧ bC ≤ j - 1 ∧ Strict.PosSynStep cx P toks mC psC aC bC c) := by
  have hc1 := Bool.and_eq_true_iff.mp coverGoalsCert_true
  have hci := List.all_eq_true.mp hc1.2 (cxIdx cx) (List.mem_range.mpr (cxIdx_lt cx))
  rw [cxOfIdx_cxIdx] at hci
  cases hst with
  | lex hnil _ _ =>
    have hne := (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp hci).1).2
    rw [← glData_eq] at hnil; simp [hnil] at hne
  | @node _ _ _ _ _ kidsA idA s hsMem _ _ hseq =>
    obtain ⟨mid, hrhs, hnoLk, hsCert⟩ := argsAlt_decompose hsMem
    have hseq' := hseq; rw [hrhs] at hseq'
    cases hseq' with
    | @term _ _ _ _ _ _ _ hOpen _ _ _ htOpen hrRest =>
      obtain ⟨hltOpen, hhOpenEq, _, _, _, _, _, _, _⟩ := syn_term_step_one htOpen
      have hOpenLe := Strict.posSynSeq_le hrRest
      have hhOpen := hhOpenEq (by omega)
      subst hhOpen
      obtain ⟨tsMid, rfl, hmidLe, _, ⟨tokClose, hgClose, htxtClose, htClose⟩, hseqMid⟩ :=
        args_seq_split_close hj hnoLk
          (fun it hit => hsCert it (by rw [hrhs]; exact List.mem_cons_of_mem _ (List.mem_append_left _ hit)))
          hrRest
      obtain ⟨_, _, _, _, tokClose', htxCloseEq, hgClose', _, htClose1⟩ := syn_term_step_one htClose
      injection htxCloseEq with hstrCEq hbCEq; subst hstrCEq; subst hbCEq
      rw [hgClose] at hgClose'; injection hgClose' with heqC; subst heqC
      have hvClose := term_non_semi_not_virt hsMem
        (Or.inl ⟨false, by
          rw [hrhs, show 1 + mid.length = mid.length + 1 from by omega, List.getElem?_cons_succ,
              List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]; rfl⟩)
        (by decide) htClose1
      refine ⟨by omega, ⟨tokClose, hgClose, hvClose, htxtClose⟩, ?_⟩
      intro c hc
      have hleafNot : ∀ x y, (!(Tree.leaf x y).isLeaf) = false := fun _ _ => rfl
      simp only [List.filter_cons, List.filter_append, hleafNot, Bool.false_eq_true,
        ↓reduceIte, List.filter_nil, List.append_nil] at hc
      obtain ⟨mC, psC, aC, bC, haC, habC, hbC, _, hstC⟩ :=
        Strict.posSynSeq_child_step (by omega) hseqMid c hc
      exact ⟨mC, psC, aC, bC, by omega, habC, hbC, hstC⟩

private theorem syn_derivesAt_shift_arguments (hok : parseTablesOk = true) {cx : Ctx} {P : CodePrims}
    {toks : List Token} {i h1 j : Nat} (hih1 : i ≤ h1) (hj : j ≤ toks.length)
    {ps : List Param} {tArgs : Tree} {k : Nat}
    (hst : DerivesAt Ecma.Spec.gl cx .syntactic (tokenAlphabet Ecma.Spec.gl cx P) toks (k + 1) .Arguments ps h1 j tArgs) :
    DerivesAt Ecma.Spec.gl cx .syntactic (tokenAlphabet Ecma.Spec.gl cx P)
      (clearHeadLT (slice toks i j)) (k + 1) .Arguments ps (h1 - i) (j - i) (shiftSynTree i tArgs) := by
  have hstPos : Strict.PosSynStep cx P toks .Arguments ps h1 j tArgs :=
    (Strict.step_antitone_neg (fun _ _ _ _ f => False.elim f) (treeSize tArgs)).1 (Nat.le_refl _) hst
  obtain ⟨hh1Lt, ⟨tokClose, hgClose, hvClose, htxtClose⟩, _⟩ := arguments_pos_props hj hstPos
  have hij : i < j := by omega
  have hc1 := Bool.and_eq_true_iff.mp coverGoalsCert_true
  have hci := List.all_eq_true.mp hc1.2 (cxIdx cx) (List.mem_range.mpr (cxIdx_lt cx))
  rw [cxOfIdx_cxIdx] at hci
  dsimp only [DerivesAt] at hst ⊢
  cases hst with
  | lex hnil _ _ =>
    have hne := (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp hci).1).2
    rw [← glData_eq] at hnil; simp [hnil] at hne
  | node s hsMem hgrd hpid hseq =>
    obtain ⟨mid, hrhs, hnoLk, hsCert⟩ := argsAlt_decompose hsMem
    have hseq' := hseq; rw [hrhs] at hseq'
    cases hseq' with
    | @term _ _ _ _ _ _ _ hOpen _ _ _ htOpen hrRest =>
      obtain ⟨tsMid, rfl, hmidLe, _, ⟨_, _, _, htClose⟩, hseqMid⟩ :=
        args_seq_split_close hj hnoLk
          (fun it hit => hsCert it (by rw [hrhs]; exact List.mem_cons_of_mem _ (List.mem_append_left _ hit)))
          hrRest
      obtain ⟨_, hhOpenEq, htOpen'⟩ := syn_term_shift (Nat.le_of_lt hij) hj hih1 (by omega) htOpen
      subst hhOpenEq
      obtain ⟨_, _, htClose'⟩ := syn_term_shift (Nat.le_of_lt hij) hj (by omega) (Nat.le_refl j) htClose
      have hseqMid' := (syn_derivesAt_shift_inner (cx := cx) (P := P) hok hij hj hgClose hvClose htxtClose k
        (treeSize.treeListSize tsMid)).2
        (Nat.le_refl _) (show i ≤ h1 + 1 from by omega) (Nat.le_refl (j - 1))
        (fun it hit => hsCert it (by rw [hrhs]; exact List.mem_cons_of_mem _ (List.mem_append_left _ hit)))
        hseqMid
      rw [shiftSynTree_node]
      refine .node s hsMem hgrd hpid ?_
      rw [hrhs, List.map_cons, shiftSynTree_leaf, List.map_append, List.map_singleton, shiftSynTree_leaf]
      exact .term htOpen' (seq_append_close_paren hseqMid' htClose')

private theorem forHeadersExplicit_all_iff {toks : List Token} :
    ∀ ks : List Tree, ForHeadersExplicit.all toks ks ↔ ∀ d ∈ ks, ForHeadersExplicit toks d
  | [] => by simp [ForHeadersExplicit.all]
  | d :: ds => by simp only [ForHeadersExplicit.all, forHeadersExplicit_all_iff ds, List.mem_cons, forall_eq_or_imp]

private theorem forHeadersExplicit_shift {cx : Ctx} {P : CodePrims} {toks : List Token}
    {i j : Nat} (hij : i ≤ j) (hj : j ≤ toks.length) :
    ∀ (sz : Nat) {m ps a b t}, treeSize t ≤ sz →
      i ≤ a → b ≤ j →
      Strict.PosSynStep cx P toks m ps a b t →
      ForHeadersExplicit toks t →
      ForHeadersExplicit (clearHeadLT (slice toks i j)) (shiftSynTree i t) := by
  let toksSub := clearHeadLT (slice toks i j)
  intro sz
  induction sz using Nat.strongRecOn with
  | ind sz ih =>
    intro m ps a b t hsz hia hb hst hfhe
    cases t with
    | leaf _ _ => simp [ForHeadersExplicit]
    | lex _ _ => simp [ForHeadersExplicit]
    | node nt id ps0 a0 b0 kids =>
      dsimp only [treeSize] at hsz
      cases hst with
      | node s hsMem _ _ hseq =>
        have hkidsStep := Strict.posSynSeq_child_step (by omega) hseq
        obtain ⟨hfor, hallK⟩ := hfhe
        rw [forHeadersExplicit_all_iff] at hallK
        rw [shiftSynTree_node]
        dsimp only [ForHeadersExplicit]
        refine ⟨fun hforNt d' hd' hntD' tok' hgSub => ?_, (forHeadersExplicit_all_iff _).mpr ?_⟩
        · obtain ⟨d, hdMem, rfl⟩ := List.mem_map.mp hd'
          rw [shiftSynTree_nt?] at hntD'
          have hnlD : (!d.isLeaf) = true := by cases d <;> simp [Tree.isLeaf, Tree.nt?] at hntD' ⊢
          have hdFilt : d ∈ kids.filter (!·.isLeaf) := List.mem_filter.mpr ⟨hdMem, hnlD⟩
          obtain ⟨mD, psD, aD, bD, haD, _, hbD, _, hstD⟩ := hkidsStep d hdFilt
          have hmDEq : mD = .LexicalDeclaration := by
            cases hstD with
            | node _ _ _ _ _ => injection hntD' with h
            | @lex _ _ _ subD tokD _ _ hleaf =>
              obtain ⟨_, ⟨K, hK⟩⟩ := hleaf
              have hsL := hK (max K 1) (Nat.le_max_left K 1)
              obtain ⟨k0, hk0⟩ : ∃ k0, max K 1 = k0 + 1 := ⟨max K 1 - 1, by omega⟩
              rw [hk0] at hsL
              dsimp only [DerivesAt] at hsL
              generalize hlen0 : tokD.text.length = len0 at hsL
              cases hsL with
              | lex _ _ hl => nomatch hl
              | node _ _ _ _ _ => injection hntD' with h
          subst hmDEq
          have hldIn : realStartNTs.contains .LexicalDeclaration = true :=
            (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp realStartCert_true).1).2
          obtain ⟨hltD, _⟩ := (posSynStep_real_start (treeSize d)).1 (Nat.le_refl _) hldIn hstD
          have hspD : d.span = (aD, bD) ∧ (shiftSynTree i d).span = (aD - i, bD - i) := by
            cases hstD with
            | node _ _ _ _ _ => exact ⟨rfl, by simp [Tree.span]⟩
            | lex _ _ _ => exact ⟨rfl, by simp [Tree.span]; omega⟩
          rw [hspD.2] at hgSub
          have hidxEq : bD - i - 1 = (bD - 1) - i := by omega
          rw [hidxEq] at hgSub
          obtain ⟨_, hvC⟩ := clearHeadLT_getElem?_text_virt (slice toks i j) ((bD - 1) - i)
          rw [hgSub, slice_getElem? toks (by omega), show i + ((bD - 1) - i) = bD - 1 from by omega,
              Option.map_some] at hvC
          cases hgOrig : toks[bD - 1]? with
          | none => rw [hgOrig] at hvC; cases hvC
          | some tokOrig =>
            rw [hgOrig, Option.map_some, Option.some.injEq] at hvC
            exact hvC.trans (hfor hforNt d hdMem hntD' tokOrig (by rw [hspD.1]; exact hgOrig))
        · intro d' hd'
          obtain ⟨d, hdMem, rfl⟩ := List.mem_map.mp hd'
          cases hlD : d.isLeaf with
          | true => cases d <;> simp [Tree.isLeaf, ForHeadersExplicit] at hlD ⊢
          | false =>
            have hdFilt : d ∈ kids.filter (!·.isLeaf) := List.mem_filter.mpr ⟨hdMem, by simp [hlD]⟩
            obtain ⟨mD, psD, aD, bD, haD, _, hbD, _, hstD⟩ := hkidsStep d hdFilt
            have hszD := treeSize_mem_le hdMem
            exact ih (treeSize d) (by omega) (t := d) (Nat.le_refl _) (by omega) (by omega) hstD (hallK d hdMem)

private theorem step_span_and_goalAt_props {cx : Ctx} {P : CodePrims} {toks : List Token}
    {neg : NT → List Param → Nat → Nat → Prop} :
    ∀ (sz : Nat),
      (∀ {n ps a b u}, treeSize u ≤ sz →
        Step (tokenAlphabet Ecma.Spec.gl cx P) neg toks Ecma.Spec.gl cx .syntactic n ps a b u →
        a ≤ b ∧ u.span = (a, b) ∧
        (∀ idx, (idx < a ∨ b ≤ idx) → u.goalAt idx = none) ∧
        (∀ off idx, off ≤ a → off ≤ idx → (shiftSynTree off u).goalAt (idx - off) = u.goalAt idx)) ∧
      (∀ {s ps k is a b m ts}, treeSize.treeListSize ts ≤ sz →
        Ecma.Grammar.Seq (tokenAlphabet Ecma.Spec.gl cx P) neg toks Ecma.Spec.gl cx .syntactic s ps k is a b m ts →
        a ≤ b ∧
        (∀ idx, (idx < a ∨ b ≤ idx) → Tree.goalAt.inKids idx ts = none) ∧
        (∀ off idx, off ≤ a → off ≤ idx →
          Tree.goalAt.inKids (idx - off) (ts.map (shiftSynTree off)) = Tree.goalAt.inKids idx ts)) := by
  intro sz
  induction sz using Nat.strongRecOn with
  | ind sz ih =>
    have hst : ∀ {n ps a b u}, treeSize u ≤ sz →
        Step (tokenAlphabet Ecma.Spec.gl cx P) neg toks Ecma.Spec.gl cx .syntactic n ps a b u →
        a ≤ b ∧ u.span = (a, b) ∧
        (∀ idx, (idx < a ∨ b ≤ idx) → u.goalAt idx = none) ∧
        (∀ off idx, off ≤ a → off ≤ idx → (shiftSynTree off u).goalAt (idx - off) = u.goalAt idx) := by
      intro n ps a b u hsz hs
      cases hs with
      | lex _ _ _ =>
        refine ⟨by omega, rfl, fun idx hout => ?_, fun off idx hoff hidx => ?_⟩
        · unfold Tree.goalAt; simp [show a ≠ idx from by omega]
        · rw [shiftSynTree_lex]; unfold Tree.goalAt
          have heq : (a - off == idx - off) = (a == idx) := by
            apply Bool.eq_iff_iff.mpr; simp only [beq_iff_eq]; omega
          rw [heq]
      | node s _ _ _ hseq =>
        dsimp only [treeSize] at hsz
        obtain ⟨hle, hout, hsh⟩ := (ih _ (by omega)).2 (Nat.le_refl _) hseq
        refine ⟨hle, rfl, hout, fun off idx hoff hidx => ?_⟩
        rw [shiftSynTree_node]
        exact hsh off idx hoff hidx
    refine ⟨hst, ?_⟩
    intro s ps k is
    induction is generalizing k with
    | nil => intro _ _ _ _ _ hs; cases hs; exact ⟨Nat.le_refl _, fun _ _ => rfl, fun _ _ _ _ => rfl⟩
    | cons _ _ ihr =>
      intro a b m ts hsz hs
      cases hs with
      | absent hr | look _ hr | noLT _ hr | empty hr | onlyIf hr => exact ihr hsz hr
      | phrase hp _ => nomatch hp
      | @term _ _ _ _ _ _ _ h _ _ _ ht hr | @butNotT _ _ _ _ _ _ _ h _ _ _ ht _ hr =>
        dsimp only [treeSize.treeListSize, treeSize] at hsz
        obtain ⟨hlt, _, _⟩ := syn_term_step_one ht
        obtain ⟨hleR, houtR, hshR⟩ := ihr (by omega) hr
        refine ⟨by omega, fun idx hout => ?_, fun off idx hoff hidx => ?_⟩
        · dsimp only [Tree.goalAt.inKids]
          have hlNone : (Tree.leaf a h).goalAt idx = none := by
            unfold Tree.goalAt
            rcases hout with h1 | h2
            · simp [show ¬ (a ≤ idx) from by omega]
            · simp [show ¬ (idx < h) from by omega]
          rw [hlNone]; exact houtR idx (by omega)
        · simp only [List.map_cons, shiftSynTree_leaf, Tree.goalAt.inKids]
          have hlEq : (Tree.leaf (a - off) (h - off)).goalAt (idx - off) = (Tree.leaf a h).goalAt idx := by
            unfold Tree.goalAt
            by_cases h1 : a ≤ idx ∧ idx < h
            · have h2 : a - off ≤ idx - off ∧ idx - off < h - off := ⟨by omega, by omega⟩
              simp [h1.1, h1.2, h2.1, h2.2]
            · have h2 : ¬ (a - off ≤ idx - off ∧ idx - off < h - off) := by omega
              by_cases ha1 : a ≤ idx
              · have hh1 : ¬ (idx < h) := fun hh => h1 ⟨ha1, hh⟩
                have hh2 : ¬ (idx - off < h - off) := by omega
                simp [ha1, hh1, hh2]
              · have ha2 : ¬ (a - off ≤ idx - off) := by omega
                simp [ha1, ha2]
          rw [hlEq, hshR off idx (by omega) hidx]
      | @nt _ _ _ _ _ _ _ _ h _ _ t0 _ hs0 _ hr | @butNotN _ _ _ _ _ _ _ _ h _ _ t0 _ hs0 _ hr =>
        dsimp only [treeSize.treeListSize] at hsz
        obtain ⟨hle1, _, hout1, hsh1⟩ := hst (by omega) hs0
        obtain ⟨hle2, hout2, hsh2⟩ := ihr (by omega) hr
        refine ⟨by omega, fun idx hout => ?_, fun off idx hoff hidx => ?_⟩
        · dsimp only [Tree.goalAt.inKids]
          rw [hout1 idx (by omega)]; exact hout2 idx (by omega)
        · dsimp only [List.map, Tree.goalAt.inKids]
          rw [hsh1 off idx hoff hidx, hsh2 off idx (by omega) hidx]

private theorem seq_child_extract {cx : Ctx} {P : CodePrims} {toks : List Token}
    {neg : NT → List Param → Nat → Nat → Prop}
    {s : Src} {ps : List Param} {k : Nat} {is : List Item} {a b : Nat} {m : List Bool} {ts : List Tree}
    (hseq : Ecma.Grammar.Seq (tokenAlphabet Ecma.Spec.gl cx P) neg toks Ecma.Spec.gl cx .syntactic s ps k is a b m ts) :
    ∀ (idx : Nat) tc, (ts.filter (!·.isLeaf))[idx]? = some tc →
      (∀ mC idC psC aC bC ksC, tc = .node mC idC psC aC bC ksC →
        a ≤ aC ∧ aC ≤ bC ∧ bC ≤ b ∧
        Step (tokenAlphabet Ecma.Spec.gl cx P) neg toks Ecma.Spec.gl cx .syntactic mC psC aC bC tc ∧
        (∀ u, aC ≤ u → u < bC → Tree.goalAt.inKids u ts = tc.goalAt u)) ∧
      (∀ kLex subLex, tc = .lex kLex subLex →
        ∃ mL tokL, toks[kLex]? = some tokL ∧
          Derives Ecma.Spec.gl cx .lexical (codeAlphabet P) tokL.text mL [] 0 tokL.text.length subLex) := by
  induction is generalizing k a m ts with
  | nil => intro idx _ h; cases hseq; simp at h
  | cons _ _ ih =>
    intro idx tc hget
    cases hseq with
    | absent hr | look _ hr | noLT _ hr | empty hr | onlyIf hr => exact ih hr idx tc hget
    | phrase hp _ => nomatch hp
    | @term _ _ _ _ _ _ _ h _ _ _ ht hr | @butNotT _ _ _ _ _ _ _ h _ _ _ ht _ hr =>
      obtain ⟨hlt, _, _⟩ := syn_term_step_one ht
      simp only [List.filter_cons, Tree.isLeaf, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hget
      obtain ⟨hnd, hlx⟩ := ih hr idx tc hget
      refine ⟨fun mC idC psC aC bC ksC htcEq => ?_, hlx⟩
      obtain ⟨haC, habC, hbC, hstC, hgC⟩ := hnd mC idC psC aC bC ksC htcEq
      refine ⟨by omega, habC, hbC, hstC, fun u hu1 hu2 => ?_⟩
      dsimp only [Tree.goalAt.inKids]
      have hlNone : (Tree.leaf a h).goalAt u = none := by
        unfold Tree.goalAt; simp [show ¬ (u < h) from by omega]
      rw [hlNone]; exact hgC u hu1 hu2
    | @nt _ _ _ m0 args0 _ _ _ h _ _ t0 _ hs0 _ hr | @butNotN _ _ _ m0 args0 _ _ _ h _ _ t0 _ hs0 _ hr =>
      obtain ⟨hle0, hsp0, hout0, _⟩ := (step_span_and_goalAt_props (treeSize t0)).1 (Nat.le_refl _) hs0
      obtain ⟨hleR, houtR, _⟩ := (step_span_and_goalAt_props (treeSize.treeListSize _)).2 (Nat.le_refl _) hr
      have hnl0 : (!t0.isLeaf) = true := by cases hs0 <;> rfl
      simp only [List.filter_cons, hnl0, ↓reduceIte] at hget
      cases idx with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hget
        subst hget
        refine ⟨fun mC idC psC aC bC ksC htcEq => ?_, fun kLex subLex htcEq => ?_⟩
        · subst htcEq
          have hs0' := hs0
          cases hs0' with
          | node _ _ _ _ _ =>
            refine ⟨Nat.le_refl _, hle0, by omega, hs0, fun u hu1 hu2 => ?_⟩
            dsimp only [Tree.goalAt.inKids]
            cases hg0 : (Tree.node m0 idC (applyArgs ps args0) a h ksC).goalAt u with
            | some g => rfl
            | none => exact houtR u (Or.inl hu2)
        · subst htcEq
          cases hs0 with
          | lex _ hgL hleaf => exact ⟨m0, _, hgL, hleaf.2⟩
      | succ idx0 =>
        simp only [List.getElem?_cons_succ] at hget
        obtain ⟨hnd, hlx⟩ := ih hr idx0 tc hget
        refine ⟨fun mC idC psC aC bC ksC htcEq => ?_, hlx⟩
        obtain ⟨haC, habC, hbC, hstC, hgC⟩ := hnd mC idC psC aC bC ksC htcEq
        refine ⟨by omega, habC, hbC, hstC, fun u hu1 hu2 => ?_⟩
        dsimp only [Tree.goalAt.inKids]
        rw [hout0 u (Or.inr (by omega))]; exact hgC u hu1 hu2

-- `checkNode` extraction:
private theorem checkNode_kids_present_args {B : Builder Node} {gx : Ctx} {cs : Array Nat}
    {st : Nat} {r : Node} {P' : Prod} {a' : Alt}
    (hc1 : (B.stamp r != st) = false)
    (hpo : prodOf (B.prod r) = some P')
    (hc4 : (P'.rule.lhs.ctorIdx != B.nt r) = false)
    (hc5 : (P'.grammar == .annexB) = false)
    (halt : (writtenAlts P'.rule)[P'.alt]? = some a')
    (hc6 : (!a'.guard.all (Guard.holds (B.args r))) = false)
    (hchk : (checkNode B gx cs st r).isEmpty = true) :
    let want := expectedKids a'.rhs P'.mask
    let kids := (B.kids r).toList
    want.length = kids.length ∧
    ∀ (idx : Nat) wn wargs, want[idx]? = some (wn, true, wargs) →
      ∃ kn c, kids[idx]? = some (kn, some c) ∧
        B.nt c = wn ∧ B.args c = applyArgs (B.args r) wargs := by
  rw [List.isEmpty_iff] at hchk
  unfold checkNode at hchk
  by_cases hlenNe : ((expectedKids a'.rhs P'.mask).length != (B.kids r).toList.length) = true
  · by_cases c2 : (!((B.span r).1 ≤ (B.span r).2 && (B.span r).2 ≤ cs.size)) = true <;>
    by_cases c3 : (B.text r != points cs (B.span r).1 (B.span r).2) = true
    all_goals
      simp only [hc1, c2, Bool.false_eq_true, ↓reduceIte] at hchk
      try simp only [c3, Bool.false_eq_true, ↓reduceIte] at hchk
      dsimp only [Id.run, Bind.bind, Pure.pure] at hchk
      rw [hpo] at hchk
      dsimp only at hchk
      simp only [hc4, hc5, Bool.false_and, Bool.false_eq_true, ↓reduceIte] at hchk
      rw [halt] at hchk
      dsimp only at hchk
      simp only [hc6, hlenNe, Bool.false_eq_true, ↓reduceIte] at hchk
      simp at hchk
  · have hlenEq : (expectedKids a'.rhs P'.mask).length = (B.kids r).toList.length := by
      simpa [bne_iff_ne] using hlenNe
    refine ⟨hlenEq, ?_⟩
    have hforInGen : ∀ (F : ((Nat × Bool × List Arg) × (Nat × Option Node)) → (List String × Nat) → Id (ForInStep (List String × Nat)))
        (_hYield : ∀ z es pos0, ∃ s, F z (es, pos0) = ForInStep.yield s)
        (_hNe : ∀ z es pos0 s, es ≠ [] → F z (es, pos0) = ForInStep.yield s → s.1 ≠ [])
        (_hStep : ∀ wn0 wargs0 kn0 kc0 es pos0 s,
          F ((wn0, true, wargs0), (kn0, kc0)) (es, pos0) = ForInStep.yield s → s.1 = [] →
          ∃ c, kc0 = some c ∧ B.nt c = wn0 ∧ B.args c = applyArgs (B.args r) wargs0)
        (zs : List ((Nat × Bool × List Arg) × (Nat × Option Node))) (es : List String) (pos0 : Nat),
        (Id.run (forIn zs (es, pos0) F)).1 = [] →
        es = [] ∧ ∀ p ∈ zs, ∀ wn wargs, p.1 = (wn, true, wargs) →
          ∃ kn c, p.2 = (kn, some c) ∧ B.nt c = wn ∧ B.args c = applyArgs (B.args r) wargs := by
      intro F hYield hNe hStep zs
      induction zs with
      | nil => intro es _ h0; exact ⟨h0, fun _ hp => nomatch hp⟩
      | cons z tl ih =>
        intro es pos0 h0
        obtain ⟨s1, hs1⟩ := hYield z es pos0
        have htlRes : (Id.run (forIn tl s1 F)).1 = [] := by
          rw [List.forIn_cons] at h0
          dsimp only [Bind.bind, Id.run] at h0
          rw [hs1] at h0
          exact h0
        obtain ⟨hs1Empty, htlSpec⟩ := ih s1.1 s1.2 htlRes
        have hesEmpty : es = [] := by
          cases es with
          | nil => rfl
          | cons _ _ => exact absurd hs1Empty (hNe z _ pos0 s1 (List.cons_ne_nil _ _) hs1)
        refine ⟨hesEmpty, fun p hp wn wargs hp1 => ?_⟩
        rcases List.mem_cons.mp hp with hpEq | hpTl
        · rcases z with ⟨⟨wn0, wp0, wargs0⟩, ⟨kn0, kc0⟩⟩
          subst hpEq
          injection hp1 with hwn hrest
          injection hrest with hwp hwargs
          rw [← hwn, ← hwargs]
          rw [hwp] at hs1
          obtain ⟨c, rfl, hntC, hargsC⟩ := hStep wn0 wargs0 kn0 kc0 es pos0 s1 hs1 hs1Empty
          exact ⟨kn0, c, rfl, hntC, hargsC⟩
        · exact htlSpec p hpTl wn wargs hp1
    have hexistsF : ∃ (es0 : List String) (F : ((Nat × Bool × List Arg) × (Nat × Option Node)) → (List String × Nat) → Id (ForInStep (List String × Nat))),
        (∀ z es pos0, ∃ s, F z (es, pos0) = ForInStep.yield s) ∧
        (∀ z es pos0 s, es ≠ [] → F z (es, pos0) = ForInStep.yield s → s.1 ≠ []) ∧
        (∀ wn0 wargs0 kn0 kc0 es pos0 s,
          F ((wn0, true, wargs0), (kn0, kc0)) (es, pos0) = ForInStep.yield s → s.1 = [] →
          ∃ c, kc0 = some c ∧ B.nt c = wn0 ∧ B.args c = applyArgs (B.args r) wargs0) ∧
        (Id.run (forIn ((expectedKids a'.rhs P'.mask).zip (B.kids r).toList) (es0, (B.span r).1) F)).1 = [] := by
      by_cases c2 : (!((B.span r).1 ≤ (B.span r).2 && (B.span r).2 ≤ cs.size)) = true <;>
      by_cases c3 : (B.text r != points cs (B.span r).1 (B.span r).2) = true
      all_goals
        simp only [hc1, c2, Bool.false_eq_true, ↓reduceIte] at hchk
        try simp only [c3, Bool.false_eq_true, ↓reduceIte] at hchk
        dsimp only [Id.run, Bind.bind, Pure.pure] at hchk
        rw [hpo] at hchk
        dsimp only at hchk
        simp only [hc4, hc5, Bool.false_and, Bool.false_eq_true, ↓reduceIte] at hchk
        rw [halt] at hchk
        dsimp only at hchk
        simp only [hc6, hlenNe, Bool.false_eq_true, ↓reduceIte] at hchk
        refine ⟨_, _, ?_, ?_, ?_, hchk⟩
        · intro ⟨⟨wn0, wp0, wargs0⟩, ⟨kn0, kc0⟩⟩ es pos0
          dsimp only [Pure.pure]
          by_cases d1 : (wn0 != kn0) = true <;> simp only [d1, Bool.false_eq_true, ↓reduceIte]
          all_goals
            cases kc0 with
            | none =>
              cases wp0 <;> exact ⟨_, rfl⟩
            | some c =>
              cases wp0 with
              | false => exact ⟨_, rfl⟩
              | true =>
                dsimp only
                by_cases d2 : (B.nt c != wn0) = true <;> simp only [d2, Bool.false_eq_true, ↓reduceIte] <;>
                by_cases d3 : (B.args c != applyArgs (B.args r) wargs0) = true <;> simp only [d3, Bool.false_eq_true, ↓reduceIte] <;>
                by_cases d4 : (!(pos0 ≤ (B.span c).1 && (B.span c).1 ≤ (B.span c).2 && (B.span c).2 ≤ (B.span r).2)) = true <;>
                simp only [d4, Bool.false_eq_true, ↓reduceIte]
                all_goals exact ⟨_, rfl⟩
        · intro ⟨⟨wn0, wp0, wargs0⟩, ⟨kn0, kc0⟩⟩ es pos0 s hes hF
          dsimp only [Pure.pure] at hF
          by_cases d1 : (wn0 != kn0) = true <;> simp only [d1, Bool.false_eq_true, ↓reduceIte] at hF
          all_goals
            cases kc0 with
            | none =>
              cases wp0 <;> (injection hF with hsEq; subst hsEq; simp [hes])
            | some c =>
              cases wp0 with
              | false => injection hF with hsEq; subst hsEq; simp [hes]
              | true =>
                dsimp only at hF
                by_cases d2 : (B.nt c != wn0) = true <;> simp only [d2, Bool.false_eq_true, ↓reduceIte] at hF <;>
                by_cases d3 : (B.args c != applyArgs (B.args r) wargs0) = true <;> simp only [d3, Bool.false_eq_true, ↓reduceIte] at hF <;>
                by_cases d4 : (!(pos0 ≤ (B.span c).1 && (B.span c).1 ≤ (B.span c).2 && (B.span c).2 ≤ (B.span r).2)) = true <;>
                simp only [d4, Bool.false_eq_true, ↓reduceIte] at hF
                all_goals (injection hF with hsEq; subst hsEq; simp [hes])
        · intro wn0 wargs0 kn0 kc0 es pos0 s hF hsEmpty
          dsimp only [Pure.pure] at hF
          cases kc0 with
          | none =>
            by_cases d1 : (wn0 != kn0) = true <;> simp only [d1, Bool.false_eq_true, ↓reduceIte] at hF <;>
            (injection hF with hsEq; subst hsEq; simp at hsEmpty)
          | some c =>
            refine ⟨c, rfl, ?_, ?_⟩
            · by_cases d2 : (B.nt c != wn0) = true
              · exfalso
                by_cases d1 : (wn0 != kn0) = true <;>
                by_cases d3 : (B.args c != applyArgs (B.args r) wargs0) = true <;>
                by_cases d4 : (!(pos0 ≤ (B.span c).1 && (B.span c).1 ≤ (B.span c).2 && (B.span c).2 ≤ (B.span r).2)) = true <;>
                simp only [d1, d2, d3, d4, Bool.false_eq_true, ↓reduceIte] at hF <;>
                (injection hF with hsEq; subst hsEq; simp at hsEmpty)
              · simpa [bne_iff_ne] using d2
            · by_cases d3 : (B.args c != applyArgs (B.args r) wargs0) = true
              · exfalso
                by_cases d1 : (wn0 != kn0) = true <;>
                by_cases d2 : (B.nt c != wn0) = true <;>
                by_cases d4 : (!(pos0 ≤ (B.span c).1 && (B.span c).1 ≤ (B.span c).2 && (B.span c).2 ≤ (B.span r).2)) = true <;>
                simp only [d1, d2, d3, d4, Bool.false_eq_true, ↓reduceIte] at hF <;>
                (injection hF with hsEq; subst hsEq; simp at hsEmpty)
              · simpa [bne_iff_ne] using d3
    obtain ⟨es0, F, hYield, hNe, hStep, hloop0⟩ := hexistsF
    have hloopSpec := (hforInGen F hYield hNe hStep _ es0 _ hloop0).2
    have hzipMemGen : ∀ {α β : Type} (xs : List α) (ys : List β) (i : Nat)
        (hi1 : i < xs.length) (hi2 : i < ys.length), (xs[i], ys[i]) ∈ xs.zip ys := by
      intro α β xs; induction xs with
      | nil => intro _ _ h; nomatch h
      | cons _ xs' ih =>
        intro ys i hi1 hi2
        cases ys with
        | nil => nomatch hi2
        | cons _ ys' =>
          cases i with
          | zero => exact List.mem_cons_self ..
          | succ i0 => exact List.mem_cons_of_mem _ (ih ys' i0 (by simp at hi1; omega) (by simp at hi2; omega))
    intro idx wn wargs hwantIdx
    obtain ⟨idxLtW, hwantEq⟩ := List.getElem?_eq_some_iff.mp hwantIdx
    have idxLtK : idx < (B.kids r).toList.length := hlenEq ▸ idxLtW
    have hmemZip := hzipMemGen (expectedKids a'.rhs P'.mask) (B.kids r).toList idx idxLtW idxLtK
    obtain ⟨kn, c, hkEq, hntC, hargsC⟩ := hloopSpec _ hmemZip wn wargs hwantEq
    exact ⟨kn, c, (List.getElem?_eq_getElem idxLtK).trans (congrArg some hkEq), hntC, hargsC⟩

-- `Relabel.shift` unfolding and `NodeRel`:
private theorem relabel_shift_mk (st lo : Nat) (cs : Array Nat)
    (k0 i0 j0 p0 nt0 : Nat) (ps0 : List Param) (kids0 : Array (NtId × Option Node)) (t0 : Subarray Nat) :
    Relabel.shift st lo cs (.mk k0 i0 j0 p0 nt0 ps0 kids0 t0) =
      .mk st (i0 - lo) (j0 - lo) p0 nt0 ps0
        (kids0.map fun c => (c.1, c.2.map (Relabel.shift st lo cs)))
        (Engine.Parse.view cs (i0 - lo) (j0 - lo)) := by
  rw [Relabel.shift]
  congr 1
  have hopt : ∀ o : Option Node,
      (o.attach.map fun ⟨x, _⟩ => Relabel.shift st lo cs x) = o.map (Relabel.shift st lo cs) := by
    intro o; cases o <;> rfl
  apply Array.ext
  · simp
  · intro idx h1 h2
    simp only [Array.getElem_map, Array.getElem_attach, hopt]

private theorem nodeKids_relabel_shift (st lo : Nat) (cs : Array Nat) (nd : Node) :
    Impl.nodeKids (Relabel.shift st lo cs nd) = (Impl.nodeKids nd).map (Relabel.shift st lo cs) := by
  rcases nd with ⟨k0, i0, j0, p0, nt0, ps0, kids0, t0⟩
  rw [relabel_shift_mk]
  apply Array.ext'
  simp only [Impl, Array.toList_filterMap, Array.toList_map]
  induction kids0.toList with
  | nil => rfl
  | cons hd tl ih =>
    rcases hd with ⟨m, _ | c⟩ <;> simp [ih]

private inductive TreeShiftRel (lo hi : Nat) :
    (Nat → Nat → Nat × Nat) → (Nat → Nat → Nat × Nat) → Tree → Tree → Prop where
  | leaf {sp1 sp2 a b a' b'} :
      sp2 a' b' = ((sp1 a b).1 - lo, (sp1 a b).2 - lo) →
      lo ≤ (sp1 a b).1 → (sp1 a b).2 ≤ hi →
      TreeShiftRel lo hi sp1 sp2 (.leaf a b) (.leaf a' b')
  | lex {sp1 sp2 k k' t t'} :
      TreeShiftRel lo hi
        (fun a b => ((sp1 k (k + 1)).1 + a, (sp1 k (k + 1)).1 + b))
        (fun a b => ((sp2 k' (k' + 1)).1 + a, (sp2 k' (k' + 1)).1 + b))
        t t' →
      TreeShiftRel lo hi sp1 sp2 (.lex k t) (.lex k' t')
  | node {sp1 sp2 nt id ps a b a' b' ks ks'} :
      sp2 a' b' = ((sp1 a b).1 - lo, (sp1 a b).2 - lo) →
      lo ≤ (sp1 a b).1 → (sp1 a b).2 ≤ hi →
      (ks.filter (!·.isLeaf)).length = (ks'.filter (!·.isLeaf)).length →
      (∀ (idx : Nat) (h1 : idx < (ks.filter (!·.isLeaf)).length) (h2 : idx < (ks'.filter (!·.isLeaf)).length),
        TreeShiftRel lo hi sp1 sp2 (ks.filter (!·.isLeaf))[idx] (ks'.filter (!·.isLeaf))[idx]) →
      TreeShiftRel lo hi sp1 sp2 (.node nt id ps a b ks) (.node nt id ps a' b' ks')

private theorem nodeSource_relabel_shift {st lo hi : Nat} {fullSrc : List Nat} {cs : Array Nat}
    (_hlh : lo ≤ hi) (_hhi : hi ≤ fullSrc.length) (_hcs : cs.toList = slice fullSrc lo hi)
    {k0 i0 j0 p0 nt0 : Nat} {ps0 : List Param} {kids0 : Array (NtId × Option Node)} {t0 : Subarray Nat}
    (_hiLo : lo ≤ i0) (_hjHi : j0 ≤ hi) :
    let nd' := Relabel.shift st lo cs (.mk k0 i0 j0 p0 nt0 ps0 kids0 t0)
    Impl.seqLen (Impl.nodeSource nd') = Impl.ofNat (slice cs.toList (i0 - lo) (j0 - lo)).length ∧
    (∀ k, Impl.seqGet (Impl.nodeSource nd') (Impl.ofNat k) =
      (slice cs.toList (i0 - lo) (j0 - lo))[k]?.map Impl.ofNat) := by
  intro nd'
  have hview : (Engine.Parse.view cs (i0 - lo) (j0 - lo)).toArray = cs.extract (i0 - lo) (j0 - lo) :=
    view_toArray_eq_extract cs (i0 - lo) (j0 - lo)
  have hext : (cs.extract (i0 - lo) (j0 - lo)).toList = slice cs.toList (i0 - lo) (j0 - lo) :=
    extract_toList_eq_slice cs (i0 - lo) (j0 - lo)
  refine ⟨?_, fun k => ?_⟩
  · dsimp only [nd']; rw [relabel_shift_mk]
    change MathVal.int ((Engine.Parse.view cs (i0 - lo) (j0 - lo)).toArray.map _).size = _
    rw [Array.size_map, hview, ← Array.length_toList, hext]
  · rw [impl_seqGet_nat]
    dsimp only [nd']; rw [relabel_shift_mk]
    change ((Engine.Parse.view cs (i0 - lo) (j0 - lo)).toArray.map (fun (c : Nat) => MathVal.int c))[k]? = _
    rw [Array.getElem?_map, hview, ← Array.getElem?_toList, hext]

private theorem nodeRel_relabel_shift_gen {M : Ecma.Model} (st lo hi : Nat)
    {st0 : Nat} {fullSrc : List Nat} {cs : Array Nat}
    (hlh : lo ≤ hi) (hhi : hi ≤ fullSrc.length) (hcs : cs.toList = slice fullSrc lo hi)
    {sp1 : Nat → Nat → Nat × Nat} {nd0 : M.Node} {t1 : Tree}
    (hrel : Ecma.Model.NodeRel M st0 fullSrc sp1 nd0 t1) :
    ∀ {nd : Node} {sp2 : Nat → Nat → Nat × Nat} {t2 : Tree},
      M = Impl → HEq nd0 nd →
      TreeShiftRel lo hi sp1 sp2 t1 t2 →
      Ecma.Model.NodeRel Impl st cs.toList sp2 (Relabel.shift st lo cs nd) t2 := by
  induction hrel with
  | @leaf sp1 nd0 a b _ hsp _ _ hklen =>
    intro nd sp2 t2 hM hnd hts
    subst hM; cases hnd
    cases hts with
    | leaf hsp2 haLo hbHi =>
      rcases nd with ⟨k0, i0, j0, p0, nt0, ps0, kids0, t0⟩
      change (i0, j0) = sp1 a b at hsp
      have hiLo : lo ≤ i0 := by rw [← hsp] at haLo; exact haLo
      have hjHi : j0 ≤ hi := by rw [← hsp] at hbHi; exact hbHi
      obtain ⟨hslen', hsget'⟩ := nodeSource_relabel_shift (st := st) hlh hhi hcs hiLo hjHi
      refine .leaf (by rw [relabel_shift_mk]) (by rw [relabel_shift_mk, hsp2, ← hsp]) ?_ ?_ ?_
      · rw [hsp2, ← hsp]; exact hslen'
      · intro k; rw [hsp2, ← hsp]; exact hsget' k
      · rw [show Impl.seqLen (Impl.nodeKids (Relabel.shift st lo cs _)) =
          MathVal.int (Impl.nodeKids (Relabel.shift st lo cs _)).size from rfl,
          nodeKids_relabel_shift, Array.size_map]
        exact hklen
  | @lex sp1 nd0 k tSub _ ih =>
    intro nd sp2 t2 hM hnd hts
    cases hts with
    | lex htsSub =>
      exact .lex (ih hM hnd htsSub)
  | @node sp1 nd0 nt id ps a b ks hnt hprod hargs _ hsp _ _ hklen hkget _ ih =>
    intro nd sp2 t2 hM hnd hts
    subst hM; cases hnd
    cases hts with
    | node hsp2 haLo hbHi hlenF hfaIdx =>
      rcases nd with ⟨k0, i0, j0, p0, nt0, ps0, kids0, t0⟩
      change (i0, j0) = sp1 a b at hsp
      have hiLo : lo ≤ i0 := by rw [← hsp] at haLo; exact haLo
      have hjHi : j0 ≤ hi := by rw [← hsp] at hbHi; exact hbHi
      obtain ⟨hslen', hsget'⟩ := nodeSource_relabel_shift (st := st) hlh hhi hcs hiLo hjHi
      refine .node (by rw [relabel_shift_mk]; exact hnt)
        (by rw [relabel_shift_mk]; exact hprod)
        (by rw [relabel_shift_mk]; exact hargs)
        (by rw [relabel_shift_mk])
        (by rw [relabel_shift_mk, hsp2, ← hsp])
        (by rw [hsp2, ← hsp]; exact hslen')
        (fun k => by rw [hsp2, ← hsp]; exact hsget' k)
        ?_ ?_ ?_
      · show MathVal.int (Impl.nodeKids (Relabel.shift st lo cs _)).size = _
        rw [nodeKids_relabel_shift, Array.size_map, ← hlenF]; exact hklen
      · intro k
        rw [impl_seqGet_nat, nodeKids_relabel_shift, Array.getElem?_map]
        have hk0 := hkget k
        rw [impl_seqGet_nat] at hk0
        rw [← hlenF, ← hk0]; simp
      · intro idx tc' c' htc' hc'
        rw [impl_seqGet_nat, nodeKids_relabel_shift, Array.getElem?_map] at hc'
        obtain ⟨c0, hc0, rfl⟩ := Option.map_eq_some_iff.mp hc'
        obtain ⟨idxLt', rfl⟩ := List.getElem?_eq_some_iff.mp htc'
        have idxLt : idx < (ks.filter (!·.isLeaf)).length := hlenF ▸ idxLt'
        have hc0Seq : Impl.seqGet (Impl.nodeKids (.mk k0 i0 j0 p0 nt0 ps0 kids0 t0)) (Impl.ofNat idx) = some c0 := by
          rwa [impl_seqGet_nat]
        exact ih idx _ c0 (List.getElem?_eq_getElem idxLt) hc0Seq rfl HEq.rfl (hfaIdx idx idxLt idxLt')

private theorem code_step_treeShiftRel (hok : parseTablesOk = true) {cx : Ctx} {P : CodePrims}
    {neg : NT → List Param → Nat → Nat → Prop} {inp : List Nat}
    {lo hi uStart : Nat} (huLo : lo ≤ uStart) :
    ∀ (sz : Nat) {m ps a b t}, treeSize t ≤ sz →
      uStart + b ≤ hi →
      Step (codeAlphabet P) neg inp Ecma.Spec.gl cx .lexical m ps a b t →
      TreeShiftRel lo hi
        (fun x y => (uStart + x, uStart + y))
        (fun x y => ((uStart - lo) + x, (uStart - lo) + y))
        t t := by
  intro sz
  induction sz using Nat.strongRecOn with
  | ind sz ih =>
    intro m ps a b t hsz hbHi hs
    cases hs with
    | lex _ _ hl => nomatch hl
    | @node _ _ _ _ _ kids id s hsMem _ _ hseq =>
      dsimp only [treeSize] at hsz
      have _ := huLo
      have hnotLeafOfStep : ∀ {m0 ps0 a0 b0 t0},
          Step (codeAlphabet P) neg inp Ecma.Spec.gl cx .lexical m0 ps0 a0 b0 t0 → (!t0.isLeaf) = true := by
        intro _ _ _ _ _ h; cases h with | lex _ _ hl => nomatch hl | node _ _ _ _ _ => rfl
      have hseqKids : ∀ {kIdx is x y mask ts}, treeSize.treeListSize ts ≤ treeSize.treeListSize kids →
          uStart + y ≤ hi →
          (∀ it ∈ is, itemTermNonEmpty it = true) →
          Ecma.Grammar.Seq (codeAlphabet P) neg inp Ecma.Spec.gl cx .lexical s ps kIdx is x y mask ts →
          ∀ c ∈ ts.filter (!·.isLeaf),
            TreeShiftRel lo hi (fun x y => (uStart + x, uStart + y)) (fun x y => ((uStart - lo) + x, (uStart - lo) + y)) c c := by
        intro kIdx is
        induction is generalizing kIdx with
        | nil => intro _ _ _ _ _ _ _ hs0 c hc; cases hs0; nomatch hc
        | cons it rest ihr =>
          intro x y mask ts hszL hyHi hne hs0 c hc
          have hneR : ∀ z ∈ rest, itemTermNonEmpty z = true :=
            fun z hz => hne z (List.mem_cons_of_mem _ hz)
          cases hs0 with
          | absent hr | look _ hr | noLT _ hr | empty hr | onlyIf hr => exact ihr hszL hyHi hneR hr c hc
          | term _ hr | butNotT _ _ hr | phrase _ hr =>
            dsimp only [treeSize.treeListSize, treeSize] at hszL
            have hleafF : ∀ p q, (!(Tree.leaf p q).isLeaf) = false := fun _ _ => rfl
            simp only [List.filter_cons, hleafF, Bool.false_eq_true, ↓reduceIte] at hc
            exact ihr (by omega) hyHi hneR hr c hc
          | nt hs0' _ hr | butNotN hs0' _ hr =>
            dsimp only [treeSize.treeListSize] at hszL
            have hhy := (code_step_bounds hok (treeSize.treeListSize _)).2 (Nat.le_refl _) hneR hr
            have hnl0 := hnotLeafOfStep hs0'
            simp only [List.filter_cons, hnl0, ↓reduceIte, List.mem_cons] at hc
            rcases hc with rfl | hcR
            · exact ih _ (by omega) (Nat.le_refl _) (by omega) hs0'
            · exact ihr (by omega) hyHi hneR hr c hcR
      refine .node (by ext <;> dsimp <;> omega) (by dsimp; omega) (by dsimp; omega) rfl (fun idx h1 _ => ?_)
      exact hseqKids (Nat.le_refl _) hbHi (fun it hit => item_term_nonempty_of_alts hok hsMem hit) hseq _ (List.getElem_mem h1)

private theorem realIdx_add_slice (toks : List Token) {i j r : Nat}
    (hij : i < j) (hj : j ≤ toks.length)
    {tf : Token} (htf : toks[i]? = some tf) (htfV : tf.virt = none)
    {tl : Token} (_htl : toks[j - 1]? = some tl) (_htlV : tl.virt = none)
    (hr : r < (toks.take j).countP (·.virt.isNone) - (toks.take i).countP (·.virt.isNone)) :
    let a0 := (toks.take i).countP (·.virt.isNone)
    let toksSub := clearHeadLT (slice toks i j)
    let uSub := realIdx r toksSub
    uSub < j - i ∧
    realIdx (a0 + r) toks = i + uSub ∧
    (r = 0 ↔ i + uSub = i) := by
  intro a0 toksSub uSub
  -- Prove general `realIdx` characterization: `realIdx n ts` is the unique index `u < ts.length`
  -- with `(ts[u]).virt = none` and `(ts.take u).countP (·.virt.isNone) = n` whenever `n < ts.countP (·.virt.isNone)`:
  have hrealSpec : ∀ (ts : List Token) (n : Nat), n < ts.countP (·.virt.isNone) →
      realIdx n ts < ts.length ∧
      (∃ tk, ts[realIdx n ts]? = some tk ∧ tk.virt = none) ∧
      (ts.take (realIdx n ts)).countP (·.virt.isNone) = n := by
    intro ts
    induction ts with
    | nil => intro n hn; simp at hn
    | cons hd rest ih =>
      intro n hn
      cases hhd : hd.virt with
      | none =>
        simp only [List.countP_cons, hhd, Option.isNone_none, ↓reduceIte] at hn
        cases n with
        | zero =>
          simp [realIdx, hhd]
        | succ n0 =>
          obtain ⟨hlt, ⟨tk, htk, htv⟩, hcnt⟩ := ih n0 (by omega)
          simp only [realIdx, hhd, Option.isNone_none, ↓reduceIte]
          refine ⟨by simp; omega, ⟨tk, by rw [show 1 + realIdx n0 rest = (realIdx n0 rest) + 1 from by omega]; simpa using htk, htv⟩, ?_⟩
          rw [show 1 + realIdx n0 rest = (realIdx n0 rest) + 1 from by omega, List.take_succ_cons,
              List.countP_cons, hhd]
          simp [hcnt]
      | some w =>
        simp only [List.countP_cons, hhd, Option.isNone_some, Bool.false_eq_true, ↓reduceIte] at hn
        obtain ⟨hlt, ⟨tk, htk, htv⟩, hcnt⟩ := ih n hn
        have hstep : realIdx n (hd :: rest) = 1 + realIdx n rest := by
          cases n <;> simp [realIdx, hhd]
        rw [hstep]
        refine ⟨by simp; omega, ⟨tk, by rw [show 1 + realIdx n rest = (realIdx n rest) + 1 from by omega]; simpa using htk, htv⟩, ?_⟩
        rw [show 1 + realIdx n rest = (realIdx n rest) + 1 from by omega, List.take_succ_cons,
            List.countP_cons, hhd]
        simpa using hcnt
  have hsubCnt : toksSub.countP (·.virt.isNone) = (toks.take j).countP (·.virt.isNone) - a0 := by
    have hlen : toksSub.length = j - i := by
      dsimp only [toksSub]; rw [clearHeadLT_length, slice_length_eq toks (Nat.le_of_lt hij) hj]
    have hc := countP_clearHeadLT_slice toks (Nat.le_of_lt hij) hj (u := j - i) (Nat.le_refl _)
    conv at hc => lhs; arg 1; rw [← hlen, List.take_length]
    rw [show i + (j - i) = j from by omega] at hc
    omega
  obtain ⟨huLt, ⟨tkSub, htkSub, htkSubV⟩, hcntSub⟩ := hrealSpec toksSub r (hsubCnt ▸ hr)
  have hsubLen : toksSub.length = j - i := by
    dsimp only [toksSub]; rw [clearHeadLT_length, slice_length_eq toks (Nat.le_of_lt hij) hj]
  have huLtJi : uSub < j - i := hsubLen ▸ huLt
  obtain ⟨_, hvC⟩ := clearHeadLT_getElem?_text_virt (slice toks i j) uSub
  dsimp only [toksSub, uSub] at htkSub hvC huLtJi hcntSub ⊢
  rw [htkSub, slice_getElem? toks huLtJi, Option.map_some] at hvC
  cases hgOrig : toks[i + realIdx r (clearHeadLT (slice toks i j))]? with
  | none => rw [hgOrig] at hvC; cases hvC
  | some tkOrig =>
    rw [hgOrig, Option.map_some, Option.some.injEq] at hvC
    have htkOrigV : tkOrig.virt = none := hvC.symm.trans htkSubV
    have hcntOrig := countP_clearHeadLT_slice toks (Nat.le_of_lt hij) hj (Nat.le_of_lt huLtJi)
    rw [hcntSub] at hcntOrig
    have hridxOrig := (filter_idx_real_tok toks hgOrig htkOrigV).2.2
    have hrealEq : realIdx (a0 + r) toks = i + realIdx r (clearHeadLT (slice toks i j)) := by
      rw [show a0 + r = r + a0 from by omega, hcntOrig, hridxOrig]
    refine ⟨huLtJi, hrealEq, ?_⟩
    -- At `r = 0`: `toksSub[0]` has `virt = none` (since `toks[i]` has `virt = none`), so `realIdx 0 toksSub = 0`:
    have hr0 : realIdx 0 toksSub = 0 := by
      dsimp only [toksSub]
      have hsl0 := slice_getElem? toks (lo := i) (hi := j) (k := 0) (by omega)
      rw [Nat.add_zero, htf] at hsl0
      cases hsl : slice toks i j with
      | nil => rw [hsl] at hsl0; cases hsl0
      | cons x0 xr =>
        rw [hsl, List.getElem?_cons_zero, Option.some.injEq] at hsl0
        subst hsl0; simp [clearHeadLT, realIdx, htfV]
    constructor
    · intro h0; subst h0; dsimp only [toksSub] at hr0; rw [hr0]; omega
    · intro heq
      have hu0 : realIdx r (clearHeadLT (slice toks i j)) = 0 := by omega
      rw [hu0] at hcntSub; simpa using hcntSub.symm

private theorem tokenSpan_shift_props (hok : parseTablesOk = true) {cx : Ctx} {fullSrc : List Nat}
    {els : List Element} {toks : List Token}
    (hscans : Scans Ecma.Spec.gl cx Engine.Model.codePrims fullSrc els)
    (hfilt : toks.filter (·.virt.isNone) = tokensOf fullSrc els)
    (hall : toks.all (fun k => k.virt.isNone || !k.lt) = true)
    {i j : Nat} (hij : i < j) (hj : j ≤ toks.length)
    {tf tl : Token}
    (htf : toks[i]? = some tf) (htfV : tf.virt = none)
    (htl : toks[j - 1]? = some tl) (htlV : tl.virt = none) (htlTxt : tl.text = [0x29]) :
    let sp := Ecma.Grammar.tokenSpan els toks i j
    let lo := sp.1; let hi := sp.2
    let src := slice fullSrc lo hi
    let toksSub := clearHeadLT (slice toks i j)
    lo < hi ∧ hi ≤ fullSrc.length ∧ fullSrc[hi - 1]? = some 0x29 ∧
    ∃ idxA idxB elsShifted bFirst,
      idxA ≤ idxB ∧ idxB < els.length ∧
      0 < bFirst ∧ bFirst ≤ src.length ∧ tf.text = slice src 0 bFirst ∧
      elsShifted = (slice els idxA (idxB + 1)).map (shiftElem lo) ∧
      Scans Ecma.Spec.gl cx Engine.Model.codePrims src elsShifted ∧
      toksSub.filter (·.virt.isNone) = tokensOf src elsShifted ∧
      toksSub.all (fun k => k.virt.isNone || !k.lt) = true ∧
      (∀ u v, i ≤ u → u ≤ v → v ≤ j → u < j →
        Ecma.Grammar.tokenSpan elsShifted toksSub (u - i) (v - i) =
          ((Ecma.Grammar.tokenSpan els toks u v).1 - lo, (Ecma.Grammar.tokenSpan els toks u v).2 - lo) ∧
        lo ≤ (Ecma.Grammar.tokenSpan els toks u v).1 ∧
        (Ecma.Grammar.tokenSpan els toks u v).1 ≤ (Ecma.Grammar.tokenSpan els toks u v).2 ∧
        (Ecma.Grammar.tokenSpan els toks u v).2 ≤ hi) ∧
      (∀ u tk, i ≤ u → u < j → toks[u]? = some tk → tk.virt = none →
        (Ecma.Grammar.tokenSpan els toks u (u + 1)).1 + tk.text.length ≤ hi) ∧
      (∀ k eSub, elsShifted[k]? = some eSub →
        ∃ eOrig, els[idxA + k]? = some eOrig ∧ eSub = shiftElem lo eOrig ∧
          (eSub.isToken = true →
            let uSub := realIdx ((elsShifted.take k).filter Element.isToken).length toksSub
            let uOrig := realIdx ((els.take (idxA + k)).filter Element.isToken).length toks
            uOrig = i + uSub ∧ i ≤ uOrig ∧ uOrig < j ∧ (k = 0 ↔ uOrig = i))) := by
  intro sp lo hi src toksSub
  let es := els.filter Element.isToken
  let zEs := els.zipIdx.filter (fun p => p.1.isToken)
  let a0 := (toks.take i).countP (·.virt.isNone)
  let b0 := (toks.take j).countP (·.virt.isNone)
  obtain ⟨hzFst, hzProps⟩ := zipIdx_filter_isToken_props els
  obtain ⟨htokOfLen, htokOfGet⟩ := tokensOf_map_es fullSrc els
  obtain ⟨hcI1, hfltA0, hridxA0⟩ := filter_idx_real_tok toks htf htfV
  obtain ⟨hcJ, hfltB1, _⟩ := filter_idx_real_tok toks htl htlV
  have hjSub1 : j - 1 + 1 = j := by omega
  rw [hjSub1] at hcJ
  have ha0LeR : a0 ≤ (toks.take (j - 1)).countP (·.virt.isNone) :=
    countP_take_mono _ toks (by omega)
  have ha0LtB0 : a0 < b0 := by dsimp only [b0]; omega
  have hb0Sub1 : b0 - 1 = (toks.take (j - 1)).countP (·.virt.isNone) := by dsimp only [b0]; omega
  have hb0LeEs : b0 ≤ es.length := by
    have h1 : b0 ≤ toks.countP (·.virt.isNone) := by
      have := countP_take_mono (·.virt.isNone) toks hj
      rwa [List.take_length] at this
    rw [countP_isNone_eq_filter_len, hfilt, htokOfLen] at h1
    exact h1
  have hb0LeFlt : b0 ≤ (els.filter Element.isToken).length := hb0LeEs
  have hzLen : zEs.length = es.length := by dsimp only [zEs, es]; rw [← hzFst, List.length_map]
  have ha0LtZ : a0 < zEs.length := hzLen ▸ Nat.lt_of_lt_of_le ha0LtB0 hb0LeEs
  have hb1LtZ : b0 - 1 < zEs.length := hzLen ▸ (by omega)
  rcases hza : zEs[a0]'ha0LtZ with ⟨eA, idxA⟩
  rcases hzb : zEs[b0 - 1]'hb1LtZ with ⟨eB, idxB⟩
  have hza? : zEs[a0]? = some (eA, idxA) := (List.getElem?_eq_getElem ha0LtZ).trans (congrArg some hza)
  have hzb? : zEs[b0 - 1]? = some (eB, idxB) := (List.getElem?_eq_getElem hb1LtZ).trans (congrArg some hzb)
  have hesGet : ∀ r (hr : r < zEs.length), es[r]? = some (zEs[r]'hr).1 := by
    intro r hr
    dsimp only [es]
    rw [← hzFst, List.getElem?_map, List.getElem?_eq_getElem hr]; rfl
  have hesA : es[a0]? = some eA := by rw [hesGet a0 ha0LtZ, hza]
  have hesB : es[b0 - 1]? = some eB := by rw [hesGet (b0 - 1) hb1LtZ, hzb]
  obtain ⟨hidxALt, helsA, heATok, htakeA⟩ := hzProps a0 (eA, idxA) hza?
  obtain ⟨hidxBLt, helsB, heBTok, htakeB⟩ := hzProps (b0 - 1) (eB, idxB) hzb?
  dsimp only at hidxALt helsA heATok htakeA hidxBLt helsB heBTok htakeB
  have hspEq : sp = (eA.i, eB.j) := by
    dsimp only [sp]
    unfold Ecma.Grammar.tokenSpan
    change (let start := (es[a0]?.map (·.i)).getD _; if a0 < b0 then (start, (es[b0 - 1]?.map (·.j)).getD start) else (start, start)) = _
    simp [hesA, hesB, ha0LtB0]
  have hloEq : lo = eA.i := congrArg Prod.fst hspEq
  have hhiEq : hi = eB.j := congrArg Prod.snd hspEq
  have hidxALeB : idxA ≤ idxB := by
    by_cases hle : idxA ≤ idxB
    · exact hle
    · exfalso
      have hsplit : els.take idxA = els.take idxB ++ (eB :: slice els (idxB + 1) idxA) := by
        have h1 : els.take idxA = els.take (idxB + 1) ++ slice els (idxB + 1) idxA := by
          unfold slice
          rw [← List.take_append_drop (idxB + 1) (els.take idxA), List.take_take,
              Nat.min_eq_left (by omega), List.drop_take]
        have h2 : els.take (idxB + 1) = els.take idxB ++ [eB] :=
          List.take_add_one.trans (by simp [helsB])
        rw [h1, h2, List.append_assoc, List.singleton_append]
      have hlenA : ((els.take idxA).filter Element.isToken).length = a0 := by
        rw [htakeA, List.length_take, Nat.min_eq_left (Nat.le_of_lt (Nat.lt_of_lt_of_le ha0LtB0 hb0LeEs))]
      have hlenB : ((els.take idxB).filter Element.isToken).length = b0 - 1 := by
        rw [htakeB, List.length_take, Nat.min_eq_left (by omega)]
      rw [hsplit, List.filter_append, List.filter_cons_of_pos heBTok, List.length_append, List.length_cons, hlenB] at hlenA
      omega
  obtain ⟨helemStep, helemOrd⟩ := scans_elem_ordered hscans
  obtain ⟨heAiLt, heAjLe, _, _⟩ := helemStep idxA eA helsA
  obtain ⟨heBiLt, heBjLe, _, _⟩ := helemStep idxB eB helsB
  have heAiLeBi := (helemOrd idxA idxB eA eB hidxALeB helsA helsB).1
  have hlh : lo < hi := by omega
  have hhiLe : hi ≤ fullSrc.length := by omega
  -- Extract `tf.text = slice fullSrc eA.i eA.j` and `tl.text = slice fullSrc eB.i eB.j`:
  have htfTxtEq : tf.text = slice fullSrc eA.i eA.j := by
    rw [hfilt] at hfltA0
    rw [htokOfGet a0, hza?, Option.map_some, Option.some.injEq] at hfltA0
    exact (congrArg Token.text hfltA0).symm
  have htlTxtEq : tl.text = slice fullSrc eB.i eB.j := by
    rw [← hb0Sub1, hfilt] at hfltB1
    rw [htokOfGet (b0 - 1), hzb?, Option.map_some, Option.some.injEq] at hfltB1
    exact (congrArg Token.text hfltB1).symm
  have hclose29 : fullSrc[hi - 1]? = some 0x29 := by
    have hscB : slice fullSrc eB.i hi = ([] : List Nat) ++ [0x29] := by
      rw [hhiEq, ← htlTxtEq, htlTxt]; rfl
    exact (slice_last_eq_getElem? hhiLe hscB).2
  have heAjLeHi : eA.j ≤ hi := by
    by_cases heqAB : idxA = idxB
    · subst heqAB; rw [helsA] at helsB; injection helsB with he; subst he; omega
    · have := (helemOrd idxA idxB eA eB hidxALeB helsA helsB).2 (by omega)
      omega
  have hsrcLen : src.length = hi - lo := slice_length_eq fullSrc (by omega) hhiLe
  let elsRaw := slice els idxA (idxB + 1)
  let elsShifted := elsRaw.map (shiftElem lo)
  have helsRawLen : elsRaw.length = idxB + 1 - idxA := slice_length_eq els (by omega) (by omega)
  have helsRawGet : ∀ k, k < idxB + 1 - idxA → elsRaw[k]? = els[idxA + k]? :=
    fun k hk => slice_getElem? els hk
  -- Prove `Scans Ecma.Spec.gl cx Engine.Model.codePrims src elsShifted`:
  have hscansSub : Scans Ecma.Spec.gl cx Engine.Model.codePrims src elsShifted := by
    obtain ⟨_, _, hallScans⟩ := hscans
    refine ⟨?_, ?_, ?_⟩
    · rw [List.all_eq_true]
      intro ⟨eS, k⟩ hmemZ
      have hmemIdx : k < elsShifted.length ∧ elsShifted[k]? = some eS := by
        have hgen : ∀ (l : List Element) (off : Nat), (eS, k) ∈ l.zipIdx off →
            off ≤ k ∧ k < off + l.length ∧ l[k - off]? = some eS := by
          intro l; induction l with
          | nil => intro _ hm; nomatch hm
          | cons hd tl ih =>
            intro off hm
            rcases List.mem_cons.mp hm with heq | htlM
            · obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq; simp
            · obtain ⟨h1, h2, h3⟩ := ih (off + 1) htlM
              refine ⟨by omega, by simp; omega, ?_⟩
              rw [show k - off = (k - (off + 1)) + 1 from by omega, List.getElem?_cons_succ]; exact h3
        obtain ⟨_, h2, h3⟩ := hgen elsShifted 0 hmemZ
        exact ⟨by omega, by simpa using h3⟩
      obtain ⟨hkLtS, hgetS⟩ := hmemIdx
      have hkLtR : k < idxB + 1 - idxA := by simpa [elsShifted, helsRawLen] using hkLtS
      rw [List.getElem?_map, helsRawGet k hkLtR] at hgetS
      obtain ⟨eO, helsO, rfl⟩ := Option.map_eq_some_iff.mp hgetS
      rw [beq_iff_eq]
      cases k with
      | zero =>
        rw [Nat.add_zero, helsA] at helsO; injection helsO with heq; subst heq
        simp [shiftElem, hloEq]
      | succ k0 =>
        have hk0Ne : (k0 + 1 == 0) = false := rfl
        simp only [hk0Ne, Bool.false_eq_true, ↓reduceIte, Nat.add_sub_cancel]
        have hk0LtR : k0 < idxB + 1 - idxA := by omega
        have hgetS0 : elsShifted[k0]? = (els[idxA + k0]?).map (shiftElem lo) := by
          dsimp only [elsShifted]; rw [List.getElem?_map, helsRawGet k0 hk0LtR]
        have hk0LtEls : idxA + k0 < els.length := by omega
        rcases helsO0 : els[idxA + k0]? with _ | eO0
        · exfalso; exact absurd helsO0 (by simp [List.getElem?_eq_getElem hk0LtEls])
        · rw [hgetS0, helsO0]
          simp only [Option.map_some, Option.getD_some, shiftElem]
          have hstepO := (helemStep (idxA + (k0 + 1)) eO helsO).2.2.2 (idxA + k0) eO0 (by omega) helsO0
          rw [hstepO]
    · have hlenS : elsShifted.length = idxB + 1 - idxA := by rw [List.length_map, helsRawLen]
      have hneS : elsShifted ≠ [] := by
        apply List.ne_nil_of_length_pos; omega
      rw [List.getLast?_eq_some_getLast hneS, List.getLast_eq_getElem hneS]
      have hlastIdx : elsShifted.length - 1 = idxB - idxA := by omega
      have hgetLastS : elsShifted[elsShifted.length - 1]? = some (shiftElem lo eB) := by
        rw [hlastIdx]; dsimp only [elsShifted]
        rw [List.getElem?_map, helsRawGet (idxB - idxA) (by omega),
            show idxA + (idxB - idxA) = idxB from by omega, helsB]; rfl
      have hgetLastElem : elsShifted[elsShifted.length - 1]'(by omega) = shiftElem lo eB := by
        have hg := (List.getElem?_eq_getElem (l := elsShifted) (i := elsShifted.length - 1) (by omega)).symm.trans hgetLastS
        exact Option.some.inj hg
      rw [hgetLastElem]
      simp [shiftElem, hsrcLen, hhiEq]
    · intro eS heSMem
      obtain ⟨k, hkLtS, rfl⟩ := List.getElem_of_mem heSMem
      have hkLtR : k < idxB + 1 - idxA := by simpa [elsShifted, helsRawLen] using hkLtS
      have hkLtEls : idxA + k < els.length := by omega
      let eO := els[idxA + k]'hkLtEls
      have helsO : els[idxA + k]? = some eO := List.getElem?_eq_getElem hkLtEls
      have heSEq : elsShifted[k] = shiftElem lo eO := by
        have hg : elsShifted[k]? = some (shiftElem lo eO) := by
          dsimp only [elsShifted]; rw [List.getElem?_map, helsRawGet k hkLtR, helsO]; rfl
        rw [List.getElem?_eq_getElem hkLtS] at hg; exact Option.some.inj hg
      rw [heSEq]
      have heOMem : eO ∈ els := List.getElem_mem hkLtEls
      obtain ⟨heOiLt, heODer, heOMax, heOFol⟩ := hallScans eO heOMem
      have heOiLo : lo ≤ eO.i := by
        rw [hloEq]; exact (helemOrd idxA (idxA + k) eA eO (by omega) helsA helsO).1
      have heOjHi : eO.j ≤ hi := by
        rw [hhiEq]
        by_cases heqB : idxA + k = idxB
        · subst heqB; rw [helsO] at helsB; injection helsB with he; subst he; exact Nat.le_refl _
        · exact Nat.le_trans ((helemOrd (idxA + k) idxB eO eB (by omega) helsO helsB).2 (by omega))
            (Nat.le_of_lt heBiLt)
      refine ⟨by dsimp [shiftElem]; omega,
        lex_derives_slice_fwd hok hlh hhiLe hclose29 heOiLo heOjHi heODer,
        fun h' hltH' hh'Le ⟨t', hdt'⟩ => ?_,
        fun hhasSub hjLtSrc nF hnF ⟨tF', hdtF'⟩ => ?_⟩
      · dsimp only [shiftElem] at hltH' hdt'
        rw [hsrcLen] at hh'Le
        have hdFull := lex_derives_slice_bwd hok hlh hhiLe hclose29 hh'Le hdt'
        rw [show lo + (eO.i - lo) = eO.i from by omega] at hdFull
        exact heOMax (lo + h') (by omega) (by omega) ⟨_, hdFull⟩
      · dsimp only [shiftElem] at hhasSub hjLtSrc hdtF'
        rw [hsrcLen] at hjLtSrc
        have hhasEq : (shiftCodeTree lo eO.tree).has .NumericLiteral (eO.i - lo) (eO.j - lo) =
            eO.tree.has .NumericLiteral eO.i eO.j := by
          obtain ⟨K, hK⟩ := heODer
          have hs := hK (max K 1) (Nat.le_max_left K 1)
          obtain ⟨k0, hk0⟩ : ∃ k0, max K 1 = k0 + 1 := ⟨max K 1 - 1, by omega⟩
          rw [hk0] at hs
          exact (code_step_has_shift hok (treeSize eO.tree)).1 (Nat.le_refl _) heOiLo hs heOiLo (by omega)
        rw [hhasEq] at hhasSub
        have hdFFull := lex_derives_slice_bwd hok hlh hhiLe hclose29 (by omega) hdtF'
        rw [show lo + (eO.j - lo) = eO.j from by omega,
            show lo + (eO.j - lo + 1) = eO.j + 1 from by omega] at hdFFull
        exact heOFol hhasSub (by omega) nF hnF ⟨_, hdFFull⟩
  -- Prove `elsShifted.filter Element.isToken = (slice es a0 b0).map (shiftElem lo)` and `tokensOf` equality:
  have helsTakeSplit : ∀ k, k ≤ idxB + 1 - idxA →
      (els.take (idxA + k)).filter Element.isToken =
        es.take a0 ++ (elsRaw.take k).filter Element.isToken := by
    intro k hk
    have hsplit : els.take (idxA + k) = els.take idxA ++ elsRaw.take k := by
      dsimp only [elsRaw]; unfold slice
      rw [List.take_take, Nat.min_eq_left hk]
      have h1 : idxA ≤ idxA + k := by omega
      rw [← List.take_append_drop idxA (els.take (idxA + k)), List.take_take, Nat.min_eq_left h1,
          List.drop_take]
      simp
    rw [hsplit, List.filter_append, htakeA]
  have helsRawFilt : elsRaw.filter Element.isToken = slice es a0 b0 := by
    have hkMax := helsTakeSplit (idxB + 1 - idxA) (Nat.le_refl _)
    rw [show idxA + (idxB + 1 - idxA) = idxB + 1 from by omega,
        ← helsRawLen, List.take_length] at hkMax
    have htakeB1 : (els.take (idxB + 1)).filter Element.isToken = es.take b0 := by
      have h1 : els.take (idxB + 1) = els.take idxB ++ [eB] :=
        List.take_add_one.trans (by simp [helsB])
      have h2 : es.take b0 = es.take (b0 - 1) ++ [eB] := by
        rw [show b0 = (b0 - 1) + 1 from by omega]
        exact List.take_add_one.trans (by simp [hesB])
      rw [h1, List.filter_append, List.filter_cons_of_pos heBTok, List.filter_nil, htakeB, h2]
    rw [htakeB1] at hkMax
    have h3 : es.take b0 = es.take a0 ++ slice es a0 b0 := by
      unfold slice
      rw [← List.take_append_drop a0 (es.take b0), List.take_take, Nat.min_eq_left (Nat.le_of_lt ha0LtB0),
          List.drop_take]
    exact List.append_cancel_left (hkMax.symm.trans h3)
  have helsShiftedFilt : elsShifted.filter Element.isToken = (slice es a0 b0).map (shiftElem lo) := by
    have hfltMap : ∀ l : List Element, (l.map (shiftElem lo)).filter Element.isToken =
        (l.filter Element.isToken).map (shiftElem lo) := by
      intro l; induction l with
      | nil => rfl
      | cons hd tl ih =>
        rw [List.map_cons, List.filter_cons, shiftElem_isToken, List.filter_cons]
        cases hd.isToken <;> simp [ih]
    rw [hfltMap, helsRawFilt]
  have hfiltSub : toksSub.filter (·.virt.isNone) = tokensOf src elsShifted := by
    -- Show both sides have length `b0 - a0` and agree at every `r < b0 - a0`:
    have hsl0 := slice_getElem? toks (lo := i) (hi := j) (k := 0) (by omega)
    rw [Nat.add_zero, htf] at hsl0
    have hfltLHS : toksSub.filter (·.virt.isNone) = clearHeadLT (slice (tokensOf fullSrc els) a0 b0) := by
      dsimp only [toksSub]
      cases hsl : slice toks i j with
      | nil => rw [hsl] at hsl0; cases hsl0
      | cons x0 xr =>
        rw [hsl, List.getElem?_cons_zero, Option.some.injEq] at hsl0
        subst hsl0
        rw [clearHeadLT_filter_isNone_of_head_real htfV, ← hsl,
            filter_slice_toks toks (Nat.le_of_lt hij) hj, hfilt]
    rw [hfltLHS]
    obtain ⟨htokSubLen, htokSubGet⟩ := tokensOf_map_es src elsShifted
    have hlenLHS : (clearHeadLT (slice (tokensOf fullSrc els) a0 b0)).length = b0 - a0 := by
      rw [clearHeadLT_length, slice_length_eq _ (Nat.le_of_lt ha0LtB0) (htokOfLen ▸ hb0LeEs)]
    have hlenRHS : (tokensOf src elsShifted).length = b0 - a0 := by
      rw [htokSubLen, helsShiftedFilt, List.length_map, slice_length_eq _ (Nat.le_of_lt ha0LtB0) hb0LeEs]
    apply List.ext_getElem (hlenLHS.trans hlenRHS.symm)
    intro r hr1 hr2
    have hrLt : r < b0 - a0 := hlenLHS ▸ hr1
    -- Match element `r` of `elsShifted.zipIdx.filter (·.1.isToken)` with `zEs[a0 + r]`:
    obtain ⟨hzSubFst, hzSubProps⟩ := zipIdx_filter_isToken_props elsShifted
    have hzSubLen : (elsShifted.zipIdx.filter (fun p => p.1.isToken)).length = b0 - a0 := by
      rw [← List.length_map (f := Prod.fst), hzSubFst, helsShiftedFilt, List.length_map,
          slice_length_eq _ (Nat.le_of_lt ha0LtB0) hb0LeEs]
    rcases hzsR : (elsShifted.zipIdx.filter (fun p => p.1.isToken))[r]'(hzSubLen ▸ hrLt) with ⟨eSubR, kSub⟩
    have hzsR? : (elsShifted.zipIdx.filter (fun p => p.1.isToken))[r]? = some (eSubR, kSub) :=
      (List.getElem?_eq_getElem (hzSubLen ▸ hrLt)).trans (congrArg some hzsR)
    obtain ⟨hkSubLt, helsSubK, heSubTok, htakeSubK⟩ := hzSubProps r (eSubR, kSub) hzsR?
    dsimp only at hkSubLt helsSubK heSubTok htakeSubK
    have hkSubLtR : kSub < idxB + 1 - idxA := by simpa [elsShifted, helsRawLen] using hkSubLt
    have helsSubK' := helsSubK
    dsimp only [elsShifted] at helsSubK'
    rw [List.getElem?_map, helsRawGet kSub hkSubLtR] at helsSubK'
    obtain ⟨eOrigR, helsOrigR, heSubEq⟩ := Option.map_eq_some_iff.mp helsSubK'
    -- Also `((els.take (idxA + kSub)).filter Element.isToken).length = a0 + r` and `eOrigR.isToken = true`:
    have heOrigTok : eOrigR.isToken = true := by rw [← shiftElem_isToken lo, heSubEq]; exact heSubTok
    have htakeOrigLen : ((els.take (idxA + kSub)).filter Element.isToken).length = a0 + r := by
      rw [helsTakeSplit kSub (Nat.le_of_lt hkSubLtR), List.length_append]
      have hlenA0 : (es.take a0).length = a0 := List.length_take_of_le (by omega)
      have hlenR : ((elsRaw.take kSub).filter Element.isToken).length = r := by
        have hmapFlt : ∀ l : List Element,
            (l.map (shiftElem lo)).filter Element.isToken = (l.filter Element.isToken).map (shiftElem lo) := by
          intro l; induction l with
          | nil => rfl
          | cons hd tl ih =>
            rw [List.map_cons, List.filter_cons, shiftElem_isToken, List.filter_cons]
            cases hd.isToken <;> simp [ih]
        have hmapTk : (elsShifted.take kSub).filter Element.isToken =
            ((elsRaw.take kSub).filter Element.isToken).map (shiftElem lo) := by
          dsimp only [elsShifted]; rw [← List.map_take]; exact hmapFlt _
        have := congrArg List.length htakeSubK
        rw [hmapTk, List.length_map, List.length_take_of_le (by rw [helsShiftedFilt, List.length_map, slice_length_eq _ (Nat.le_of_lt ha0LtB0) hb0LeEs]; omega)] at this
        exact this
      omega
    -- Show `zEs[a0 + r]? = some (eOrigR, idxA + kSub)`:
    have hzrLt : a0 + r < zEs.length := hzLen ▸ (by omega)
    rcases hzr : zEs[a0 + r]'hzrLt with ⟨eZ, kZ⟩
    have hzr? : zEs[a0 + r]? = some (eZ, kZ) := (List.getElem?_eq_getElem hzrLt).trans (congrArg some hzr)
    obtain ⟨hkZLt, helsZ, heZTok, htakeZ⟩ := hzProps (a0 + r) (eZ, kZ) hzr?
    dsimp only at hkZLt helsZ heZTok htakeZ
    have htakeZLen : ((els.take kZ).filter Element.isToken).length = a0 + r := by
      rw [htakeZ, List.length_take_of_le (by omega)]
    have hkZEq : kZ = idxA + kSub := by
      by_cases hlt1 : kZ < idxA + kSub
      · exfalso
        have hsp1 : els.take (idxA + kSub) = els.take kZ ++ (eZ :: slice els (kZ + 1) (idxA + kSub)) := by
          have ha1 : els.take (idxA + kSub) = els.take (kZ + 1) ++ slice els (kZ + 1) (idxA + kSub) := by
            unfold slice; rw [← List.take_append_drop (kZ + 1) (els.take (idxA + kSub)),
              List.take_take, Nat.min_eq_left (by omega), List.drop_take]
          have ha2 : els.take (kZ + 1) = els.take kZ ++ [eZ] := List.take_add_one.trans (by simp [helsZ])
          rw [ha1, ha2, List.append_assoc, List.singleton_append]
        rw [hsp1, List.filter_append, List.filter_cons_of_pos heZTok, List.length_append, List.length_cons, htakeZLen] at htakeOrigLen
        omega
      · by_cases hlt2 : idxA + kSub < kZ
        · exfalso
          have hsp2 : els.take kZ = els.take (idxA + kSub) ++ (eOrigR :: slice els (idxA + kSub + 1) kZ) := by
            have ha1 : els.take kZ = els.take (idxA + kSub + 1) ++ slice els (idxA + kSub + 1) kZ := by
              unfold slice; rw [← List.take_append_drop (idxA + kSub + 1) (els.take kZ),
                List.take_take, Nat.min_eq_left (by omega), List.drop_take]
            have ha2 : els.take (idxA + kSub + 1) = els.take (idxA + kSub) ++ [eOrigR] :=
              List.take_add_one.trans (by simp [helsOrigR])
            rw [ha1, ha2, List.append_assoc, List.singleton_append]
          rw [hsp2, List.filter_append, List.filter_cons_of_pos heOrigTok, List.length_append, List.length_cons, htakeOrigLen] at htakeZLen
          omega
        · omega
    subst hkZEq
    rw [helsOrigR] at helsZ; injection helsZ with heZEq; subst heZEq
    have heOrigLo : lo ≤ eOrigR.i := by
      rw [hloEq]; exact (helemOrd idxA (idxA + kSub) eA eOrigR (by omega) helsA helsOrigR).1
    have heOrigHi : eOrigR.j ≤ hi := by
      rw [hhiEq]
      by_cases heqB : idxA + kSub = idxB
      · subst heqB; rw [helsOrigR] at helsB; injection helsB with he; subst he; exact Nat.le_refl _
      · exact Nat.le_trans ((helemOrd (idxA + kSub) idxB eOrigR eB (by omega) helsOrigR helsB).2 (by omega))
          (Nat.le_of_lt heBiLt)
    -- Compare `[r]?` on both sides:
    apply Option.some.inj
    rw [← List.getElem?_eq_getElem hr1, ← List.getElem?_eq_getElem hr2, htokSubGet r, hzsR?, Option.map_some]
    cases r with
    | zero =>
      have hkSub0 : kSub = 0 := by
        by_cases h0 : kSub = 0
        · exact h0
        · exfalso
          have hsp0 : elsRaw.take kSub = eA :: (elsRaw.drop 1).take (kSub - 1) := by
            have hg0 := helsRawGet 0 (by omega)
            rw [Nat.add_zero, helsA] at hg0
            cases hrw : elsRaw with
            | nil => rw [hrw] at hg0; cases hg0
            | cons x0 xr =>
              rw [hrw, List.getElem?_cons_zero, Option.some.injEq] at hg0
              subst hg0
              obtain ⟨m0, rfl⟩ : ∃ m0, kSub = m0 + 1 := ⟨kSub - 1, by omega⟩
              simp
          rw [Nat.add_zero] at htakeOrigLen
          rw [helsTakeSplit kSub (Nat.le_of_lt hkSubLtR), hsp0, List.filter_cons_of_pos heATok,
              List.length_append, List.length_cons, List.length_take_of_le (by omega)] at htakeOrigLen
          omega
      subst hkSub0
      rw [Nat.add_zero, helsA] at helsOrigR; injection helsOrigR with heq; subst heq; subst heSubEq
      have hslTok0 := slice_getElem? (tokensOf fullSrc els) (lo := a0) (hi := b0) (k := 0) (by omega)
      rw [Nat.add_zero, htokOfGet a0, hza?, Option.map_some] at hslTok0
      cases hslT : slice (tokensOf fullSrc els) a0 b0 with
      | nil => rw [hslT] at hslTok0; cases hslTok0
      | cons t0 tr =>
        rw [hslT, List.getElem?_cons_zero, Option.some.injEq] at hslTok0
        subst hslTok0
        dsimp only [src]
        simp [clearHeadLT, shiftElem, slice_of_slice fullSrc heOrigLo heOrigHi]
    | succ r0 =>
      have hkSubPos : 0 < kSub := by
        by_cases h0 : kSub = 0
        · exfalso
          subst h0
          rw [Nat.add_zero, htakeA, List.length_take_of_le (by omega)] at htakeOrigLen
          omega
        · omega
      rw [clearHeadLT_getElem?_pos _ (Nat.zero_lt_succ r0), slice_getElem? _ hrLt,
          htokOfGet (a0 + (r0 + 1)), hzr?, Option.map_some]
      subst heSubEq
      dsimp only [src]
      simp only [Option.some.injEq, shiftElem]
      rw [slice_of_slice fullSrc heOrigLo heOrigHi]
      refine congrArg (Token.mk _ · none) ?_
      -- Compare `before.any (·.breaks ...)`:
      have htwSplit : (els.take (idxA + kSub)).reverse.takeWhile (fun (x : Element) => !x.isToken) =
          (elsRaw.take kSub).reverse.takeWhile (fun (x : Element) => !x.isToken) := by
        have hraw0 : elsRaw.take kSub = eA :: slice els (idxA + 1) (idxA + kSub) := by
          dsimp only [elsRaw]; unfold slice
          rw [List.take_take, Nat.min_eq_left (Nat.le_of_lt hkSubLtR)]
          have hd : els.drop idxA = eA :: els.drop (idxA + 1) :=
            List.drop_eq_getElem_cons hidxALt |>.trans (by
              have : els[idxA] = eA := Option.some.inj ((List.getElem?_eq_getElem hidxALt).symm.trans helsA)
              rw [this])
          have hkSubSub : idxA + kSub - (idxA + 1) = kSub - 1 := by omega
          rw [hd, hkSubSub]
          conv => lhs; rw [show kSub = (kSub - 1) + 1 from by omega, List.take_succ_cons]
        have hfull : els.take (idxA + kSub) = els.take idxA ++ elsRaw.take kSub := by
          dsimp only [elsRaw]; unfold slice
          rw [List.take_take, Nat.min_eq_left (Nat.le_of_lt hkSubLtR)]
          rw [← List.take_append_drop idxA (els.take (idxA + kSub)), List.take_take,
              Nat.min_eq_left (by omega), List.drop_take]
          simp
        rw [hfull, hraw0, List.reverse_append, List.reverse_cons, List.append_assoc, List.singleton_append]
        have htwApp : ∀ (l1 l2 : List Element),
            (l1 ++ (eA :: l2)).takeWhile (fun (x : Element) => !x.isToken) =
              (l1 ++ [eA]).takeWhile (fun (x : Element) => !x.isToken) := by
          intro l1 l2; induction l1 with
          | nil => simp [heATok]
          | cons x xs ih =>
            simp only [List.cons_append, List.takeWhile_cons]
            cases (!x.isToken) <;> simp [ih]
        exact htwApp _ _
      have htwMap : (elsShifted.take kSub).reverse.takeWhile (fun (x : Element) => !x.isToken) =
          ((elsRaw.take kSub).reverse.takeWhile (fun (x : Element) => !x.isToken)).map (shiftElem lo) := by
        dsimp only [elsShifted]
        rw [← List.map_take, ← List.map_reverse]
        generalize (elsRaw.take kSub).reverse = l
        induction l with
        | nil => rfl
        | cons x xs ih =>
          rw [List.map_cons, List.takeWhile_cons, shiftElem_isToken, List.takeWhile_cons]
          cases (!x.isToken) <;> simp [ih]
      rw [htwMap, htwSplit]
      have hmemTW : ∀ {α : Type} (p : α → Bool) (l : List α) {x : α}, x ∈ l.takeWhile p → x ∈ l := by
        intro α p l; induction l with
        | nil => intro _ h; nomatch h
        | cons a as iha =>
          intro x h; rw [List.takeWhile_cons] at h
          cases hp : p a with
          | false => simp [hp] at h
          | true =>
            simp only [hp, ↓reduceIte, List.mem_cons] at h
            rcases h with rfl | h2
            · exact List.mem_cons_self ..
            · exact List.mem_cons_of_mem _ (iha h2)
      have hmemBounds : ∀ x ∈ (elsRaw.take kSub).reverse.takeWhile (fun (x : Element) => !x.isToken), lo ≤ x.i ∧ x.j ≤ hi := by
        intro x hx
        have hxRev := hmemTW _ _ hx
        have hxTake := List.mem_reverse.mp hxRev
        have hxRaw := List.mem_of_mem_take hxTake
        obtain ⟨m, hmLt, rfl⟩ := List.getElem_of_mem hxRaw
        rw [helsRawLen] at hmLt
        have hmEls : idxA + m < els.length := by omega
        have helsM : els[idxA + m]? = some elsRaw[m] := by
          rw [← helsRawGet m hmLt, List.getElem?_eq_getElem (by rwa [helsRawLen])]
        refine ⟨hloEq ▸ (helemOrd idxA (idxA + m) eA _ (by omega) helsA helsM).1, ?_⟩
        rw [hhiEq]
        by_cases heqB : idxA + m = idxB
        · subst heqB; rw [helsM] at helsB; injection helsB with he; subst he; exact Nat.le_refl _
        · exact Nat.le_trans ((helemOrd (idxA + m) idxB _ eB (by omega) helsM helsB).2 (by omega))
            (Nat.le_of_lt heBiLt)
      generalize (elsRaw.take kSub).reverse.takeWhile (fun (x : Element) => !x.isToken) = bef at hmemBounds ⊢
      induction bef with
      | nil => rfl
      | cons x xs ih =>
        obtain ⟨hxi, hxj⟩ := hmemBounds x (List.mem_cons_self ..)
        simp only [List.map_cons, List.any_cons, shiftElem_breaks hxi hxj,
          ih (fun y hy => hmemBounds y (List.mem_cons_of_mem _ hy))]
  -- `toksSub.all`:
  have hallSub : toksSub.all (fun k => k.virt.isNone || !k.lt) = true := by
    rw [List.all_eq_true]
    intro tk htkMem
    dsimp only [toksSub] at htkMem
    cases hsl : slice toks i j with
    | nil => rw [hsl] at htkMem; nomatch htkMem
    | cons x0 xr =>
      rw [hsl, clearHeadLT] at htkMem
      rcases List.mem_cons.mp htkMem with rfl | hmemXr
      · simp
      · have hmemSl : tk ∈ slice toks i j := by rw [hsl]; exact List.mem_cons_of_mem _ hmemXr
        obtain ⟨idx, hidxLt, rfl⟩ := List.getElem_of_mem hmemSl
        rw [slice_length_eq toks (Nat.le_of_lt hij) hj] at hidxLt
        have hg := slice_getElem? toks hidxLt
        rw [List.getElem?_eq_getElem (by rwa [slice_length_eq toks (Nat.le_of_lt hij) hj])] at hg
        exact List.all_eq_true.mp hall _ (List.mem_of_getElem? hg.symm)
  -- `tokenSpan` shift for `i ≤ u ≤ v ≤ j` and `u < j`:
  have hspanSub : ∀ u v, i ≤ u → u ≤ v → v ≤ j → u < j →
      Ecma.Grammar.tokenSpan elsShifted toksSub (u - i) (v - i) =
        ((Ecma.Grammar.tokenSpan els toks u v).1 - lo, (Ecma.Grammar.tokenSpan els toks u v).2 - lo) ∧
      lo ≤ (Ecma.Grammar.tokenSpan els toks u v).1 ∧
      (Ecma.Grammar.tokenSpan els toks u v).1 ≤ (Ecma.Grammar.tokenSpan els toks u v).2 ∧
      (Ecma.Grammar.tokenSpan els toks u v).2 ≤ hi := by
    intro u v hiu huv hvj huj
    let ru := (toksSub.take (u - i)).countP (·.virt.isNone)
    let rv := (toksSub.take (v - i)).countP (·.virt.isNone)
    have hcu0 : ru + a0 = (toks.take u).countP (·.virt.isNone) := by
      dsimp only [ru, toksSub, a0]
      have h := countP_clearHeadLT_slice toks (Nat.le_of_lt hij) hj (u := u - i) (by omega)
      rwa [show i + (u - i) = u from by omega] at h
    have hcv0 : rv + a0 = (toks.take v).countP (·.virt.isNone) := by
      dsimp only [rv, toksSub, a0]
      have h := countP_clearHeadLT_slice toks (Nat.le_of_lt hij) hj (u := v - i) (by omega)
      rwa [show i + (v - i) = v from by omega] at h
    have huCntLe : (toks.take u).countP (·.virt.isNone) ≤ b0 - 1 := by
      rw [hb0Sub1]; exact countP_take_mono _ toks (by omega)
    have hvCntLe : (toks.take v).countP (·.virt.isNone) ≤ b0 :=
      countP_take_mono _ toks hvj
    have hruLt : ru < b0 - a0 := by omega
    have hruLeRv : ru ≤ rv := countP_take_mono _ toksSub (by omega)
    have hrvLe : rv ≤ b0 - a0 := by omega
    have hauLt : a0 + ru < zEs.length := hzLen ▸ (by omega)
    rcases hzu : zEs[a0 + ru]'hauLt with ⟨eU, idxU⟩
    have hzu? : zEs[a0 + ru]? = some (eU, idxU) := (List.getElem?_eq_getElem hauLt).trans (congrArg some hzu)
    obtain ⟨_, helsU, heUTok, htakeU⟩ := hzProps (a0 + ru) (eU, idxU) hzu?
    dsimp only at helsU heUTok htakeU
    have hesU : es[a0 + ru]? = some eU := by rw [hesGet (a0 + ru) hauLt, hzu]
    have hesSubU : (elsShifted.filter Element.isToken)[ru]? = some (shiftElem lo eU) := by
      rw [helsShiftedFilt, List.getElem?_map, slice_getElem? es hruLt, hesU]; rfl
    have hidxAU : idxA ≤ idxU := by
      by_cases hle : idxA ≤ idxU
      · exact hle
      · exfalso
        have hsp1 : els.take idxA = els.take idxU ++ (eU :: slice els (idxU + 1) idxA) := by
          have ha1 : els.take idxA = els.take (idxU + 1) ++ slice els (idxU + 1) idxA := by
            unfold slice; rw [← List.take_append_drop (idxU + 1) (els.take idxA), List.take_take, Nat.min_eq_left (by omega), List.drop_take]
          have ha2 : els.take (idxU + 1) = els.take idxU ++ [eU] := List.take_add_one.trans (by simp [helsU])
          rw [ha1, ha2, List.append_assoc, List.singleton_append]
        have hlenA0 : ((els.take idxA).filter Element.isToken).length = a0 := by
          rw [htakeA, List.length_take_of_le (by omega)]
        have hlenU : ((els.take idxU).filter Element.isToken).length = a0 + ru := by
          rw [htakeU, List.length_take_of_le (by omega)]
        rw [hsp1, List.filter_append, List.filter_cons_of_pos heUTok, List.length_append, List.length_cons, hlenU] at hlenA0
        omega
    have hidxUB : idxU ≤ idxB := by
      by_cases hle : idxU ≤ idxB
      · exact hle
      · exfalso
        have hsp1 : els.take idxU = els.take idxB ++ (eB :: slice els (idxB + 1) idxU) := by
          have ha1 : els.take idxU = els.take (idxB + 1) ++ slice els (idxB + 1) idxU := by
            unfold slice; rw [← List.take_append_drop (idxB + 1) (els.take idxU), List.take_take, Nat.min_eq_left (by omega), List.drop_take]
          have ha2 : els.take (idxB + 1) = els.take idxB ++ [eB] := List.take_add_one.trans (by simp [helsB])
          rw [ha1, ha2, List.append_assoc, List.singleton_append]
        have hlenB : ((els.take idxB).filter Element.isToken).length = b0 - 1 := by
          rw [htakeB, List.length_take_of_le (by omega)]
        have hlenU : ((els.take idxU).filter Element.isToken).length = a0 + ru := by
          rw [htakeU, List.length_take_of_le (by omega)]
        rw [hsp1, List.filter_append, List.filter_cons_of_pos heBTok, List.length_append, List.length_cons, hlenB] at hlenU
        omega
    have heUiLo : lo ≤ eU.i := hloEq ▸ (helemOrd idxA idxU eA eU hidxAU helsA helsU).1
    have heUiHi : eU.i ≤ hi := by
      rw [hhiEq]
      exact Nat.le_trans ((helemOrd idxU idxB eU eB hidxUB helsU helsB).1) (Nat.le_of_lt heBiLt)
    have hcu' : (toks.take u).countP (·.virt.isNone) = a0 + ru := by omega
    have hcv' : (toks.take v).countP (·.virt.isNone) = a0 + rv := by omega
    by_cases hltR : ru < rv
    · have hltR' : a0 + ru < a0 + rv := by omega
      have hav1Lt : a0 + rv - 1 < zEs.length := hzLen ▸ (by omega)
      rcases hzv : zEs[a0 + rv - 1]'hav1Lt with ⟨eV, idxV⟩
      have hzv? : zEs[a0 + rv - 1]? = some (eV, idxV) := (List.getElem?_eq_getElem hav1Lt).trans (congrArg some hzv)
      obtain ⟨_, helsV, heVTok, htakeV⟩ := hzProps (a0 + rv - 1) (eV, idxV) hzv?
      dsimp only at helsV heVTok htakeV
      have hesV : es[a0 + rv - 1]? = some eV := by rw [hesGet (a0 + rv - 1) hav1Lt, hzv]
      have hesSubV : (elsShifted.filter Element.isToken)[rv - 1]? = some (shiftElem lo eV) := by
        rw [helsShiftedFilt, List.getElem?_map, slice_getElem? es (by omega),
            show a0 + (rv - 1) = a0 + rv - 1 from by omega, hesV]; rfl
      have hidxUV : idxU ≤ idxV := by
        by_cases hle : idxU ≤ idxV
        · exact hle
        · exfalso
          have hsp1 : els.take idxU = els.take idxV ++ (eV :: slice els (idxV + 1) idxU) := by
            have ha1 : els.take idxU = els.take (idxV + 1) ++ slice els (idxV + 1) idxU := by
              unfold slice; rw [← List.take_append_drop (idxV + 1) (els.take idxU), List.take_take, Nat.min_eq_left (by omega), List.drop_take]
            have ha2 : els.take (idxV + 1) = els.take idxV ++ [eV] := List.take_add_one.trans (by simp [helsV])
            rw [ha1, ha2, List.append_assoc, List.singleton_append]
          have hlenU : ((els.take idxU).filter Element.isToken).length = a0 + ru := by rw [htakeU, List.length_take_of_le (by omega)]
          have hlenV : ((els.take idxV).filter Element.isToken).length = a0 + rv - 1 := by rw [htakeV, List.length_take_of_le (by omega)]
          rw [hsp1, List.filter_append, List.filter_cons_of_pos heVTok, List.length_append, List.length_cons, hlenV] at hlenU
          omega
      have hidxVB : idxV ≤ idxB := by
        by_cases hle : idxV ≤ idxB
        · exact hle
        · exfalso
          have hsp1 : els.take idxV = els.take idxB ++ (eB :: slice els (idxB + 1) idxV) := by
            have ha1 : els.take idxV = els.take (idxB + 1) ++ slice els (idxB + 1) idxV := by
              unfold slice; rw [← List.take_append_drop (idxB + 1) (els.take idxV), List.take_take, Nat.min_eq_left (by omega), List.drop_take]
            have ha2 : els.take (idxB + 1) = els.take idxB ++ [eB] := List.take_add_one.trans (by simp [helsB])
            rw [ha1, ha2, List.append_assoc, List.singleton_append]
          have hlenB : ((els.take idxB).filter Element.isToken).length = b0 - 1 := by rw [htakeB, List.length_take_of_le (by omega)]
          have hlenV : ((els.take idxV).filter Element.isToken).length = a0 + rv - 1 := by rw [htakeV, List.length_take_of_le (by omega)]
          rw [hsp1, List.filter_append, List.filter_cons_of_pos heBTok, List.length_append, List.length_cons, hlenB] at hlenV
          omega
      have heUiLeVj : eU.i ≤ eV.j := by
        have := (helemOrd idxU idxV eU eV hidxUV helsU helsV).1
        have := (helemStep idxV eV helsV).1
        omega
      have heVjHi : eV.j ≤ hi := by
        rw [hhiEq]
        by_cases heqVB : idxV = idxB
        · subst heqVB; rw [helsV] at helsB; injection helsB with he; subst he; exact Nat.le_refl _
        · exact Nat.le_trans ((helemOrd idxV idxB eV eB hidxVB helsV helsB).2 (by omega)) (Nat.le_of_lt heBiLt)
      have hspSubUV : Ecma.Grammar.tokenSpan elsShifted toksSub (u - i) (v - i) = (eU.i - lo, eV.j - lo) := by
        unfold Ecma.Grammar.tokenSpan
        change (let s0 := ((elsShifted.filter Element.isToken)[ru]?.map (·.i)).getD _;
                if ru < rv then (s0, ((elsShifted.filter Element.isToken)[rv - 1]?.map (·.j)).getD s0) else (s0, s0)) = _
        simp [hltR, hesSubU, hesSubV, shiftElem]
      have hspOrigUV : Ecma.Grammar.tokenSpan els toks u v = (eU.i, eV.j) := by
        unfold Ecma.Grammar.tokenSpan
        change (let s0 := (es[(toks.take u).countP (·.virt.isNone)]?.map (·.i)).getD _;
                if (toks.take u).countP (·.virt.isNone) < (toks.take v).countP (·.virt.isNone)
                then (s0, (es[(toks.take v).countP (·.virt.isNone) - 1]?.map (·.j)).getD s0) else (s0, s0)) = _
        rw [hcu', hcv']
        simp [hltR', hesU, hesV]
      rw [hspSubUV, hspOrigUV]
      exact ⟨rfl, heUiLo, heUiLeVj, heVjHi⟩
    · have hltR' : ¬ (a0 + ru < a0 + rv) := by omega
      have hspSubUV : Ecma.Grammar.tokenSpan elsShifted toksSub (u - i) (v - i) = (eU.i - lo, eU.i - lo) := by
        unfold Ecma.Grammar.tokenSpan
        change (let s0 := ((elsShifted.filter Element.isToken)[ru]?.map (·.i)).getD _;
                if ru < rv then (s0, ((elsShifted.filter Element.isToken)[rv - 1]?.map (·.j)).getD s0) else (s0, s0)) = _
        simp [hltR, hesSubU, shiftElem]
      have hspOrigUV : Ecma.Grammar.tokenSpan els toks u v = (eU.i, eU.i) := by
        unfold Ecma.Grammar.tokenSpan
        change (let s0 := (es[(toks.take u).countP (·.virt.isNone)]?.map (·.i)).getD _;
                if (toks.take u).countP (·.virt.isNone) < (toks.take v).countP (·.virt.isNone)
                then (s0, (es[(toks.take v).countP (·.virt.isNone) - 1]?.map (·.j)).getD s0) else (s0, s0)) = _
        rw [hcu', hcv']
        simp [hltR', hesU]
      rw [hspSubUV, hspOrigUV]
      exact ⟨rfl, heUiLo, Nat.le_refl _, heUiHi⟩
  -- Real token span bound `(tokenSpan els toks u (u + 1)).1 + tk.text.length ≤ hi`:
  have htokLenHi : ∀ u tk, i ≤ u → u < j → toks[u]? = some tk → tk.virt = none →
      (Ecma.Grammar.tokenSpan els toks u (u + 1)).1 + tk.text.length ≤ hi := by
    intro u tk hiu huj hgetU hvU
    obtain ⟨hcU1, hfltU, _⟩ := filter_idx_real_tok toks hgetU hvU
    let rU := (toks.take u).countP (·.virt.isNone)
    have hrULtB0 : rU < b0 := by
      have : rU ≤ b0 - 1 := hb0Sub1 ▸ countP_take_mono _ toks (by omega)
      omega
    have hrULtZ : rU < zEs.length := hzLen ▸ Nat.lt_of_lt_of_le hrULtB0 hb0LeEs
    rcases hzU : zEs[rU]'hrULtZ with ⟨eU, idxU⟩
    have hzU? : zEs[rU]? = some (eU, idxU) := (List.getElem?_eq_getElem hrULtZ).trans (congrArg some hzU)
    have hesU : es[rU]? = some eU := by rw [hesGet rU hrULtZ, hzU]
    rw [hfilt] at hfltU
    rw [htokOfGet rU, hzU?, Option.map_some, Option.some.injEq] at hfltU
    have htxtU : tk.text = slice fullSrc eU.i eU.j := (congrArg Token.text hfltU).symm
    obtain ⟨_, helsU, _, _⟩ := hzProps rU (eU, idxU) hzU?
    obtain ⟨heUiLt, heUjLe, _, _⟩ := helemStep idxU eU helsU
    have hlenU : tk.text.length = eU.j - eU.i := by
      rw [htxtU, slice_length_eq fullSrc (Nat.le_of_lt heUiLt) heUjLe]
    have hspU : Ecma.Grammar.tokenSpan els toks u (u + 1) = (eU.i, eU.j) := by
      unfold Ecma.Grammar.tokenSpan
      change (let start := (es[(toks.take u).countP (·.virt.isNone)]?.map (·.i)).getD _;
              if (toks.take u).countP (·.virt.isNone) < (toks.take (u + 1)).countP (·.virt.isNone)
              then (start, (es[(toks.take (u + 1)).countP (·.virt.isNone) - 1]?.map (·.j)).getD start)
              else (start, start)) = _
      dsimp only [rU] at hesU
      rw [hcU1]; simp [hesU]
    obtain ⟨_, _, _, heUjHi⟩ := hspanSub u (u + 1) hiu (by omega) (by omega) huj
    rw [hspU] at heUjHi ⊢
    dsimp only at heUjHi ⊢
    omega
  refine ⟨hlh, hhiLe, hclose29, idxA, idxB, elsShifted, eA.j - lo,
    hidxALeB, hidxBLt, by omega, by rw [hsrcLen]; omega,
    by
      dsimp only [src]
      have h0 : 0 = eA.i - lo := by omega
      rw [htfTxtEq, h0, slice_of_slice fullSrc (Nat.le_of_eq hloEq) heAjLeHi],
    rfl, hscansSub, hfiltSub, hallSub, hspanSub, htokLenHi, ?_⟩
  intro k eSub hgetSub
  have hkLtS : k < elsShifted.length := (List.getElem?_eq_some_iff.mp hgetSub).1
  have hkLtR : k < idxB + 1 - idxA := by simpa [elsShifted, helsRawLen] using hkLtS
  dsimp only [elsShifted] at hgetSub
  rw [List.getElem?_map, helsRawGet k hkLtR] at hgetSub
  obtain ⟨eOrig, helsOrig, rfl⟩ := Option.map_eq_some_iff.mp hgetSub
  refine ⟨eOrig, helsOrig, rfl, fun heSubTok => ?_⟩
  let rSub := ((elsShifted.take k).filter Element.isToken).length
  have htakeOrigEq : ((els.take (idxA + k)).filter Element.isToken).length = a0 + rSub := by
    rw [helsTakeSplit k (Nat.le_of_lt hkLtR), List.length_append]
    have hlenA0 : (es.take a0).length = a0 := List.length_take_of_le (by omega)
    have hmapFlt : ∀ l : List Element,
        (l.map (shiftElem lo)).filter Element.isToken = (l.filter Element.isToken).map (shiftElem lo) := by
      intro l; induction l with
      | nil => rfl
      | cons hd tl ih =>
        rw [List.map_cons, List.filter_cons, shiftElem_isToken, List.filter_cons]
        cases hd.isToken <;> simp [ih]
    have hmapTk : (elsShifted.take k).filter Element.isToken =
        ((elsRaw.take k).filter Element.isToken).map (shiftElem lo) := by
      dsimp only [elsShifted]; rw [← List.map_take]; exact hmapFlt _
    have hrSubEq : rSub = ((elsRaw.take k).filter Element.isToken).length := by
      dsimp only [rSub]; rw [hmapTk, List.length_map]
    omega
  have hrSubLt : rSub < b0 - a0 := by
    have heOrigTok : eOrig.isToken = true := by rwa [shiftElem_isToken] at heSubTok
    have hltAll : ((elsShifted.take k).filter Element.isToken).length <
        (elsShifted.filter Element.isToken).length := by
      have hsp : elsShifted = elsShifted.take k ++ (shiftElem lo eOrig :: elsShifted.drop (k + 1)) := by
        conv => lhs; rw [← List.take_append_drop k elsShifted]
        have hd : elsShifted.drop k = shiftElem lo eOrig :: elsShifted.drop (k + 1) :=
          List.drop_eq_getElem_cons hkLtS |>.trans (by
            have hg : elsShifted[k]? = some (shiftElem lo eOrig) := by
              dsimp only [elsShifted]
              rw [List.getElem?_map, helsRawGet k hkLtR, helsOrig]; rfl
            rw [List.getElem?_eq_getElem hkLtS] at hg
            rw [Option.some.inj hg])
        rw [hd]
      conv => rhs; rw [hsp]
      rw [List.filter_append, List.filter_cons_of_pos heSubTok, List.length_append, List.length_cons]
      omega
    rw [helsShiftedFilt, List.length_map, slice_length_eq es (Nat.le_of_lt ha0LtB0) hb0LeEs] at hltAll
    exact hltAll
  obtain ⟨huSubLt, hridxEq, hr0Iff⟩ := realIdx_add_slice toks hij hj htf htfV htl htlV hrSubLt
  rw [htakeOrigEq, hridxEq]
  refine ⟨rfl, by omega, by omega, ?_⟩
  constructor
  · intro hk0; subst hk0; exact hr0Iff.mp rfl
  · intro huEq
    have hr0 : rSub = 0 := hr0Iff.mpr huEq
    by_cases hk0 : k = 0
    · exact hk0
    · exfalso
      have hsp0 : elsShifted.take k = shiftElem lo eA :: (elsShifted.drop 1).take (k - 1) := by
        have hg0 : elsShifted[0]? = some (shiftElem lo eA) := by
          dsimp only [elsShifted]
          rw [List.getElem?_map, helsRawGet 0 (by omega), Nat.add_zero, helsA]; rfl
        cases hsL : elsShifted with
        | nil => rw [hsL] at hg0; cases hg0
        | cons x0 xr =>
          rw [hsL, List.getElem?_cons_zero, Option.some.injEq] at hg0
          subst hg0
          obtain ⟨m0, rfl⟩ : ∃ m0, k = m0 + 1 := ⟨k - 1, by omega⟩
          simp
      have heAShTok : (shiftElem lo eA).isToken = true := by rw [shiftElem_isToken]; exact heATok
      dsimp only [rSub] at hr0
      rw [hsp0, List.filter_cons_of_pos heAShTok, List.length_cons] at hr0
      omega

private theorem syn_step_treeShiftRel (hok : parseTablesOk = true) {cx : Ctx} {toks : List Token}
    {lo hi i j : Nat} (hij : i < j) (hj : j ≤ toks.length)
    {sp1 sp2 : Nat → Nat → Nat × Nat}
    (hspSub : ∀ u v, i ≤ u → u ≤ v → v ≤ j → u < j →
      sp2 (u - i) (v - i) = ((sp1 u v).1 - lo, (sp1 u v).2 - lo) ∧
      lo ≤ (sp1 u v).1 ∧ (sp1 u v).1 ≤ (sp1 u v).2 ∧ (sp1 u v).2 ≤ hi)
    (htokHi : ∀ u tk, i ≤ u → u < j → toks[u]? = some tk → tk.virt = none →
      (sp1 u (u + 1)).1 + tk.text.length ≤ hi) :
    ∀ (sz : Nat) {m ps a b t}, treeSize t ≤ sz →
      i ≤ a → b ≤ j - 1 →
      Strict.PosSynStep cx Engine.Model.codePrims toks m ps a b t →
      TreeShiftRel lo hi sp1 sp2 t (shiftSynTree i t) := by
  intro sz
  induction sz using Nat.strongRecOn with
  | ind sz ih =>
    intro m ps a b t hsz hia hb hs
    have _ := hij; have _ := hj
    cases hs with
    | @lex _ _ _ subLex tokA _ hgA hleaf =>
      obtain ⟨hvA, ⟨K, hK⟩⟩ := hleaf
      have hsL := hK (max K 1) (Nat.le_max_left K 1)
      obtain ⟨k0, hk0⟩ : ∃ k0, max K 1 = k0 + 1 := ⟨max K 1 - 1, by omega⟩
      rw [hk0] at hsL
      obtain ⟨hspEq, haLo, _, _⟩ := hspSub a (a + 1) hia (by omega) (by omega) (by omega)
      have hbHi := htokHi a tokA hia (by omega) hgA hvA
      rw [shiftSynTree_lex]
      refine .lex ?_
      have h2eq : (fun x y => ((sp2 (a - i) (a - i + 1)).1 + x, (sp2 (a - i) (a - i + 1)).1 + y)) =
          (fun x y => (((sp1 a (a + 1)).1 - lo) + x, ((sp1 a (a + 1)).1 - lo) + y)) := by
        rw [show a - i + 1 = (a + 1) - i from by omega, hspEq]
      rw [h2eq]
      exact code_step_treeShiftRel hok haLo (treeSize subLex) (Nat.le_refl _) hbHi hsL
    | @node _ _ _ _ _ kids id s _ _ _ hseq =>
      dsimp only [treeSize] at hsz
      have hab := Strict.posSynSeq_le hseq
      obtain ⟨hspEq, haLo, _, hbHi⟩ := hspSub a b hia hab (by omega) (by omega)
      rw [shiftSynTree_node]
      have hfltMap : ∀ ks : List Tree,
          (ks.map (shiftSynTree i)).filter (!·.isLeaf) = (ks.filter (!·.isLeaf)).map (shiftSynTree i) := by
        intro ks; induction ks with
        | nil => rfl
        | cons kd kds ihk =>
          rw [List.map_cons, List.filter_cons, shiftSynTree_isLeaf, List.filter_cons]
          cases kd.isLeaf <;> simp [ihk]
      refine .node hspEq haLo hbHi (by rw [hfltMap kids, List.length_map]) (fun idx h1 h2 => ?_)
      have hkids := Strict.posSynSeq_child_step (by omega) hseq
      have hcIn : (kids.filter (!·.isLeaf))[idx] ∈ kids.filter (!·.isLeaf) := List.getElem_mem h1
      obtain ⟨mC, psC, aC, bC, haC, _, hbC, _, hstC⟩ := hkids _ hcIn
      have hszC := treeSize_mem_le (List.mem_filter.mp hcIn).1
      have hgetEq : ((kids.map (shiftSynTree i)).filter (!·.isLeaf))[idx] =
          shiftSynTree i (kids.filter (!·.isLeaf))[idx] := by
        apply Option.some.inj
        rw [← List.getElem?_eq_getElem h2, hfltMap kids, List.getElem?_map,
            List.getElem?_eq_getElem h1, Option.map_some]
      rw [hgetEq]
      exact ih (treeSize _) (by omega) (t := _) (Nat.le_refl _) (by omega) (by omega) hstC

private theorem arguments_treeShiftRel (hok : parseTablesOk = true) {cx : Ctx} {toks : List Token}
    {lo hi i h1 j : Nat} (hj : j ≤ toks.length) (hih1 : i ≤ h1)
    {sp1 sp2 : Nat → Nat → Nat × Nat}
    (hspSub : ∀ u v, i ≤ u → u ≤ v → v ≤ j → u < j →
      sp2 (u - i) (v - i) = ((sp1 u v).1 - lo, (sp1 u v).2 - lo) ∧
      lo ≤ (sp1 u v).1 ∧ (sp1 u v).1 ≤ (sp1 u v).2 ∧ (sp1 u v).2 ≤ hi)
    (htokHi : ∀ u tk, i ≤ u → u < j → toks[u]? = some tk → tk.virt = none →
      (sp1 u (u + 1)).1 + tk.text.length ≤ hi)
    {ps : List Param} {tArgs : Tree}
    (hst : Strict.PosSynStep cx Engine.Model.codePrims toks .Arguments ps h1 j tArgs) :
    TreeShiftRel lo hi sp1 sp2 tArgs (shiftSynTree i tArgs) := by
  obtain ⟨hh1Lt, _, hkidsB⟩ := arguments_pos_props hj hst
  cases hst with
  | lex hnil _ _ =>
    have hc1 := Bool.and_eq_true_iff.mp coverGoalsCert_true
    have hci := List.all_eq_true.mp hc1.2 (cxIdx cx) (List.mem_range.mpr (cxIdx_lt cx))
    rw [cxOfIdx_cxIdx] at hci
    rw [← glData_eq] at hnil; simp [hnil] at hci
  | @node _ _ _ _ _ kidsA idA _ _ _ _ _ =>
    obtain ⟨hspEq, haLo, _, hbHi⟩ := hspSub h1 j hih1 (Nat.le_of_lt hh1Lt) (Nat.le_refl j) hh1Lt
    rw [shiftSynTree_node]
    have hfltMap : ∀ ks : List Tree,
        (ks.map (shiftSynTree i)).filter (!·.isLeaf) = (ks.filter (!·.isLeaf)).map (shiftSynTree i) := by
      intro ks; induction ks with
      | nil => rfl
      | cons kd kds ihk =>
        rw [List.map_cons, List.filter_cons, shiftSynTree_isLeaf, List.filter_cons]
        cases kd.isLeaf <;> simp [ihk]
    refine .node hspEq haLo hbHi (by rw [hfltMap kidsA, List.length_map]) (fun idx h1 h2 => ?_)
    have hcIn : (kidsA.filter (!·.isLeaf))[idx] ∈ kidsA.filter (!·.isLeaf) := List.getElem_mem h1
    obtain ⟨mC, psC, aC, bC, haC, _, hbC, hstC⟩ := hkidsB _ hcIn
    have hgetEq : ((kidsA.map (shiftSynTree i)).filter (!·.isLeaf))[idx] =
        shiftSynTree i (kidsA.filter (!·.isLeaf))[idx] := by
      apply Option.some.inj
      rw [← List.getElem?_eq_getElem h2, hfltMap kidsA, List.getElem?_map,
          List.getElem?_eq_getElem h1, Option.map_some]
    rw [hgetEq]
    exact syn_step_treeShiftRel hok (by omega) hj hspSub htokHi (treeSize _) (Nat.le_refl _) (by omega) hbC hstC

/-! ## Section 7: `SynSub`, `relabel_core`, `ParsedInv`, and `Engine.Impl.coverLaws` -/

def SynSub (pc : ParseCx) (d : Node) : Prop :=
  let gx := Engine.grammarCx pc
  ∃ (st0 : Nat) (fullSrc : List Nat) (els : List Element) (toks : List Token)
    (subNt : NT) (p : Nat) (subPs : List Param) (i j : Nat) (kidsT : List Tree) (firstRoot : Bool),
    parseTablesOk = true ∧
    Scans Ecma.Spec.gl gx Engine.Model.codePrims fullSrc els ∧
    toks.filter (·.virt.isNone) = tokensOf fullSrc els ∧
    toks.all (fun k => k.virt.isNone || !k.lt) = true ∧
    (∀ k e, els[k]? = some e →
      if k == 0 && firstRoot then e.goal = .InputElementHashbangOrRegExp
      else if !e.isToken then e.goal = .InputElementDiv
      else
        let u := realIdx ((els.take k).filter Element.isToken).length toks
        i ≤ u → u < j → (Tree.node subNt p subPs i j kidsT).goalAt u = some e.goal) ∧
    j ≤ toks.length ∧
    Derives Ecma.Spec.gl gx .syntactic (tokenAlphabet Ecma.Spec.gl gx Engine.Model.codePrims)
      toks subNt subPs i j (.node subNt p subPs i j kidsT) ∧
    ForHeadersExplicit toks (.node subNt p subPs i j kidsT) ∧
    Ecma.Model.NodeRel Impl st0 fullSrc (Ecma.Grammar.tokenSpan els toks) d (.node subNt p subPs i j kidsT)

def ParsedInv (pc : ParseCx) (d : Node) : Prop :=
  NoCoverSub d ∨ SynSub pc d

private theorem setTreeRootPs_step_and_rel {cx : Ctx} {P : CodePrims} {inp : List Token}
    {neg : NT → List Param → Nat → Nat → Prop}
    {m : NT} {psOld psNew : List Param} {a b : Nat} {t : Tree}
    {st : Nat} {src : List Nat} {sp : Nat → Nat → Nat × Nat} {nd : Node}
    (hp : (match t with | .node _ _ _ _ _ _ => ∀ q, q ∈ psOld ↔ q ∈ psNew | _ => True))
    (hst : Step (tokenAlphabet Ecma.Spec.gl cx P) neg inp Ecma.Spec.gl cx .syntactic m psOld a b t)
    (hrel : Ecma.Model.NodeRel Impl st src sp nd t) :
    let t' := match t with
      | .node nt id _ i0 j0 ks => Tree.node nt id psNew i0 j0 ks
      | other => other
    Step (tokenAlphabet Ecma.Spec.gl cx P) neg inp Ecma.Spec.gl cx .syntactic m psNew a b t' ∧
    Ecma.Model.NodeRel Impl st src sp nd t' := by
  cases hst with
  | lex hnil hg hl =>
    exact ⟨.lex hnil hg hl, hrel⟩
  | @node _ _ _ _ _ ks id s hsMem hgrd hpid hseq =>
    dsimp only at hp ⊢
    exact ⟨step_congr_root_params hp (.node s hsMem hgrd hpid hseq),
           nodeRel_congr_root_params hp hrel⟩

private def setRootPs (psNew : List Param) : Tree → Tree
  | .node nt id _ i0 j0 ks => .node nt id psNew i0 j0 ks
  | other => other

private theorem setRootPs_step {cx : Ctx} {P : CodePrims} {inp : List Token}
    {neg : NT → List Param → Nat → Nat → Prop}
    {m : NT} {psOld psNew : List Param} {a b : Nat} {t : Tree}
    (hp : match t with | .node _ _ _ _ _ _ => ∀ q, q ∈ psOld ↔ q ∈ psNew | _ => True)
    (hst : Step (tokenAlphabet Ecma.Spec.gl cx P) neg inp Ecma.Spec.gl cx .syntactic m psOld a b t) :
    Step (tokenAlphabet Ecma.Spec.gl cx P) neg inp Ecma.Spec.gl cx .syntactic m psNew a b (setRootPs psNew t) := by
  cases hst with
  | lex hnil hg hl => exact .lex hnil hg hl
  | node s hsMem hgrd hpid hseq => exact step_congr_root_params hp (.node s hsMem hgrd hpid hseq)

private theorem setRootPs_props (psNew : List Param) (t : Tree) :
    (setRootPs psNew t).isLeaf = t.isLeaf ∧
    (setRootPs psNew t).nt? = t.nt? ∧
    (setRootPs psNew t).span = t.span ∧
    (∀ u, (setRootPs psNew t).goalAt u = t.goalAt u) ∧
    (∀ toks, ForHeadersExplicit toks (setRootPs psNew t) ↔ ForHeadersExplicit toks t) := by
  cases t <;> exact ⟨rfl, rfl, rfl, fun _ => rfl, fun _ => Iff.rfl⟩

private theorem present_paren_extract {cx : Ctx} {P : CodePrims} {toks : List Token}
    {neg : NT → List Param → Nat → Nat → Prop}
    {n : NT} {s : Src} (hsMem : s ∈ Ecma.Spec.gl.alts cx .syntactic n)
    {ps : List Param} {kIdx : Nat} {rhs : List Item} {i j : Nat} {mask : List Bool} {kidsT : List Tree}
    (hpres : Relabel.present rhs mask = sParen.alt.rhs)
    (hidx : ∀ u < rhs.length, s.alt.rhs[kIdx + u]? = rhs[u]?)
    (hseq : Ecma.Grammar.Seq (tokenAlphabet Ecma.Spec.gl cx P) neg toks Ecma.Spec.gl cx .syntactic
      s ps kIdx rhs i j mask kidsT) :
    ∃ h1 h2 psExpr tExpr tokOpen tokClose,
      kidsT = [.leaf i h1, tExpr, .leaf h2 j] ∧
      i < h1 ∧ h1 ≤ h2 ∧ h2 < j ∧
      toks[i]? = some tokOpen ∧ tokOpen.virt = none ∧ tokOpen.text = [0x28] ∧
      (j ≤ toks.length → h1 = i + 1 ∧ j = h2 + 1 ∧
        toks[j - 1]? = some tokClose ∧ tokClose.virt = none ∧ tokClose.text = [0x29]) ∧
      Step (tokenAlphabet Ecma.Spec.gl cx P) neg toks Ecma.Spec.gl cx .syntactic .Expression psExpr h1 h2 tExpr := by
  -- Helper extracting one mandatory symbol from `Relabel.present rhs mask = symItem :: restTarget`:
  have hextractOne : ∀ {k0 : Nat} {is0 : List Item} {a0 b0 : Nat} {m0 : List Bool} {ts0 : List Tree}
      {sym0 : Sym} {restTarget : List Item},
      Relabel.present is0 m0 = .sym sym0 false :: restTarget →
      (∀ u < is0.length, s.alt.rhs[k0 + u]? = is0[u]?) →
      Ecma.Grammar.Seq (tokenAlphabet Ecma.Spec.gl cx P) neg toks Ecma.Spec.gl cx .syntactic s ps k0 is0 a0 b0 m0 ts0 →
      ∃ k1 restIs hMid restM restTs tHead oHead,
        Relabel.present restIs restM = restTarget ∧
        (∀ u < restIs.length, s.alt.rhs[k1 + 1 + u]? = restIs[u]?) ∧
        s.alt.rhs[k1]? = some (.sym sym0 oHead) ∧
        ts0 = tHead :: restTs ∧
        (match sym0 with
          | .t x => tHead = .leaf a0 hMid ∧ (tokenAlphabet Ecma.Spec.gl cx P).term s k1 x (slice toks a0 hMid)
          | .nt mW argsW => Step (tokenAlphabet Ecma.Spec.gl cx P) neg toks Ecma.Spec.gl cx .syntactic mW (applyArgs ps argsW) a0 hMid tHead) ∧
        Ecma.Grammar.Seq (tokenAlphabet Ecma.Spec.gl cx P) neg toks Ecma.Spec.gl cx .syntactic s ps (k1 + 1) restIs hMid b0 restM restTs := by
    intro k0 is0
    induction is0 generalizing k0 with
    | nil => intro _ _ _ _ _ _ h; cases h
    | cons it tl ih =>
      intro a0 b0 m0 ts0 sym0 restTarget hp0 hi0 hs0
      have hitAt : s.alt.rhs[k0]? = some it := by simpa using hi0 0 (by simp)
      have hiTl : ∀ u < tl.length, s.alt.rhs[k0 + 1 + u]? = tl[u]? := by
        intro u hu; have := hi0 (u + 1) (by simp; omega)
        rwa [show k0 + (u + 1) = k0 + 1 + u from by omega, List.getElem?_cons_succ] at this
      cases hs0 with
      | absent hr =>
        simp only [Relabel.present] at hp0
        exact ih hp0 hiTl hr
      | look _ _ | noLT _ _ | empty _ | onlyIf _ | phrase _ _ | butNotT _ _ _ | butNotN _ _ _ =>
        simp only [Relabel.present] at hp0; cases hp0
      | @term _ _ _ x o _ _ hMid _ restM restTs ht hr =>
        cases o with
        | false =>
          simp only [Relabel.present] at hp0
          injection hp0 with hhead htail
          injection hhead with hsym _
          subst hsym
          exact ⟨k0, tl, hMid, restM, restTs, .leaf a0 hMid, false, htail, hiTl, hitAt, rfl, ⟨rfl, ht⟩, hr⟩
        | true =>
          simp only [↓reduceIte, Relabel.present] at hp0
          injection hp0 with hhead htail
          injection hhead with hsym _
          subst hsym
          exact ⟨k0, tl, hMid, restM, restTs, .leaf a0 hMid, true, htail, hiTl, hitAt, rfl, ⟨rfl, ht⟩, hr⟩
      | @nt _ _ _ mW argsW o _ _ hMid _ restM tHead restTs hst _ hr =>
        cases o with
        | false =>
          simp only [Relabel.present] at hp0
          injection hp0 with hhead htail
          injection hhead with hsym _
          subst hsym
          exact ⟨k0, tl, hMid, restM, restTs, tHead, false, htail, hiTl, hitAt, rfl, hst, hr⟩
        | true =>
          simp only [↓reduceIte, Relabel.present] at hp0
          injection hp0 with hhead htail
          injection hhead with hsym _
          subst hsym
          exact ⟨k0, tl, hMid, restM, restTs, tHead, true, htail, hiTl, hitAt, rfl, hst, hr⟩
  have hextractNil : ∀ {k0 : Nat} {is0 : List Item} {a0 b0 : Nat} {m0 : List Bool} {ts0 : List Tree},
      Relabel.present is0 m0 = [] →
      Ecma.Grammar.Seq (tokenAlphabet Ecma.Spec.gl cx P) neg toks Ecma.Spec.gl cx .syntactic s ps k0 is0 a0 b0 m0 ts0 →
      a0 = b0 ∧ ts0 = [] := by
    intro k0 is0
    induction is0 generalizing k0 with
    | nil => intro _ _ _ _ _ hs0; cases hs0; exact ⟨rfl, rfl⟩
    | cons _ tl ih =>
      intro _ _ _ _ hp0 hs0
      cases hs0 with
      | absent hr => simp only [Relabel.present] at hp0; exact ih hp0 hr
      | @term _ _ _ _ o _ _ _ _ _ _ _ _ =>
        cases o <;> (simp only [↓reduceIte, Relabel.present] at hp0; cases hp0)
      | @nt _ _ _ _ _ o _ _ _ _ _ _ _ _ _ _ =>
        cases o <;> (simp only [↓reduceIte, Relabel.present] at hp0; cases hp0)
      | _ => simp only [Relabel.present] at hp0; cases hp0
  dsimp only [sParen] at hpres
  obtain ⟨k1, r1, h1, m1, ts1, t1, o1, hp1, hi1, hit1, rfl, ⟨rfl, htOpen⟩, hseq1⟩ := hextractOne hpres hidx hseq
  obtain ⟨k2, r2, h2, m2, ts2, tExpr, _, hp2, hi2, _, rfl, hstExpr, hseq2⟩ := hextractOne hp1 hi1 hseq1
  obtain ⟨k3, r3, h3, m3, ts3, t3, o3, hp3, _, hit3, rfl, ⟨rfl, htClose⟩, hseq3⟩ := hextractOne hp2 hi2 hseq2
  obtain ⟨rfl, rfl⟩ := hextractNil hp3 hseq3
  obtain ⟨hlt1, hh1Eq, _, _, tokOpen, htx1, hgOpen, htxtOpen, htOpen1⟩ := syn_term_step_one htOpen
  injection htx1 with hs1 hb1; subst hs1; subst hb1
  have hvOpen := term_non_semi_not_virt hsMem (Or.inl ⟨o1, hit1⟩) (by decide) htOpen1
  obtain ⟨hlt3, hh3Eq, _, _, tokClose, htx3, hgClose, htxtClose, htClose1⟩ := syn_term_step_one htClose
  injection htx3 with hs3 hb3; subst hs3; subst hb3
  have hvClose := term_non_semi_not_virt hsMem (Or.inl ⟨o3, hit3⟩) (by decide) htClose1
  have hleExpr := Strict.posSynStep_le
    ((Strict.step_antitone_neg (fun _ _ _ _ f => False.elim f) (treeSize tExpr)).1 (Nat.le_refl _) hstExpr)
  refine ⟨h1, h2, _, tExpr, tokOpen, tokClose, rfl, hlt1, hleExpr, hlt3,
    hgOpen, hvOpen, htxtOpen, fun hjLe => ?_, hstExpr⟩
  have hh1 := hh1Eq (by omega)
  have hh3 := hh3Eq hjLe
  exact ⟨hh1, hh3, by rw [hh3, Nat.add_sub_cancel]; exact hgClose, hvClose, htxtClose⟩

private theorem present_call_extract {cx : Ctx} {P : CodePrims} {toks : List Token}
    {neg : NT → List Param → Nat → Nat → Prop}
    {n : NT} {s : Src} (_hsMem : s ∈ Ecma.Spec.gl.alts cx .syntactic n)
    {ps : List Param} {kIdx : Nat} {rhs : List Item} {i j : Nat} {mask : List Bool} {kidsT : List Tree}
    (hpres : Relabel.present rhs mask = sCall.alt.rhs)
    (hseq : Ecma.Grammar.Seq (tokenAlphabet Ecma.Spec.gl cx P) neg toks Ecma.Spec.gl cx .syntactic
      s ps kIdx rhs i j mask kidsT) :
    ∃ h1 psMem psArgs tMem tArgs,
      kidsT = [tMem, tArgs] ∧
      Step (tokenAlphabet Ecma.Spec.gl cx P) neg toks Ecma.Spec.gl cx .syntactic .MemberExpression psMem i h1 tMem ∧
      Step (tokenAlphabet Ecma.Spec.gl cx P) neg toks Ecma.Spec.gl cx .syntactic .Arguments psArgs h1 j tArgs := by
  have hextractNt : ∀ {k0 : Nat} {is0 : List Item} {a0 b0 : Nat} {m0 : List Bool} {ts0 : List Tree}
      {mTarget : NT} {argsTarget : List Arg} {restTarget : List Item},
      Relabel.present is0 m0 = .sym (.nt mTarget argsTarget) false :: restTarget →
      Ecma.Grammar.Seq (tokenAlphabet Ecma.Spec.gl cx P) neg toks Ecma.Spec.gl cx .syntactic s ps k0 is0 a0 b0 m0 ts0 →
      ∃ k1 restIs hMid restM restTs tHead,
        Relabel.present restIs restM = restTarget ∧
        ts0 = tHead :: restTs ∧
        Step (tokenAlphabet Ecma.Spec.gl cx P) neg toks Ecma.Spec.gl cx .syntactic mTarget (applyArgs ps argsTarget) a0 hMid tHead ∧
        Ecma.Grammar.Seq (tokenAlphabet Ecma.Spec.gl cx P) neg toks Ecma.Spec.gl cx .syntactic s ps (k1 + 1) restIs hMid b0 restM restTs := by
    intro k0 is0
    induction is0 generalizing k0 with
    | nil => intro _ _ _ _ _ _ _ h; cases h
    | cons _ tl ih =>
      intro a0 b0 m0 ts0 mTarget argsTarget restTarget hp0 hs0
      cases hs0 with
      | absent hr => simp only [Relabel.present] at hp0; exact ih hp0 hr
      | look _ _ | noLT _ _ | empty _ | onlyIf _ | phrase _ _ | butNotT _ _ _ | butNotN _ _ _ =>
        simp only [Relabel.present] at hp0; cases hp0
      | @term _ _ _ _ o _ _ _ _ _ _ _ _ =>
        cases o <;> (simp only [↓reduceIte, Relabel.present] at hp0; cases hp0)
      | @nt _ _ _ mW argsW o _ _ hMid _ restM tHead restTs hst _ hr =>
        cases o with
        | false =>
          simp only [Relabel.present] at hp0
          injection hp0 with hhead htail
          injection hhead with hsym _
          injection hsym with hmEq haEq; subst hmEq; subst haEq
          exact ⟨k0, tl, hMid, restM, restTs, tHead, htail, rfl, hst, hr⟩
        | true =>
          simp only [↓reduceIte, Relabel.present] at hp0
          injection hp0 with hhead htail
          injection hhead with hsym _
          injection hsym with hmEq haEq; subst hmEq; subst haEq
          exact ⟨k0, tl, hMid, restM, restTs, tHead, htail, rfl, hst, hr⟩
  have hextractNil : ∀ {k0 : Nat} {is0 : List Item} {a0 b0 : Nat} {m0 : List Bool} {ts0 : List Tree},
      Relabel.present is0 m0 = [] →
      Ecma.Grammar.Seq (tokenAlphabet Ecma.Spec.gl cx P) neg toks Ecma.Spec.gl cx .syntactic s ps k0 is0 a0 b0 m0 ts0 →
      a0 = b0 ∧ ts0 = [] := by
    intro k0 is0
    induction is0 generalizing k0 with
    | nil => intro _ _ _ _ _ hs0; cases hs0; exact ⟨rfl, rfl⟩
    | cons _ tl ih =>
      intro _ _ _ _ hp0 hs0
      cases hs0 with
      | absent hr => simp only [Relabel.present] at hp0; exact ih hp0 hr
      | @term _ _ _ _ o _ _ _ _ _ _ _ _ =>
        cases o <;> (simp only [↓reduceIte, Relabel.present] at hp0; cases hp0)
      | @nt _ _ _ _ _ o _ _ _ _ _ _ _ _ _ _ =>
        cases o <;> (simp only [↓reduceIte, Relabel.present] at hp0; cases hp0)
      | _ => simp only [Relabel.present] at hp0; cases hp0
  dsimp only [sCall] at hpres
  obtain ⟨k1, r1, h1, m1, ts1, tMem, hp1, rfl, hstMem, hseq1⟩ := hextractNt hpres hseq
  obtain ⟨k2, r2, h2, m2, ts2, tArgs, hp2, rfl, hstArgs, hseq2⟩ := hextractNt hp1 hseq1
  obtain ⟨rfl, rfl⟩ := hextractNil hp2 hseq2
  exact ⟨h1, _, _, tMem, tArgs, rfl, hstMem, hstArgs⟩

private theorem prodOf_src_eq (hok : parseTablesOk = true) {cx : Ctx} {n : NT}
    {s : Src} (hsMem : s ∈ Ecma.Spec.gl.alts cx .syntactic n)
    {m : List Bool} {p : Nat} (hpid : Ecma.Spec.gl.prodId s m = some p)
    {P : Prod} {a : Alt} (hpo : prodOf p = some P) (halt : P.altOf = some a)
    (hm : m ∈ masks s.alt.opts) :
    a = s.alt ∧ P.mask = m := by
  obtain ⟨_, id', P1, hid', hpo1, _, hrule1, halt1, hmask1, _⟩ := prodIdOf_spec hok hsMem hm
  have hidEq : id' = p := Option.some.inj (hid'.symm.trans hpid)
  subst hidEq
  rw [hpo] at hpo1; injection hpo1 with hpEq; subst hpEq
  refine ⟨?_, hmask1⟩
  have hsG := hsMem; rw [← glData_eq] at hsG
  obtain ⟨_, hsAlt⟩ := alts_src_origin rfl hsG
  unfold Prod.altOf at halt
  cases hb : P.rule.body with
  | oneOf _ => rw [hb] at halt; cases halt
  | alts as =>
    rw [hb] at halt
    unfold writtenAlts at hsAlt
    rw [← hrule1, hb] at hsAlt
    dsimp only at hsAlt halt
    rw [← halt1, halt] at hsAlt
    exact Option.some.inj hsAlt

private theorem seq_masks_any_neg {cx : Ctx} {P : CodePrims} {toks : List Token}
    {neg : NT → List Param → Nat → Nat → Prop}
    {s : Src} {ps : List Param} {k : Nat} {is : List Item} {a b : Nat} {m : List Bool} {ts : List Tree}
    (hseq : Ecma.Grammar.Seq (tokenAlphabet Ecma.Spec.gl cx P) neg toks Ecma.Spec.gl cx .syntactic s ps k is a b m ts) :
    m ∈ masks ((is.filter fun | .sym _ true => true | _ => false).length) := by
  induction is generalizing k a m ts with
  | nil => cases hseq; simp [masks]
  | cons _ _ ih =>
    cases hseq with
    | absent hr =>
      rw [List.filter_cons_of_pos rfl, List.length_cons, masks]
      exact List.mem_append.mpr (Or.inl (List.mem_map.mpr ⟨_, ih hr, rfl⟩))
    | @term _ _ _ _ o' _ _ _ _ _ _ _ hr | @nt _ _ _ _ _ o' _ _ _ _ _ _ _ _ _ hr =>
      cases o' with
      | false => simpa using ih hr
      | true =>
        simp only [↓reduceIte, List.filter_cons, List.length_cons, masks]
        exact List.mem_append.mpr (Or.inr (List.mem_map.mpr ⟨_, ih hr, rfl⟩))
    | butNotT _ _ hr | butNotN _ _ hr | phrase _ hr | look _ hr | noLT _ hr | empty hr | onlyIf hr =>
      simpa using ih hr

private theorem seqOfNats_inj {xs ys : List Nat}
    (h : Impl.seqOfNats xs = Impl.seqOfNats ys) : xs = ys := by
  rw [seqOfNats_eq, seqOfNats_eq] at h
  have hL : xs.map (fun (c : Nat) => MathVal.int c) = ys.map (fun (c : Nat) => MathVal.int c) :=
    congrArg Array.toList h
  have hgen : ∀ (l1 l2 : List Nat),
      l1.map (fun (c : Nat) => MathVal.int c) = l2.map (fun (c : Nat) => MathVal.int c) → l1 = l2 := by
    intro l1; induction l1 with
    | nil => intro l2 hm; cases l2 <;> simp at hm ⊢
    | cons a1 r1 ih =>
      intro l2 hm
      cases l2 with
      | nil => simp at hm
      | cons a2 r2 =>
        simp only [List.map_cons, List.cons.injEq, MathVal.int.injEq, Int.natCast_inj] at hm
        rw [hm.1, ih r2 hm.2]
  exact hgen xs ys hL

private theorem nodeSource_eq_seqOfNats_of_nodeRel {st0 : Nat} {fullSrc : List Nat}
    {sp : Nat → Nat → Nat × Nat} {nd : Node}
    {nt : NT} {id : Nat} {ps : List Param} {i j : Nat} {kids : List Tree}
    (hrel : Ecma.Model.NodeRel Impl st0 fullSrc sp nd (.node nt id ps i j kids)) :
    Impl.nodeSource nd = Impl.seqOfNats (slice fullSrc (sp i j).1 (sp i j).2) := by
  obtain ⟨_, _, _, _, _, hslen, hsget, _, _, _⟩ := nodeRel_node_inv hrel
  rw [seqOfNats_eq]
  apply Array.ext
  · change (Impl.nodeSource nd).size = _ at *
    simp only [List.size_toArray, List.length_map]
    have : ((Impl.nodeSource nd).size : Int) = ((slice fullSrc (sp i j).1 (sp i j).2).length : Int) :=
      MathVal.int.inj hslen
    exact Int.natCast_inj.mp this
  · intro k hk1 hk2
    have hg := hsget k
    rw [impl_seqGet_nat, List.getElem?_eq_getElem (by
      simp only [List.size_toArray, List.length_map] at hk2; exact hk2)] at hg
    simp only [List.getElem_toArray, List.getElem_map]
    rw [Array.getElem?_eq_getElem hk1] at hg
    exact Option.some.inj hg

-- Main `relabel` soundness core: proves BOTH `CoverIs` and `SynSub` for `r`!
private theorem relabel_core {pc : ParseCx} {st : Nat} {n r : Node}
    {goalIdx : NtId} {args : List (ParamId × Bool)} {ps : List Param}
    (hinv : ParsedInv pc n)
    (hps : ParamsOf args ps)
    (hrelab : Relabel.relabel pc st n goalIdx args = some r) :
    ∃ (goal : NT) (src : List Nat) (tCov : Tree),
      goal.ctorIdx = goalIdx ∧
      Impl.nodeSource n = Impl.seqOfNats src ∧
      ({ gl := Ecma.Spec.gl, cx := Engine.grammarCx pc, P := Engine.Model.codePrims, strict := pc.strict } : GrammarCtx).CoverIs
        Impl st goal ps src r tCov ∧
      SynSub pc r := by
  unfold Relabel.relabel at hrelab
  by_cases hth : (!parseTablesOkThunk.get) = true
  · simp only [hth, ↓reduceIte] at hrelab; cases hrelab
  · have hthF : (!parseTablesOkThunk.get) = false := Bool.eq_false_iff.mpr hth
    have hok := parseTablesOk_of_thunk hthF
    simp only [hthF, Bool.false_eq_true, ↓reduceIte] at hrelab
    rcases n with ⟨stN, loN, hiN, p, ntIdx, psN, kidsN, tN⟩
    dsimp only at hrelab
    obtain ⟨hpairs, hrelab⟩ := guard_bind_some hrelab
    obtain ⟨p', htarget, hrelab⟩ := Option.bind_eq_some_iff.mp hrelab
    obtain ⟨hchk, hrelab⟩ := guard_bind_some hrelab
    obtain ⟨hstrictB, hrelab⟩ := guard_bind_some hrelab
    obtain ⟨_, hret⟩ := guard_bind_some hrelab
    injection hret with hrEq
    have hcovTrue : isCoverNtIdx ntIdx = true := by
      unfold Relabel.pairs at hpairs
      rw [List.contains_iff_mem] at hpairs
      simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hpairs
      unfold isCoverNtIdx
      rcases hpairs with ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> simp
    rcases hinv with hnoCov | hsynSub
    · exfalso
      have := hnoCov _ (Or.inl rfl)
      change isCoverNtIdx ntIdx = false at this
      rw [hcovTrue] at this; cases this
    · obtain ⟨st0, fullSrc, els, toks, subNt, pTree, subPs, i, j, kidsT, firstRoot,
        _, hscans, hfilt, hall, hgoalsSub, hjLe, hderSub, hfheSub, hnrelSub⟩ := hsynSub
      let gx := Engine.grammarCx pc
      let cs := tN.toArray
      have hnrelProps : ntIdx = subNt.ctorIdx ∧ p = pTree ∧
          (loN, hiN) = Ecma.Grammar.tokenSpan els toks i j ∧
          cs.toList = slice fullSrc loN hiN := by
        obtain ⟨hnt, hpId, _, _, hsp, _, _, _, _, _⟩ := nodeRel_node_inv hnrelSub
        have hsrcEq := nodeSource_eq_seqOfNats_of_nodeRel hnrelSub
        have hcsMap : Impl.nodeSource (.mk stN loN hiN p ntIdx psN kidsN tN) =
            Impl.seqOfNats cs.toList := by
          rw [seqOfNats_eq]
          apply Array.ext'
          simp [Impl, cs]
        rw [hcsMap, ← hsp] at hsrcEq
        exact ⟨hnt, hpId, hsp, seqOfNats_inj hsrcEq⟩
      obtain ⟨hntIdxEq, rfl, hloHiEq, hcsSlice⟩ := hnrelProps
      -- Unpack `Relabel.target gx p goalIdx = some p'`:
      unfold Relabel.target at htarget
      rcases opt_none_or_some (prodOf p) with hpoNone | ⟨P_orig, hpoOrig⟩
      · rw [hpoNone] at htarget; cases htarget
      · rw [hpoOrig] at htarget; dsimp only [Bind.bind, Option.bind] at htarget
        rcases opt_none_or_some P_orig.altOf with haltNone | ⟨a_orig, haltOrig⟩
        · rw [haltNone] at htarget; cases htarget
        · rw [haltOrig] at htarget; dsimp only [Bind.bind, Option.bind] at htarget
          rcases opt_none_or_some (ruleNt .syntactic goalIdx) with hrnNone | ⟨goal, hrnGoal⟩
          · rw [hrnNone] at htarget; cases htarget
          · rw [hrnGoal] at htarget; dsimp only [Bind.bind, Option.bind] at htarget
            obtain ⟨hgoalIdxEq, hhasSynGoal⟩ := ruleNt_some_imp hok hrnGoal
            -- Classify `(subNt, goal)` into Pair 1 or Pair 2:
            have hpairCases : (subNt = .CoverParenthesizedExpressionAndArrowParameterList ∧ goal = .ParenthesizedExpression) ∨
                (subNt = .CoverCallExpressionAndAsyncArrowHead ∧ goal = .CallMemberExpression) := by
              unfold Relabel.pairs at hpairs
              rw [List.contains_iff_mem, hntIdxEq, ← hgoalIdxEq] at hpairs
              simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hpairs
              rcases hpairs with ⟨h1, h2⟩ | ⟨h1, h2⟩
              · exact Or.inl ⟨nt_ctorIdx_inj h1, nt_ctorIdx_inj h2⟩
              · exact Or.inr ⟨nt_ctorIdx_inj h1, nt_ctorIdx_inj h2⟩
            have hc1 := Bool.and_eq_true_iff.mp coverGoalsCert_true
            have hci := List.all_eq_true.mp hc1.2 (cxIdx gx) (List.mem_range.mpr (cxIdx_lt gx))
            rw [cxOfIdx_cxIdx] at hci
            -- Extract `[e] = altsOf gx .syntactic goal` and `prodIdOf e [] = some p'`:
            let eGoal : Src := if goal == .ParenthesizedExpression then sParen else sCall
            have haltsGoal : Ecma.Spec.gl.alts gx .syntactic goal = [eGoal] := by
              rw [← glData_eq]
              rcases hpairCases with ⟨_, rfl⟩ | ⟨_, rfl⟩
              · exact of_decide_eq_true (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp hci).1).1).1
              · exact of_decide_eq_true (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp hci).1).1).2
            rw [altsOf_eq hok, haltsGoal] at htarget
            dsimp only at htarget
            obtain ⟨hguardPres, hpidE⟩ := guard_bind_some htarget
            simp only [Bool.and_eq_true] at hguardPres
            have heOpts0 : eGoal.alt.opts = 0 := beq_iff_eq.mp hguardPres.1.2
            have heMem : eGoal ∈ Ecma.Spec.gl.alts gx .syntactic goal := by rw [haltsGoal]; exact List.mem_singleton.mpr rfl
            have hmEmpty : ([] : List Bool) ∈ masks eGoal.alt.opts := by rw [heOpts0]; simp [masks]
            obtain ⟨hpidOfEq, idE, P', hpidESpec, hpo', hgram', hrule', halt', hmask', _⟩ :=
              prodIdOf_spec hok heMem hmEmpty
            have hp'Eq : p' = idE := Option.some.inj ((hpidOfEq.symm.trans hpidE).symm.trans hpidESpec)
            subst idE
            have halt'Some : (writtenAlts P'.rule)[P'.alt]? = some eGoal.alt := by
              rw [hrule', halt']
              rcases hpairCases with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> rfl
            -- Extract `checkNode` facts on `r`:
            have hc1R : (Engine.builder.stamp r != st) = false := by
              rw [← hrEq]; exact bne_self_eq_false st
            have hpo'R : prodOf (Engine.builder.prod r) = some P' := by
              rw [← hrEq]; exact hpo'
            have hc4R : (P'.rule.lhs.ctorIdx != Engine.builder.nt r) = false := by
              rw [← hrEq, hrule', ← hgoalIdxEq]
              rcases hpairCases with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> exact bne_self_eq_false _
            have hc5R : (P'.grammar == .annexB) = false := by
              rw [hgram']
              rcases hpairCases with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> rfl
            have hc6R : (!eGoal.alt.guard.all (Guard.holds (Engine.builder.args r))) = false := by
              rcases hpairCases with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> rfl
            rw [hrEq] at hchk
            obtain ⟨hlenWant, hwantArgs⟩ := checkNode_kids_present_args hc1R hpo'R hc4R hc5R halt'Some hc6R hchk
            rw [hmask'] at hlenWant hwantArgs
            have hpArgsIff := paramsOfArgs_iff_of_paramsOf hps
            have hpArgsContains : ∀ q, (paramsOfArgs args).contains q = ps.contains q := fun q => by
              apply Bool.eq_iff_iff.mpr; simp only [List.contains_iff_mem]; exact hpArgsIff q
            -- Inspect `hderSub` at `max K 1` to get `present s0.alt.rhs m0 = eGoal.alt.rhs`:
            obtain ⟨K, hK⟩ := hderSub
            have hstSub0 := hK (max K 1) (Nat.le_max_left K 1)
            obtain ⟨kInit, hkInit⟩ : ∃ kInit, max K 1 = kInit + 1 := ⟨max K 1 - 1, by omega⟩
            rw [hkInit] at hstSub0
            -- Build `(toksSub, elsSub, tCov)` in each of the two cover pairs:
            have hbuildCov : ∃ (tf tl : Token) (kidsCov : List Tree) (kidsOrigNonLeaf : List Tree),
                i < j ∧
                toks[i]? = some tf ∧ tf.virt = none ∧
                toks[j - 1]? = some tl ∧ tl.virt = none ∧ tl.text = [0x29] ∧
                kidsOrigNonLeaf = kidsT.filter (!·.isLeaf) ∧
                (kidsCov.filter (!·.isLeaf)).length = kidsOrigNonLeaf.length ∧
                (∀ u, i ≤ u → Tree.goalAt.inKids (u - i) kidsCov = Tree.goalAt.inKids u kidsT) ∧
                Sentence Ecma.Spec.gl gx Engine.Model.codePrims goal ps (clearHeadLT (slice toks i j))
                  (.node goal p' ps 0 (j - i) kidsCov) ∧
                ForHeadersExplicit (clearHeadLT (slice toks i j)) (.node goal p' ps 0 (j - i) kidsCov) ∧
                (∀ (elsSub : List Element),
                  let sp1 := Ecma.Grammar.tokenSpan els toks
                  let sp2 := Ecma.Grammar.tokenSpan elsSub (clearHeadLT (slice toks i j))
                  (∀ u v, i ≤ u → u ≤ v → v ≤ j → u < j →
                    sp2 (u - i) (v - i) = ((sp1 u v).1 - loN, (sp1 u v).2 - loN) ∧
                    loN ≤ (sp1 u v).1 ∧ (sp1 u v).1 ≤ (sp1 u v).2 ∧ (sp1 u v).2 ≤ hiN) →
                  (∀ u tk, i ≤ u → u < j → toks[u]? = some tk → tk.virt = none →
                    (sp1 u (u + 1)).1 + tk.text.length ≤ hiN) →
                  ∀ (idx : Nat) c0 tcOrig tcCov,
                    kidsOrigNonLeaf[idx]? = some tcOrig →
                    (kidsCov.filter (!·.isLeaf))[idx]? = some tcCov →
                    Impl.seqGet (Impl.nodeKids (.mk stN loN hiN p ntIdx psN kidsN tN)) (Impl.ofNat idx) = some c0 →
                    Ecma.Model.NodeRel Impl st0 fullSrc sp1 c0 tcOrig →
                    Ecma.Model.NodeRel Impl st cs.toList sp2 (Relabel.shift st loN cs c0) tcCov) := by
              -- Extract child node `c0` from `r`'s `kids` when every entry of `want` has `wp = true`:
              have hrKidsGet : ∀ (idx : Nat) wn wargs, (expectedKids eGoal.alt.rhs [])[idx]? = some (wn, true, wargs) →
                  ∃ c0, Impl.seqGet (Impl.nodeKids (.mk stN loN hiN p ntIdx psN kidsN tN)) (Impl.ofNat idx) = some c0 ∧
                    Impl.nodeArgs c0 = applyArgs (paramsOfArgs args) wargs := by
                intro idx wn wargs hw
                obtain ⟨kn, cSh, hkR, _, hargsSh⟩ := hwantArgs idx wn wargs hw
                have hargsR : Engine.builder.args r = paramsOfArgs args := by rw [← hrEq]; rfl
                rw [hargsR] at hargsSh
                -- Notice `r`'s kids has NO `none` entries because every entry in `expectedKids eGoal.alt.rhs []` has `wp = true`!
                have hallPresent : ∀ idx' < (Engine.builder.kids r).toList.length,
                    ∃ kn' c', (Engine.builder.kids r).toList[idx']? = some (kn', some c') := by
                  intro idx' hlt'
                  have idx'LtW : idx' < (expectedKids eGoal.alt.rhs []).length := hlenWant.symm ▸ hlt'
                  have hwpT : ∃ wn' wargs', (expectedKids eGoal.alt.rhs [])[idx']? = some (wn', true, wargs') := by
                    rcases hpairCases with ⟨_, rfl⟩ | ⟨_, rfl⟩
                    · have heG : eGoal = sParen := rfl
                      rw [heG] at idx'LtW ⊢
                      dsimp only [sParen, expectedKids] at idx'LtW ⊢
                      have h0 : idx' = 0 := by simp at idx'LtW; omega
                      subst h0; exact ⟨_, _, rfl⟩
                    · have heG : eGoal = sCall := rfl
                      rw [heG] at idx'LtW ⊢
                      dsimp only [sCall, expectedKids] at idx'LtW ⊢
                      have h01 : idx' = 0 ∨ idx' = 1 := by simp at idx'LtW; omega
                      rcases h01 with rfl | rfl <;> exact ⟨_, _, rfl⟩
                  obtain ⟨wn', wargs', hw'⟩ := hwpT
                  obtain ⟨kn', c', hk', _, _⟩ := hwantArgs idx' wn' wargs' hw'
                  exact ⟨kn', c', hk'⟩
                have hrKidsEq : (Engine.builder.kids r).toList =
                    kidsN.toList.map (fun (m, c) => (m, c.map (Relabel.shift st loN cs))) := by
                  rw [← hrEq]; exact Array.toList_map
                rw [hrKidsEq, List.getElem?_map] at hkR
                obtain ⟨⟨m0, optC0⟩, hkN0, hpairEq⟩ := Option.map_eq_some_iff.mp hkR
                cases optC0 with
                | none => cases hpairEq
                | some c0 =>
                  simp only [Option.map_some, Prod.mk.injEq, Option.some.injEq] at hpairEq
                  obtain ⟨_, rfl⟩ := hpairEq
                  have hallNPresent : ∀ (u : Nat) (hu : u < kidsN.toList.length), (kidsN.toList[u]'hu).2.isSome = true := by
                    intro u hu
                    have huR : u < (Engine.builder.kids r).toList.length := by rw [hrKidsEq, List.length_map]; exact hu
                    obtain ⟨_, _, hgu⟩ := hallPresent u huR
                    rw [hrKidsEq, List.getElem?_map, List.getElem?_eq_getElem hu] at hgu
                    rcases hku : kidsN.toList[u]'hu with ⟨_, _ | _⟩ <;> simp [hku] at hgu ⊢
                  have hfltIdx : (kidsN.toList.filterMap Prod.snd)[idx]? = some c0 := by
                    have hgen : ∀ (l : List (NtId × Option Node)) (idx0 : Nat) (m1 : NtId),
                        (∀ (u : Nat) (hu : u < l.length), (l[u]'hu).2.isSome = true) →
                        l[idx0]? = some (m1, some c0) →
                        (l.filterMap Prod.snd)[idx0]? = some c0 := by
                      intro l; induction l with
                      | nil => intro _ _ _ h; simp at h
                      | cons hd tl ih =>
                        rcases hd with ⟨m, _ | d⟩
                        · intro _ _ hallP _; exfalso; have := hallP 0 (by simp); simp at this
                        · intro idx0 m1 hallP hk0
                          cases idx0 with
                          | zero =>
                            simp only [List.getElem?_cons_zero, Option.some.injEq, Prod.mk.injEq] at hk0
                            exact congrArg some hk0.2
                          | succ idx1 =>
                            simp only [List.getElem?_cons_succ, List.filterMap_cons] at hk0 ⊢
                            exact ih idx1 m1 (fun u hu => hallP (u + 1) (by simp; omega)) hk0
                    exact hgen kidsN.toList idx m0 hallNPresent hkN0
                  refine ⟨c0, ?_, ?_⟩
                  · rw [impl_seqGet_nat]
                    change (kidsN.filterMap Prod.snd)[idx]? = some c0
                    rwa [← Array.getElem?_toList, Array.toList_filterMap]
                  · rcases c0 with ⟨_, _, _, _, _, psC0, _, _⟩
                    rw [relabel_shift_mk] at hargsSh
                    exact hargsSh
              rcases hpairCases with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
              · -- PAIR 1: `CoverParenthesizedExpressionAndArrowParameterList` -> `ParenthesizedExpression`
                dsimp only [eGoal] at hguardPres heMem hpidESpec hwantArgs hrKidsGet
                have hs0Step : ∃ h1 h2 psE0 tExpr tokOpen tokClose,
                    kidsT = [.leaf i h1, tExpr, .leaf h2 j] ∧
                    i < h1 ∧ h1 ≤ h2 ∧ h2 < j ∧ h1 = i + 1 ∧ j = h2 + 1 ∧
                    toks[i]? = some tokOpen ∧ tokOpen.virt = none ∧ tokOpen.text = [0x28] ∧
                    toks[j - 1]? = some tokClose ∧ tokClose.virt = none ∧ tokClose.text = [0x29] ∧
                    Strict.PosSynStep gx Engine.Model.codePrims toks .Expression psE0 h1 h2 tExpr := by
                  cases hstSub0 with
                  | node s0 hs0Mem _ hpid0 hseq0 =>
                    obtain ⟨_, hopts0⟩ := alt_lhs_and_opts hok hs0Mem
                    have hm0 := hopts0 ▸ seq_masks_any_neg hseq0
                    obtain ⟨haEq0, hmEq0⟩ := prodOf_src_eq hok hs0Mem hpid0 hpoOrig haltOrig hm0
                    have hpres0 : Relabel.present s0.alt.rhs P_orig.mask = sParen.alt.rhs := by
                      rw [← haEq0]
                      have hgp : (sParen.alt.rhs == Relabel.present a_orig.rhs P_orig.mask) = true := by
                        simpa [eGoal] using hguardPres.2
                      exact sym_false_list_beq_eq
                        [.t (.text "(" false), .nt .Expression [⟨.plus, .In⟩, ⟨.quest, .Yield⟩, ⟨.quest, .Await⟩], .t (.text ")" false)]
                        _ hgp
                    obtain ⟨h1, h2, psE0, tExpr, tokOpen, tokClose, hkidsEq, hi1, h12, h2j,
                      hgO, hvO, htO, hcloseFn, hstE⟩ :=
                      present_paren_extract hs0Mem (hmEq0 ▸ hpres0) (fun _ _ => by simp) hseq0
                    obtain ⟨hh1, hh2, hgC, hvC, htC⟩ := hcloseFn hjLe
                    exact ⟨h1, h2, psE0, tExpr, tokOpen, tokClose, hkidsEq, hi1, h12, h2j, hh1, hh2,
                      hgO, hvO, htO, hgC, hvC, htC,
                      (Strict.step_antitone_neg (fun _ _ _ _ f => False.elim f) (treeSize tExpr)).1 (Nat.le_refl _) hstE⟩
                obtain ⟨h1, h2, psE0, tExpr, tokOpen, tokClose, hkidsTEq, hi1, h12, h2j, hh1Eq, hjEq,
                  hgOpen, hvOpen, htxtOpen, hgClose, hvClose, htxtClose, hposExpr⟩ := hs0Step
                let wargsE : List Arg := [⟨.plus, .In⟩, ⟨.quest, .Yield⟩, ⟨.quest, .Await⟩]
                have hrKidsGetP : ∀ (idx : Nat) wn wargs, (expectedKids sParen.alt.rhs [])[idx]? = some (wn, true, wargs) →
                    ∃ c0, Impl.seqGet (Impl.nodeKids (.mk stN loN hiN p ntIdx psN kidsN tN)) (Impl.ofNat idx) = some c0 ∧
                      Impl.nodeArgs c0 = applyArgs (paramsOfArgs args) wargs := by
                  simpa [eGoal] using hrKidsGet
                obtain ⟨cExpr, hgetCExpr, hargsCExpr⟩ := hrKidsGetP 0 NT.Expression.ctorIdx wargsE rfl
                have hleafF : ∀ x y, (!(Tree.leaf x y).isLeaf) = false := fun _ _ => rfl
                have hnlExpr : (!tExpr.isLeaf) = true := by cases hposExpr <;> rfl
                have hfltOrig : kidsT.filter (!·.isLeaf) = [tExpr] := by
                  rw [hkidsTEq]; simp only [List.filter_cons, List.filter_nil, hleafF, hnlExpr, Bool.false_eq_true, ↓reduceIte]
                have hnrelExpr : Ecma.Model.NodeRel Impl st0 fullSrc (Ecma.Grammar.tokenSpan els toks) cExpr tExpr :=
                  (nodeRel_node_inv hnrelSub).2.2.2.2.2.2.2.2.2 0 tExpr cExpr (by rw [hfltOrig]; rfl) hgetCExpr
                have hpExprCongr : match tExpr with | .node _ _ psC _ _ _ => ∀ q, q ∈ psC ↔ q ∈ applyArgs ps wargsE | _ => True := by
                  cases tExpr with
                  | leaf _ _ | lex _ _ => trivial
                  | node ntC idC psC aC bC ksC =>
                    have hargsRel := (nodeRel_node_inv hnrelExpr).2.2.1
                    intro q
                    change Impl.nodeArgs cExpr = _ at hargsCExpr
                    rw [← hargsRel q, hargsCExpr, applyArgs_eq_of_contains hpArgsContains wargsE]
                    exact List.contains_iff_mem
                let tExprCov := setRootPs (applyArgs ps wargsE) (shiftSynTree i tExpr)
                let kidsCov : List Tree := [.leaf 0 1, tExprCov, .leaf (j - 1 - i) (j - i)]
                have hnlExprCov : (!tExprCov.isLeaf) = true := by
                  dsimp only [tExprCov]; rw [(setRootPs_props _ _).1, shiftSynTree_isLeaf]; exact hnlExpr
                have hfltCov : kidsCov.filter (!·.isLeaf) = [tExprCov] := by
                  dsimp only [kidsCov]; simp only [List.filter_cons, List.filter_nil, hleafF, hnlExprCov, Bool.false_eq_true, ↓reduceIte]
                refine ⟨tokOpen, tokClose, kidsCov, kidsT.filter (!·.isLeaf), by omega,
                  hgOpen, hvOpen, hgClose, hvClose, htxtClose, rfl,
                  by rw [hfltCov, hfltOrig]; rfl, ?_, ?_, ?_, ?_⟩
                · intro u hiu
                  rw [hkidsTEq]
                  dsimp only [kidsCov, Tree.goalAt.inKids]
                  have hl1 : (Tree.leaf 0 1).goalAt (u - i) = (Tree.leaf i h1).goalAt u := by
                    unfold Tree.goalAt
                    by_cases hu : u < h1
                    · have hu' : u - i < 1 := by omega
                      simp [hiu, hu, hu']
                    · have hu' : ¬ (u - i < 1) := by omega
                      simp [hiu, hu, hu']
                  have hl2 : (Tree.leaf (j - 1 - i) (j - i)).goalAt (u - i) = (Tree.leaf h2 j).goalAt u := by
                    unfold Tree.goalAt
                    by_cases h1u : h2 ≤ u
                    · by_cases h2u : u < j
                      · have ha' : j - 1 - i ≤ u - i := by omega
                        have hb' : u - i < j - i := by omega
                        simp [h1u, h2u, ha', hb']
                      · have hb' : ¬ (u - i < j - i) := by omega
                        simp [h1u, h2u, hb']
                    · have ha' : ¬ (j - 1 - i ≤ u - i) := by omega
                      simp [h1u, ha']
                  have heGoal : tExprCov.goalAt (u - i) = tExpr.goalAt u := by
                    dsimp only [tExprCov]; rw [(setRootPs_props _ _).2.2.2.1]
                    exact ((step_span_and_goalAt_props (treeSize tExpr)).1 (Nat.le_refl _) hposExpr).2.2.2 i u (by omega) hiu
                  rw [hl1, heGoal, hl2]
                · refine ⟨max K 1, fun k hk => ?_⟩
                  have hsk := hK k (Nat.le_trans (Nat.le_max_left K 1) hk)
                  obtain ⟨km, rfl⟩ : ∃ km, k = km + 1 := ⟨k - 1, by omega⟩
                  cases hsk with
                  | node sK hsKMem _ hpidK hseqK =>
                    obtain ⟨_, hoptsK⟩ := alt_lhs_and_opts hok hsKMem
                    have hmK := hoptsK ▸ seq_masks_any_neg hseqK
                    obtain ⟨haEqK, hmEqK⟩ := prodOf_src_eq hok hsKMem hpidK hpoOrig haltOrig hmK
                    have hpresK : Relabel.present sK.alt.rhs P_orig.mask = sParen.alt.rhs := by
                      rw [← haEqK]
                      have hgp : (sParen.alt.rhs == Relabel.present a_orig.rhs P_orig.mask) = true := by
                        simpa [eGoal] using hguardPres.2
                      exact sym_false_list_beq_eq
                        [.t (.text "(" false), .nt .Expression [⟨.plus, .In⟩, ⟨.quest, .Yield⟩, ⟨.quest, .Await⟩], .t (.text ")" false)]
                        _ hgp
                    obtain ⟨h1K, h2K, psEK, tExprK, _, _, hkidsKEq, _, _, _, _, _, _, hcloseFnK, hstEK⟩ :=
                      present_paren_extract hsKMem (hmEqK ▸ hpresK) (fun _ _ => by simp) hseqK
                    obtain ⟨hh1K, hh2K, _, _, _⟩ := hcloseFnK hjLe
                    have hlistEq := hkidsTEq.symm.trans hkidsKEq
                    injection hlistEq with hl1Eq htl1
                    injection htl1 with htEEq htl2
                    injection htl2 with hl2Eq _
                    injection hl1Eq with _ hh1Eq'
                    injection hl2Eq with hh2Eq' _
                    subst h1K; subst h2K; subst tExprK
                    have hpsEK : match tExpr with | .node _ _ psC _ _ _ => psEK = psC | _ => True := by
                      cases hstEK <;> trivial
                    have hstEKShift := (syn_derivesAt_shift_inner (i := i) hok (by omega) hjLe hgClose hvClose htxtClose km
                      (treeSize tExpr)).1 (Nat.le_refl _) (by omega) (by omega) hstEK
                    have hstEKCov : Step (tokenAlphabet Ecma.Spec.gl gx Engine.Model.codePrims)
                        (fun n ps x y => ∃ t0, DerivesAt Ecma.Spec.gl gx .syntactic (tokenAlphabet Ecma.Spec.gl gx Engine.Model.codePrims) (clearHeadLT (slice toks i j)) km n ps x y t0)
                        (clearHeadLT (slice toks i j)) Ecma.Spec.gl gx .syntactic .Expression (applyArgs ps wargsE) (h1 - i) (h2 - i) tExprCov := by
                      rw [hh1Eq]
                      exact setRootPs_step (by
                        cases tExpr with
                        | leaf _ _ => rw [shiftSynTree_leaf]; trivial
                        | lex _ _ => rw [shiftSynTree_lex]; trivial
                        | node _ _ _ _ _ _ =>
                          rw [shiftSynTree_node]
                          dsimp only at hpsEK hpExprCongr ⊢
                          rwa [hpsEK]) hstEKShift
                    have hsubLen : (clearHeadLT (slice toks i j)).length = j - i := by
                      rw [clearHeadLT_length, slice_length_eq toks (by omega) hjLe]
                    have htOpenCov : (tokenAlphabet Ecma.Spec.gl gx Engine.Model.codePrims).term sParen 0 (.text "(" false)
                        (slice (clearHeadLT (slice toks i j)) 0 1) := by
                      have htOrig : (tokenAlphabet Ecma.Spec.gl gx Engine.Model.codePrims).term sParen 0 (.text "(" false) (slice toks i (i + 1)) := by
                        have hscO : slice toks i (i + 1) = [tokOpen] := by
                          apply List.ext_getElem
                          · rw [slice_length_eq toks (by omega) (by omega)]; simp
                          · intro idx hlen1 hlen2
                            have hg0 := slice_getElem? toks (lo := i) (hi := i + 1) (k := idx) (by
                              rw [slice_length_eq toks (by omega) (by omega)] at hlen1; exact hlen1)
                            have hidx0 : idx = 0 := by simp at hlen2; omega
                            subst hidx0; rw [Nat.add_zero i, hgOpen] at hg0
                            simp only [List.getElem?_eq_getElem hlen1] at hg0
                            exact Option.some.inj hg0
                        dsimp only [tokenAlphabet]; rw [hscO]
                        exact ⟨htxtOpen, by simp [hvOpen]⟩
                      have := (syn_term_shift (Nat.le_of_lt (by omega)) hjLe (Nat.le_refl i) (by omega) htOrig).2.2
                      simpa [Nat.sub_self, show i + 1 - i = 1 from by omega] using this
                    have htCloseCov : (tokenAlphabet Ecma.Spec.gl gx Engine.Model.codePrims).term sParen 2 (.text ")" false)
                        (slice (clearHeadLT (slice toks i j)) (j - 1 - i) (j - i)) := by
                      have htOrig : (tokenAlphabet Ecma.Spec.gl gx Engine.Model.codePrims).term sParen 2 (.text ")" false) (slice toks (j - 1) j) := by
                        have hscC : slice toks (j - 1) j = [tokClose] := by
                          apply List.ext_getElem
                          · rw [slice_length_eq toks (by omega) hjLe]; simp; omega
                          · intro idx hlen1 hlen2
                            have hg0 := slice_getElem? toks (lo := j - 1) (hi := j) (k := idx) (by
                              rw [slice_length_eq toks (by omega) hjLe] at hlen1; exact hlen1)
                            have hidx0 : idx = 0 := by simp at hlen2; omega
                            subst hidx0; rw [Nat.add_zero (j - 1), hgClose] at hg0
                            simp only [List.getElem?_eq_getElem hlen1] at hg0
                            exact Option.some.inj hg0
                        dsimp only [tokenAlphabet]; rw [hscC]
                        exact ⟨htxtClose, by simp [hvClose]⟩
                      exact (syn_term_shift (Nat.le_of_lt (by omega)) hjLe (by omega) (Nat.le_refl j) htOrig).2.2
                    dsimp only [DerivesAt]
                    rw [hsubLen]
                    have heMemP : sParen ∈ Ecma.Spec.gl.alts gx .syntactic .ParenthesizedExpression := by
                      simpa [eGoal] using heMem
                    have hpidEP : Ecma.Spec.gl.prodId sParen [] = some p' := by
                      simpa [eGoal] using hpidESpec
                    refine .node sParen heMemP rfl hpidEP ?_
                    dsimp only [sParen, kidsCov]
                    rw [show h1 - i = 1 from by omega, show h2 - i = j - 1 - i from by omega] at hstEKCov
                    exact .term htOpenCov (.nt hstEKCov trivial (.term htCloseCov .nil))
                · rw [hkidsTEq] at hfheSub
                  have hallOrig := (forHeadersExplicit_all_iff _).mp hfheSub.2
                  have hfheE := forHeadersExplicit_shift (i := i) (j := j) (by omega) hjLe (treeSize tExpr) (Nat.le_refl _)
                    (by omega) (by omega) hposExpr (hallOrig tExpr (by simp))
                  have hfheECov := ((setRootPs_props (applyArgs ps wargsE) (shiftSynTree i tExpr)).2.2.2.2 _).mpr hfheE
                  rw [ForHeadersExplicit]
                  refine ⟨(fun h => by cases h), (forHeadersExplicit_all_iff _).mpr ?_⟩
                  intro d hd
                  simp only [kidsCov, List.mem_cons, List.not_mem_nil, or_false] at hd
                  rcases hd with rfl | rfl | rfl
                  · trivial
                  · exact hfheECov
                  · trivial
                · intro elsSub sp1 sp2 hspSub htokHi idx c0 tcOrig tcCov htcO htcC hget0 hrel0
                  rw [hfltOrig] at htcO; rw [hfltCov] at htcC
                  cases idx with
                  | succ idx0 => simp at htcO
                  | zero =>
                    simp only [List.getElem?_cons_zero, Option.some.injEq] at htcO htcC
                    subst htcO; subst htcC
                    rw [hgetCExpr] at hget0; injection hget0 with hcEq; subst hcEq
                    have htsE := syn_step_treeShiftRel hok (by omega) hjLe hspSub htokHi (treeSize tExpr) (Nat.le_refl _)
                      (by omega) (by omega) hposExpr
                    have hrelSh := nodeRel_relabel_shift_gen st loN hiN
                      (by
                        obtain ⟨_, haLo, hab, hbHi⟩ := hspSub i j (Nat.le_refl i) (by omega) (Nat.le_refl j) (by omega)
                        dsimp only [sp1] at haLo hab hbHi
                        rw [← hloHiEq] at haLo hab hbHi; dsimp at haLo hab hbHi; omega)
                      (by
                        have := (tokenSpan_shift_props hok hscans hfilt hall (by omega) hjLe hgOpen hvOpen hgClose hvClose htxtClose).2.1
                        rwa [← hloHiEq] at this)
                      hcsSlice hrel0 rfl HEq.rfl htsE
                    dsimp only [tExprCov]
                    cases tExpr with
                    | leaf _ _ => rw [shiftSynTree_leaf] at hrelSh ⊢; exact hrelSh
                    | lex _ _ => rw [shiftSynTree_lex] at hrelSh ⊢; exact hrelSh
                    | node _ _ _ _ _ _ => rw [shiftSynTree_node] at hrelSh ⊢; exact nodeRel_congr_root_params hpExprCongr hrelSh
              · -- PAIR 2: `CoverCallExpressionAndAsyncArrowHead` -> `CallMemberExpression`
                dsimp only [eGoal] at hguardPres heMem hpidESpec hwantArgs hrKidsGet
                have hs0Step : ∃ h1 psM0 psA0 tMem tArgs tokFirst tokClose,
                    kidsT = [tMem, tArgs] ∧
                    i < h1 ∧ h1 < j ∧
                    toks[i]? = some tokFirst ∧ tokFirst.virt = none ∧
                    toks[j - 1]? = some tokClose ∧ tokClose.virt = none ∧ tokClose.text = [0x29] ∧
                    Strict.PosSynStep gx Engine.Model.codePrims toks .MemberExpression psM0 i h1 tMem ∧
                    Strict.PosSynStep gx Engine.Model.codePrims toks .Arguments psA0 h1 j tArgs := by
                  cases hstSub0 with
                  | node s0 hs0Mem _ hpid0 hseq0 =>
                    obtain ⟨_, hopts0⟩ := alt_lhs_and_opts hok hs0Mem
                    have hm0 := hopts0 ▸ seq_masks_any_neg hseq0
                    obtain ⟨haEq0, hmEq0⟩ := prodOf_src_eq hok hs0Mem hpid0 hpoOrig haltOrig hm0
                    have hpres0 : Relabel.present s0.alt.rhs P_orig.mask = sCall.alt.rhs := by
                      rw [← haEq0]
                      have hgp : (sCall.alt.rhs == Relabel.present a_orig.rhs P_orig.mask) = true := by
                        simpa [eGoal] using hguardPres.2
                      exact sym_false_list_beq_eq
                        [.nt .MemberExpression [⟨.quest, .Yield⟩, ⟨.quest, .Await⟩], .nt .Arguments [⟨.quest, .Yield⟩, ⟨.quest, .Await⟩]]
                        _ hgp
                    obtain ⟨h1, psM0, psA0, tMem, tArgs, hkidsEq, hstM, hstA⟩ :=
                      present_call_extract hs0Mem (hmEq0 ▸ hpres0) hseq0
                    have hposM := (Strict.step_antitone_neg (fun _ _ _ _ f => False.elim f) (treeSize tMem)).1 (Nat.le_refl _) hstM
                    have hposA := (Strict.step_antitone_neg (fun _ _ _ _ f => False.elim f) (treeSize tArgs)).1 (Nat.le_refl _) hstA
                    have hmIn : realStartNTs.contains .MemberExpression = true :=
                      (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp realStartCert_true).1).1).1
                    obtain ⟨hiLtH1, tokFirst, hgF, hvF⟩ := (posSynStep_real_start (treeSize tMem)).1 (Nat.le_refl _) hmIn hposM
                    obtain ⟨hh1LtJ, ⟨tokClose, hgC, hvC, htC⟩, _⟩ := arguments_pos_props hjLe hposA
                    exact ⟨h1, psM0, psA0, tMem, tArgs, tokFirst, tokClose, hkidsEq, hiLtH1, hh1LtJ,
                      hgF, hvF, hgC, hvC, htC, hposM, hposA⟩
                obtain ⟨h1, psM0, psA0, tMem, tArgs, tokFirst, tokClose, hkidsTEq, hiLtH1, hh1LtJ,
                  hgFirst, hvFirst, hgClose, hvClose, htxtClose, hposMem, hposArgs⟩ := hs0Step
                let wargsMA : List Arg := [⟨.quest, .Yield⟩, ⟨.quest, .Await⟩]
                have hrKidsGetC : ∀ (idx : Nat) wn wargs, (expectedKids sCall.alt.rhs [])[idx]? = some (wn, true, wargs) →
                    ∃ c0, Impl.seqGet (Impl.nodeKids (.mk stN loN hiN p ntIdx psN kidsN tN)) (Impl.ofNat idx) = some c0 ∧
                      Impl.nodeArgs c0 = applyArgs (paramsOfArgs args) wargs := by
                  simpa [eGoal] using hrKidsGet
                obtain ⟨cMem, hgetCMem, hargsCMem⟩ := hrKidsGetC 0 NT.MemberExpression.ctorIdx wargsMA rfl
                obtain ⟨cArgs, hgetCArgs, hargsCArgs⟩ := hrKidsGetC 1 NT.Arguments.ctorIdx wargsMA rfl
                have hnlMem : (!tMem.isLeaf) = true := by cases hposMem <;> rfl
                have hnlArgs : (!tArgs.isLeaf) = true := by cases hposArgs <;> rfl
                have hfltOrig : kidsT.filter (!·.isLeaf) = [tMem, tArgs] := by
                  rw [hkidsTEq]; simp only [List.filter_cons, List.filter_nil, hnlMem, hnlArgs, ↓reduceIte]
                have hkidsRelSub := (nodeRel_node_inv hnrelSub).2.2.2.2.2.2.2.2.2
                have hnrelMem : Ecma.Model.NodeRel Impl st0 fullSrc (Ecma.Grammar.tokenSpan els toks) cMem tMem :=
                  hkidsRelSub 0 tMem cMem (by rw [hfltOrig]; rfl) hgetCMem
                have hnrelArgs : Ecma.Model.NodeRel Impl st0 fullSrc (Ecma.Grammar.tokenSpan els toks) cArgs tArgs :=
                  hkidsRelSub 1 tArgs cArgs (by rw [hfltOrig]; rfl) hgetCArgs
                have hpMemCongr : match tMem with | .node _ _ psC _ _ _ => ∀ q, q ∈ psC ↔ q ∈ applyArgs ps wargsMA | _ => True := by
                  cases tMem with
                  | leaf _ _ | lex _ _ => trivial
                  | node _ _ psC _ _ _ =>
                    have hargsRel := (nodeRel_node_inv hnrelMem).2.2.1
                    intro q; change Impl.nodeArgs cMem = _ at hargsCMem
                    rw [← hargsRel q, hargsCMem, applyArgs_eq_of_contains hpArgsContains wargsMA]
                    exact List.contains_iff_mem
                have hpArgsCongr : match tArgs with | .node _ _ psC _ _ _ => ∀ q, q ∈ psC ↔ q ∈ applyArgs ps wargsMA | _ => True := by
                  cases tArgs with
                  | leaf _ _ | lex _ _ => trivial
                  | node _ _ psC _ _ _ =>
                    have hargsRel := (nodeRel_node_inv hnrelArgs).2.2.1
                    intro q; change Impl.nodeArgs cArgs = _ at hargsCArgs
                    rw [← hargsRel q, hargsCArgs, applyArgs_eq_of_contains hpArgsContains wargsMA]
                    exact List.contains_iff_mem
                let tMemCov := setRootPs (applyArgs ps wargsMA) (shiftSynTree i tMem)
                let tArgsCov := setRootPs (applyArgs ps wargsMA) (shiftSynTree i tArgs)
                let kidsCov : List Tree := [tMemCov, tArgsCov]
                have hnlMemCov : (!tMemCov.isLeaf) = true := by
                  dsimp only [tMemCov]; rw [(setRootPs_props _ _).1, shiftSynTree_isLeaf]; exact hnlMem
                have hnlArgsCov : (!tArgsCov.isLeaf) = true := by
                  dsimp only [tArgsCov]; rw [(setRootPs_props _ _).1, shiftSynTree_isLeaf]; exact hnlArgs
                have hfltCov : kidsCov.filter (!·.isLeaf) = [tMemCov, tArgsCov] := by
                  dsimp only [kidsCov]; simp only [List.filter_cons, List.filter_nil, hnlMemCov, hnlArgsCov, ↓reduceIte]
                refine ⟨tokFirst, tokClose, kidsCov, kidsT.filter (!·.isLeaf), by omega,
                  hgFirst, hvFirst, hgClose, hvClose, htxtClose, rfl,
                  by rw [hfltCov, hfltOrig]; rfl, ?_, ?_, ?_, ?_⟩
                · intro u hiu
                  rw [hkidsTEq]
                  dsimp only [kidsCov, Tree.goalAt.inKids, tMemCov, tArgsCov]
                  rw [(setRootPs_props _ _).2.2.2.1, (setRootPs_props _ _).2.2.2.1,
                      ((step_span_and_goalAt_props (treeSize tMem)).1 (Nat.le_refl _) hposMem).2.2.2 i u (Nat.le_refl i) hiu,
                      ((step_span_and_goalAt_props (treeSize tArgs)).1 (Nat.le_refl _) hposArgs).2.2.2 i u (by omega) hiu]
                · refine ⟨max K 1, fun k hk => ?_⟩
                  have hsk := hK k (Nat.le_trans (Nat.le_max_left K 1) hk)
                  obtain ⟨km, rfl⟩ : ∃ km, k = km + 1 := ⟨k - 1, by omega⟩
                  cases hsk with
                  | node sK hsKMem _ hpidK hseqK =>
                    obtain ⟨_, hoptsK⟩ := alt_lhs_and_opts hok hsKMem
                    have hmK := hoptsK ▸ seq_masks_any_neg hseqK
                    obtain ⟨haEqK, hmEqK⟩ := prodOf_src_eq hok hsKMem hpidK hpoOrig haltOrig hmK
                    have hpresK : Relabel.present sK.alt.rhs P_orig.mask = sCall.alt.rhs := by
                      rw [← haEqK]
                      have hgp : (sCall.alt.rhs == Relabel.present a_orig.rhs P_orig.mask) = true := by
                        simpa [eGoal] using hguardPres.2
                      exact sym_false_list_beq_eq
                        [.nt .MemberExpression [⟨.quest, .Yield⟩, ⟨.quest, .Await⟩], .nt .Arguments [⟨.quest, .Yield⟩, ⟨.quest, .Await⟩]]
                        _ hgp
                    obtain ⟨h1K, psMK, psAK, tMemK, tArgsK, hkidsKEq, hstMK, hstAK⟩ :=
                      present_call_extract hsKMem (hmEqK ▸ hpresK) hseqK
                    have hlistEq := hkidsTEq.symm.trans hkidsKEq
                    injection hlistEq with htMEq htl1
                    injection htl1 with htAEq _
                    subst tMemK; subst tArgsK
                    have hh1KEq : h1K = h1 := by
                      have hsp1 := ((step_span_and_goalAt_props (treeSize tMem)).1 (Nat.le_refl _) hposMem).2.1
                      have hsp2 := ((step_span_and_goalAt_props (treeSize tMem)).1 (Nat.le_refl _) hstMK).2.1
                      exact Prod.mk.inj (hsp2.symm.trans hsp1) |>.2
                    subst h1K
                    have hpsMK : match tMem with | .node _ _ psC _ _ _ => psMK = psC | _ => True := by
                      cases hstMK <;> trivial
                    have hpsAK : match tArgs with | .node _ _ psC _ _ _ => psAK = psC | _ => True := by
                      cases hstAK <;> trivial
                    have hstMKShift := (syn_derivesAt_shift_inner (i := i) hok (by omega) hjLe hgClose hvClose htxtClose km
                      (treeSize tMem)).1 (Nat.le_refl _) (Nat.le_refl i) (by omega) hstMK
                    have hstAKShift := syn_derivesAt_shift_arguments (i := i) hok (by omega) hjLe hstAK
                    have hstMKCov : Step (tokenAlphabet Ecma.Spec.gl gx Engine.Model.codePrims)
                        (fun n ps x y => ∃ t0, DerivesAt Ecma.Spec.gl gx .syntactic (tokenAlphabet Ecma.Spec.gl gx Engine.Model.codePrims) (clearHeadLT (slice toks i j)) km n ps x y t0)
                        (clearHeadLT (slice toks i j)) Ecma.Spec.gl gx .syntactic .MemberExpression (applyArgs ps wargsMA) 0 (h1 - i) tMemCov := by
                      rw [Nat.sub_self] at hstMKShift
                      exact setRootPs_step (by
                        cases tMem with
                        | leaf _ _ => rw [shiftSynTree_leaf]; trivial
                        | lex _ _ => rw [shiftSynTree_lex]; trivial
                        | node _ _ _ _ _ _ =>
                          rw [shiftSynTree_node]
                          dsimp only at hpsMK hpMemCongr ⊢
                          rwa [hpsMK]) hstMKShift
                    have hstAKCov : Step (tokenAlphabet Ecma.Spec.gl gx Engine.Model.codePrims)
                        (fun n ps x y => ∃ t0, DerivesAt Ecma.Spec.gl gx .syntactic (tokenAlphabet Ecma.Spec.gl gx Engine.Model.codePrims) (clearHeadLT (slice toks i j)) km n ps x y t0)
                        (clearHeadLT (slice toks i j)) Ecma.Spec.gl gx .syntactic .Arguments (applyArgs ps wargsMA) (h1 - i) (j - i) tArgsCov := by
                      exact setRootPs_step (by
                        cases tArgs with
                        | leaf _ _ => rw [shiftSynTree_leaf]; trivial
                        | lex _ _ => rw [shiftSynTree_lex]; trivial
                        | node _ _ _ _ _ _ =>
                          rw [shiftSynTree_node]
                          dsimp only at hpsAK hpArgsCongr ⊢
                          rwa [hpsAK]) hstAKShift
                    have hsubLen : (clearHeadLT (slice toks i j)).length = j - i := by
                      rw [clearHeadLT_length, slice_length_eq toks (by omega) hjLe]
                    dsimp only [DerivesAt]
                    rw [hsubLen]
                    have heMemC : sCall ∈ Ecma.Spec.gl.alts gx .syntactic .CallMemberExpression := by
                      simpa [eGoal] using heMem
                    have hpidEC : Ecma.Spec.gl.prodId sCall [] = some p' := by
                      simpa [eGoal] using hpidESpec
                    refine .node sCall heMemC rfl hpidEC ?_
                    dsimp only [sCall, kidsCov]
                    exact .nt hstMKCov trivial (.nt hstAKCov trivial .nil)
                · -- `ForHeadersExplicit`:
                  rw [hkidsTEq] at hfheSub
                  have hallOrig := (forHeadersExplicit_all_iff _).mp hfheSub.2
                  have hfheM := forHeadersExplicit_shift (i := i) (j := j) (by omega) hjLe (treeSize tMem) (Nat.le_refl _)
                    (Nat.le_refl i) (by omega) hposMem (hallOrig tMem (by simp))
                  have hfheA := forHeadersExplicit_shift (i := i) (j := j) (by omega) hjLe (treeSize tArgs) (Nat.le_refl _)
                    (by omega) (Nat.le_refl j) hposArgs (hallOrig tArgs (by simp))
                  rw [ForHeadersExplicit]
                  refine ⟨(fun h => by cases h), (forHeadersExplicit_all_iff _).mpr ?_⟩
                  intro d hd
                  simp only [kidsCov, List.mem_cons, List.not_mem_nil, or_false] at hd
                  rcases hd with rfl | rfl
                  · exact ((setRootPs_props _ _).2.2.2.2 _).mpr hfheM
                  · exact ((setRootPs_props _ _).2.2.2.2 _).mpr hfheA
                · -- `NodeRel` on shifted children `0` (`MemberExpression`) and `1` (`Arguments`):
                  intro elsSub sp1 sp2 hspSub htokHi idx c0 tcOrig tcCov htcO htcC hget0 hrel0
                  have hhiNLe : hiN ≤ fullSrc.length := by
                    have := (tokenSpan_shift_props hok hscans hfilt hall (by omega) hjLe hgFirst hvFirst hgClose hvClose htxtClose).2.1
                    rwa [← hloHiEq] at this
                  have hloLeHi : loN ≤ hiN := by
                    obtain ⟨_, haLo, hab, hbHi⟩ := hspSub i j (Nat.le_refl i) (by omega) (Nat.le_refl j) (by omega)
                    dsimp only [sp1] at haLo hab hbHi
                    rw [← hloHiEq] at haLo hab hbHi; dsimp at haLo hab hbHi; omega
                  rw [hfltOrig] at htcO; rw [hfltCov] at htcC
                  cases idx with
                  | zero =>
                    simp only [List.getElem?_cons_zero, Option.some.injEq] at htcO htcC
                    subst htcO; subst htcC
                    rw [hgetCMem] at hget0; injection hget0 with hcEq; subst hcEq
                    have htsM := syn_step_treeShiftRel hok (by omega) hjLe hspSub htokHi (treeSize tMem) (Nat.le_refl _)
                      (Nat.le_refl i) (by omega) hposMem
                    have hrelSh := nodeRel_relabel_shift_gen st loN hiN hloLeHi hhiNLe hcsSlice hrel0 rfl HEq.rfl htsM
                    dsimp only [tMemCov]
                    cases tMem with
                    | leaf _ _ => rw [shiftSynTree_leaf] at hrelSh ⊢; exact hrelSh
                    | lex _ _ => rw [shiftSynTree_lex] at hrelSh ⊢; exact hrelSh
                    | node _ _ _ _ _ _ => rw [shiftSynTree_node] at hrelSh ⊢; exact nodeRel_congr_root_params hpMemCongr hrelSh
                  | succ idx1 =>
                    cases idx1 with
                    | succ _ => simp at htcO
                    | zero =>
                      simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at htcO htcC
                      subst htcO; subst htcC
                      rw [hgetCArgs] at hget0; injection hget0 with hcEq; subst hcEq
                      have htsA := arguments_treeShiftRel hok hjLe (Nat.le_of_lt hiLtH1) hspSub htokHi hposArgs
                      have hrelSh := nodeRel_relabel_shift_gen st loN hiN hloLeHi hhiNLe hcsSlice hrel0 rfl HEq.rfl htsA
                      dsimp only [tArgsCov]
                      cases tArgs with
                      | leaf _ _ => rw [shiftSynTree_leaf] at hrelSh ⊢; exact hrelSh
                      | lex _ _ => rw [shiftSynTree_lex] at hrelSh ⊢; exact hrelSh
                      | node _ _ _ _ _ _ => rw [shiftSynTree_node] at hrelSh ⊢; exact nodeRel_congr_root_params hpArgsCongr hrelSh
            obtain ⟨tf, tl, kidsCov, _, hij, htf, htfV, htl, htlV, htlTxt, rfl,
              hlenKidsCov, hgoalKidsEq, hsentCov0, hfheCov, hchildRelFn⟩ := hbuildCov
            let toksSub := clearHeadLT (slice toks i j)
            have hsubLen : toksSub.length = j - i := by
              dsimp only [toksSub]; rw [clearHeadLT_length, slice_length_eq toks (Nat.le_of_lt hij) hjLe]
            let tCov := Tree.node goal p' ps 0 toksSub.length kidsCov
            have hsentCov : Sentence Ecma.Spec.gl gx Engine.Model.codePrims goal ps toksSub tCov := by
              dsimp only [tCov]; rwa [hsubLen]
            have hfheCov' : ForHeadersExplicit toksSub tCov := by
              dsimp only [tCov]; rwa [hsubLen]
            -- Apply `tokenSpan_shift_props`:
            obtain ⟨hlhSp, hhiLeSp, _, idxA, idxB, elsShifted, bFirst,
              hidxALeB, hidxBLt, hbFirstPos, hbFirstLe, htfTxtSlice,
              _, hscansSh, hfiltSh, hallSh, hspanSh, htokHiSh, helsShElem⟩ :=
              tokenSpan_shift_props hok hscans hfilt hall hij hjLe htf htfV htl htlV htlTxt
            have hloEqSp : (Ecma.Grammar.tokenSpan els toks i j).1 = loN := congrArg Prod.fst hloHiEq.symm
            have hhiEqSp : (Ecma.Grammar.tokenSpan els toks i j).2 = hiN := congrArg Prod.snd hloHiEq.symm
            rw [hloEqSp] at hlhSp hscansSh hfiltSh hbFirstLe htfTxtSlice hspanSh helsShElem
            rw [hhiEqSp] at hlhSp hhiLeSp hscansSh hfiltSh hbFirstLe htfTxtSlice hspanSh htokHiSh
            let src := slice fullSrc loN hiN
            -- Extract `lg` at index `0` of `tCov` via `posSynStep_expr_first_safe`:
            have hgoalSafe : exprFirstSafeNTs.contains goal = true := by
              rcases hpairCases with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> rfl
            have hposCov := Strict.posSynStep_of_derives hsentCov
            obtain ⟨lg, tok0Sub, _, hgTok0Sub, _, htCovGoal0, hlgOr, hn7dTok0, h2fImpTok0⟩ :=
              (posSynStep_expr_first_safe hok (treeSize tCov)).1 (Nat.le_refl _) hgoalSafe hposCov
            have htok0Txt : tok0Sub.text = slice src 0 bFirst := by
              obtain ⟨htxtC, _⟩ := clearHeadLT_getElem?_text_virt (slice toks i j) 0
              dsimp only [toksSub] at hgTok0Sub
              rw [hgTok0Sub, slice_getElem? toks (by omega), Nat.add_zero, htf] at htxtC
              simp only [Option.map_some, Option.some.injEq] at htxtC
              exact htxtC.trans htfTxtSlice
            have hsrc0Eq : tok0Sub.text[0]? = src[0]? := by
              rw [htok0Txt, slice_getElem? src hbFirstPos, Nat.add_zero]
            -- Build `elsSub` (re-tagging `elsShifted[0]` if `idxA == 0 && firstRoot`):
            have helsSubEx : ∃ elsSub : List Element,
                Scans Ecma.Spec.gl gx Engine.Model.codePrims src elsSub ∧
                GoalsAt goal elsSub toksSub tCov ∧
                toksSub.filter (·.virt.isNone) = tokensOf src elsSub ∧
                (∀ u v, Ecma.Grammar.tokenSpan elsSub toksSub u v = Ecma.Grammar.tokenSpan elsShifted toksSub u v) := by
              by_cases hretag : (idxA == 0 && firstRoot) = true
              · simp only [Bool.and_eq_true, beq_iff_eq] at hretag
                obtain ⟨rfl, rfl⟩ := hretag
                have hneSh : elsShifted ≠ [] := by
                  cases hL : elsShifted with
                  | nil =>
                    exfalso
                    have hlast0 := hscansSh.2.1
                    rw [hL, slice_length_eq fullSrc (Nat.le_of_lt hlhSp) hhiLeSp] at hlast0
                    simp at hlast0; omega
                  | cons _ _ => exact List.cons_ne_nil _ _
                cases hL : elsShifted with
                | nil => exact absurd hL hneSh
                | cons e0Sh restSh =>
                  obtain ⟨e0Orig, hels0Orig, he0ShEq, _⟩ := helsShElem 0 e0Sh (by rw [hL]; rfl)
                  rw [Nat.zero_add] at hels0Orig
                  have he0GoalHB : e0Orig.goal = .InputElementHashbangOrRegExp := by
                    simpa using hgoalsSub 0 e0Orig hels0Orig
                  have he0ShGoal : e0Sh.goal = .InputElementHashbangOrRegExp := by
                    rw [he0ShEq]; exact he0GoalHB
                  have he0ShI : e0Sh.i = 0 := by
                    have hz := List.all_eq_true.mp hscansSh.1 (e0Sh, 0) (by rw [hL]; simp [List.zipIdx_cons])
                    simpa using beq_iff_eq.mp hz
                  obtain ⟨he0ShLt, he0ShDer, he0ShMax, he0ShFol⟩ :=
                    hscansSh.2.2 e0Sh (by rw [hL]; exact List.mem_cons_self ..)
                  have he0ShLe : e0Sh.j ≤ src.length := (scans_elem_ordered hscansSh).1 0 e0Sh (by rw [hL]; rfl) |>.2.1
                  have he0ShTok : e0Sh.isToken = true := by
                    cases htok0B : e0Sh.isToken with
                    | true => rfl
                    | false =>
                      exfalso
                      have hsp0 := (hspanSh i j (Nat.le_refl i) (Nat.le_of_lt hij) (Nat.le_refl j) hij).1
                      rw [hloEqSp, hhiEqSp, Nat.sub_self] at hsp0
                      unfold Ecma.Grammar.tokenSpan at hsp0
                      have hcnt0 : ((clearHeadLT (slice toks i j)).take 0).countP (·.virt.isNone) = 0 := rfl
                      have hcntPos : 0 < ((clearHeadLT (slice toks i j)).take (j - i)).countP (·.virt.isNone) := by
                        have hlenCS : (clearHeadLT (slice toks i j)).length = j - i := hsubLen
                        rw [← hlenCS, List.take_length, List.countP_eq_length_filter]
                        have hsl0 := slice_getElem? toks (lo := i) (hi := j) (k := 0) (by omega)
                        rw [Nat.add_zero, htf] at hsl0
                        cases hsl : slice toks i j with
                        | nil => rw [hsl] at hsl0; cases hsl0
                        | cons x0 xr =>
                          rw [hsl, List.getElem?_cons_zero, Option.some.injEq] at hsl0
                          subst hsl0; simp [clearHeadLT, htfV]
                      have hfltRest : (elsShifted.filter Element.isToken) = restSh.filter Element.isToken := by
                        rw [hL, List.filter_cons_of_neg (by simp [htok0B])]
                      have hneFlt : restSh.filter Element.isToken ≠ [] := by
                        intro hnil
                        have hlen0 : (tokensOf src elsShifted).length = 0 := by
                          rw [(tokensOf_map_es src elsShifted).1, hfltRest, hnil]; rfl
                        have hlenCS : (clearHeadLT (slice toks i j)).length = j - i := hsubLen
                        have hcntPos' : 0 < (clearHeadLT (slice toks i j)).countP (·.virt.isNone) := by
                          rw [← hlenCS, List.take_length] at hcntPos; exact hcntPos
                        rw [← hfiltSh, ← List.countP_eq_length_filter] at hlen0
                        omega
                      cases hrf : restSh.filter Element.isToken with
                      | nil => exact absurd hrf hneFlt
                      | cons e1F _ =>
                        have he1Mem : e1F ∈ restSh := (List.mem_filter.mp (by rw [hrf]; exact List.mem_cons_self ..)).1
                        obtain ⟨mR, hmRLt, rfl⟩ := List.getElem_of_mem he1Mem
                        have hord1 := (scans_elem_ordered hscansSh).2 0 (mR + 1) e0Sh restSh[mR] (by omega)
                          (by rw [hL]; rfl) (by rw [hL, List.getElem?_cons_succ, List.getElem?_eq_getElem hmRLt])
                        have hposI : 0 < restSh[mR].i := by have := hord1.2 (by omega); omega
                        have hstartEq := congrArg Prod.fst hsp0
                        simp [hcntPos, hfltRest, hrf] at hstartEq
                        omega
                  have he0ShDef : e0Sh = ⟨0, e0Sh.j, .InputElementHashbangOrRegExp, e0Sh.tree⟩ := by
                    cases e0Sh; simp_all
                  rw [he0ShDef] at he0ShTok he0ShDer he0ShMax he0ShFol
                  obtain ⟨trLg, hisTokLg, hderLg, hmaxLg, hhasLg⟩ :=
                    retag_hashbang_first_token hok (by rw [← he0ShI]; exact he0ShLt) he0ShLe hlgOr
                      (hsrc0Eq ▸ hn7dTok0) (hsrc0Eq ▸ h2fImpTok0) he0ShTok he0ShDer he0ShMax
                  let e0New : Element := ⟨0, e0Sh.j, lg, trLg⟩
                  have he0NewTok : e0New.isToken = true := hisTokLg
                  let elsSub := e0New :: restSh
                  have hscansNew : Scans Ecma.Spec.gl gx Engine.Model.codePrims src elsSub := by
                    refine ⟨?_, ?_, ?_⟩
                    · rw [List.all_eq_true]
                      intro ⟨eX, kX⟩ hmX
                      have hmIdx : ∀ (l : List Element) (off : Nat) (x : Element) (k : Nat),
                          (x, k) ∈ l.zipIdx off → off ≤ k ∧ k < off + l.length ∧ l[k - off]? = some x := by
                        intro l; induction l with
                        | nil => intro _ _ _ h; nomatch h
                        | cons hd tl ih =>
                          intro off x k hm0
                          rcases List.mem_cons.mp hm0 with heq | htl0
                          · obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq; simp
                          · obtain ⟨h1, h2, h3⟩ := ih (off + 1) x k htl0
                            exact ⟨by omega, by simp; omega, by rw [show k - off = (k - (off + 1)) + 1 from by omega, List.getElem?_cons_succ]; exact h3⟩
                      obtain ⟨_, hkXLt, hgX⟩ := hmIdx elsSub 0 eX kX hmX
                      simp only [Nat.zero_add, Nat.sub_zero] at hkXLt hgX
                      cases kX with
                      | zero =>
                        dsimp only [elsSub] at hgX
                        simp only [List.getElem?_cons_zero, Option.some.injEq] at hgX
                        subst hgX; rfl
                      | succ mX =>
                        dsimp only [elsSub] at hgX hkXLt
                        simp only [List.getElem?_cons_succ] at hgX
                        have hmSh : (eX, mX + 1) ∈ elsShifted.zipIdx := by
                          rw [hL, List.zipIdx_cons]
                          exact List.mem_cons_of_mem _ (by
                            obtain ⟨hmXLt, rfl⟩ := List.getElem?_eq_some_iff.mp hgX
                            have hgen : ∀ (l : List Element) (off idx : Nat) (h : idx < l.length),
                                (l[idx], off + idx) ∈ l.zipIdx off := by
                              intro l; induction l with
                              | nil => intro _ _ h; nomatch h
                              | cons y ys ihy =>
                                intro off idx h
                                cases idx with
                                | zero => simp [List.zipIdx_cons]
                                | succ u =>
                                  rw [List.zipIdx_cons]
                                  exact List.mem_cons_of_mem _ (by
                                    have := ihy (off + 1) u (by simp at h; omega)
                                    rwa [show off + 1 + u = off + (u + 1) from by omega] at this)
                            simpa [Nat.one_add] using hgen restSh 1 mX hmXLt)
                        have hzOld := List.all_eq_true.mp hscansSh.1 (eX, mX + 1) hmSh
                        cases mX with
                        | zero => simpa [elsSub, hL, e0New] using hzOld
                        | succ mX0 => simpa [elsSub, hL] using hzOld
                    · cases restSh with
                      | nil => simpa [elsSub, hL, e0New] using hscansSh.2.1
                      | cons r1 rs =>
                        have hlastEq : (elsSub.getLast?).map (·.j) = (elsShifted.getLast?).map (·.j) := by
                          rw [hL]; rfl
                        simpa [hlastEq] using hscansSh.2.1
                    · intro eX hmX
                      rcases List.mem_cons.mp hmX with rfl | hrestM
                      · exact ⟨by dsimp [e0New]; rw [← he0ShI]; exact he0ShLt, hderLg, hmaxLg,
                          by dsimp [e0New]; rw [hhasLg]; exact he0ShFol⟩
                      · exact hscansSh.2.2 eX (by rw [hL]; exact List.mem_cons_of_mem _ hrestM)
                  have htokOfEq : tokensOf src elsSub = tokensOf src elsShifted := by
                    obtain ⟨hlen1, hget1⟩ := tokensOf_map_es src elsSub
                    obtain ⟨hlen2, hget2⟩ := tokensOf_map_es src elsShifted
                    have hfltLen : (elsSub.filter Element.isToken).length = (elsShifted.filter Element.isToken).length := by
                      rw [hL]; dsimp only [elsSub]
                      rw [List.filter_cons_of_pos hisTokLg, List.filter_cons_of_pos (by rw [he0ShDef]; exact he0ShTok)]
                      simp
                    apply List.ext_getElem (hlen1.trans (hfltLen.trans hlen2.symm))
                    intro r hr1 hr2
                    apply Option.some.inj
                    rw [← List.getElem?_eq_getElem hr1, ← List.getElem?_eq_getElem hr2, hget1 r, hget2 r]
                    cases r with
                    | zero =>
                      have he0Tok : e0Sh.isToken = true := by rw [he0ShDef]; exact he0ShTok
                      rw [hL]; dsimp only [elsSub]
                      simp [List.zipIdx_cons, he0NewTok, he0Tok, e0New, he0ShI]
                    | succ r0 =>
                      have he0Tok : e0Sh.isToken = true := by rw [he0ShDef]; exact he0ShTok
                      rw [hL]; dsimp only [elsSub]
                      simp only [List.zipIdx_cons, List.filter_cons, he0NewTok, he0Tok, ↓reduceIte,
                        List.getElem?_cons_succ]
                      cases hzf : ((restSh.zipIdx 1).filter (fun p => p.1.isToken))[r0]? with
                      | none => rfl
                      | some ek =>
                        rcases ek with ⟨eR, kR⟩
                        have hkRPos : 1 ≤ kR := by
                          have hgen : ∀ (l : List Element) (off : Nat), (eR, kR) ∈ (l.zipIdx off).filter (fun p => p.1.isToken) → off ≤ kR := by
                            intro l; induction l with
                            | nil => intro _ h; nomatch h
                            | cons _ tl ih =>
                              intro off h; rw [List.zipIdx_cons, List.filter_cons] at h
                              split at h
                              · rcases List.mem_cons.mp h with heq | htl
                                · obtain ⟨_, rfl⟩ := Prod.mk.inj heq; exact Nat.le_refl _
                                · have := ih (off + 1) htl; omega
                              · have := ih (off + 1) h; omega
                          exact hgen restSh 1 (List.mem_of_getElem? hzf)
                        obtain ⟨mR, rfl⟩ : ∃ mR, kR = mR + 1 := ⟨kR - 1, by omega⟩
                        simp only [Option.map_some, Option.some.injEq, List.take_succ_cons, List.reverse_cons]
                        have htwStop : ∀ (l : List Element) (x : Element), x.isToken = true →
                            (l ++ [x]).takeWhile (fun (y : Element) => !y.isToken) = l.takeWhile (fun (y : Element) => !y.isToken) := by
                          intro l x hx; induction l with
                          | nil => simp [hx]
                          | cons y ys ih =>
                            simp only [List.cons_append, List.takeWhile_cons]
                            cases (!y.isToken) <;> simp [ih]
                        rw [htwStop _ e0New he0NewTok, htwStop _ e0Sh he0Tok]
                  have hspEqSub : ∀ u v, Ecma.Grammar.tokenSpan elsSub toksSub u v =
                      Ecma.Grammar.tokenSpan elsShifted toksSub u v := by
                    intro u v
                    have hfIJ : (elsSub.filter Element.isToken).map (fun e => (e.i, e.j)) =
                        (elsShifted.filter Element.isToken).map (fun e => (e.i, e.j)) := by
                      rw [hL]; dsimp only [elsSub, e0New]
                      rw [List.filter_cons_of_pos hisTokLg, List.filter_cons_of_pos (by rw [he0ShDef]; exact he0ShTok)]
                      simp [he0ShI]
                    unfold Ecma.Grammar.tokenSpan
                    have hmapI : ∀ (l1 l2 : List Element), l1.map (fun e => (e.i, e.j)) = l2.map (fun e => (e.i, e.j)) →
                        (∀ (idx : Nat), l1[idx]?.map (·.i) = l2[idx]?.map (·.i)) ∧
                        (∀ (idx : Nat), l1[idx]?.map (·.j) = l2[idx]?.map (·.j)) ∧
                        (l1.getLast?.map (·.j) = l2.getLast?.map (·.j)) := by
                      intro l1 l2 hm
                      refine ⟨fun idx => ?_, fun idx => ?_, ?_⟩
                      · have h := congrArg (fun xs => xs[idx]?.map Prod.fst) hm
                        simp only [List.getElem?_map, Option.map_map] at h
                        exact h
                      · have h := congrArg (fun xs => xs[idx]?.map Prod.snd) hm
                        simp only [List.getElem?_map, Option.map_map] at h
                        exact h
                      · have h := congrArg (fun xs => xs.getLast?.map Prod.snd) hm
                        simp only [List.getLast?_map, Option.map_map] at h
                        exact h
                    obtain ⟨hiM, hjM, hlM⟩ := hmapI _ _ hfIJ
                    simp only [hiM, hjM, hlM]
                  have hgoalNotSM : (goal == .Script || goal == .Module) = false := by
                    rcases hpairCases with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> rfl
                  have hgoalsNew : GoalsAt goal elsSub toksSub tCov := by
                    intro k eSub hkSub
                    simp only [hgoalNotSM, Bool.and_false, Bool.false_eq_true, ↓reduceIte]
                    cases k with
                    | zero =>
                      dsimp only [elsSub] at hkSub
                      simp only [List.getElem?_cons_zero, Option.some.injEq] at hkSub
                      subst hkSub
                      rw [show (!e0New.isToken) = false from by rw [he0NewTok]; rfl]
                      dsimp only [↓reduceIte, List.take, List.filter, List.length]
                      have hr0 : realIdx 0 toksSub = 0 := by
                        dsimp only [toksSub]
                        have hsl0 := slice_getElem? toks (lo := i) (hi := j) (k := 0) (by omega)
                        rw [Nat.add_zero, htf] at hsl0
                        cases hsl : slice toks i j with
                        | nil => rw [hsl] at hsl0; cases hsl0
                        | cons x0 xr =>
                          rw [hsl, List.getElem?_cons_zero, Option.some.injEq] at hsl0
                          subst hsl0; simp [clearHeadLT, realIdx, htfV]
                      rw [hr0]; exact htCovGoal0
                    | succ k0 =>
                      have hkSh : elsShifted[k0 + 1]? = some eSub := by
                        rw [hL]; simpa [elsSub] using hkSub
                      obtain ⟨eOrig, helsOrig, rfl, htokFn⟩ := helsShElem (k0 + 1) eSub hkSh
                      rw [Nat.zero_add] at helsOrig htokFn
                      have hgOrig := hgoalsSub (k0 + 1) eOrig helsOrig
                      have hk0Ne0 : ((k0 + 1 == 0) && true) = false := rfl
                      rw [hk0Ne0] at hgOrig
                      dsimp only [↓reduceIte] at hgOrig
                      rw [shiftElem_isToken]
                      by_cases hnotT : (!eOrig.isToken) = true
                      · simp only [hnotT, ↓reduceIte] at hgOrig ⊢; exact hgOrig
                      · simp only [hnotT, Bool.false_eq_true, ↓reduceIte] at hgOrig ⊢
                        have htakeSubLen : ((elsSub.take (k0 + 1)).filter Element.isToken).length =
                            ((elsShifted.take (k0 + 1)).filter Element.isToken).length := by
                          rw [hL]; dsimp only [elsSub]
                          rw [List.take_succ_cons, List.take_succ_cons,
                              List.filter_cons_of_pos he0NewTok, List.filter_cons_of_pos (by rw [he0ShDef]; exact he0ShTok)]
                          simp
                        rw [htakeSubLen]
                        obtain ⟨huOrigEq, hiuO, huOLt, _⟩ := htokFn (by
                          rw [shiftElem_isToken]; cases heT : eOrig.isToken <;> simp [heT] at hnotT ⊢)
                        have hgSub := hgOrig hiuO huOLt
                        dsimp only [Tree.goalAt] at hgSub
                        dsimp only [tCov, Tree.goalAt]
                        rw [← hgoalKidsEq _ hiuO, huOrigEq, Nat.add_sub_cancel_left] at hgSub
                        exact hgSub
                  exact ⟨elsSub, hscansNew, hgoalsNew, hfiltSh.trans htokOfEq.symm, fun u v => hL ▸ hspEqSub u v⟩
              · have hgoalNotSM : (goal == .Script || goal == .Module) = false := by
                  rcases hpairCases with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> rfl
                have hgoalsNew : GoalsAt goal elsShifted toksSub tCov := by
                  intro k eSub hkSh
                  simp only [hgoalNotSM, Bool.and_false, Bool.false_eq_true, ↓reduceIte]
                  obtain ⟨eOrig, helsOrig, rfl, htokFn⟩ := helsShElem k eSub hkSh
                  have hgOrig := hgoalsSub (idxA + k) eOrig helsOrig
                  have hnotHB : ((idxA + k == 0) && firstRoot) = false := by
                    apply Bool.eq_false_iff.mpr; intro hT
                    simp only [Bool.and_eq_true, beq_iff_eq, Nat.add_eq_zero_iff] at hT
                    exact hretag (Bool.and_eq_true_iff.mpr ⟨beq_iff_eq.mpr hT.1.1, hT.2⟩)
                  rw [hnotHB] at hgOrig
                  dsimp only [↓reduceIte] at hgOrig
                  rw [shiftElem_isToken]
                  by_cases hnotT : (!eOrig.isToken) = true
                  · simp only [hnotT, ↓reduceIte] at hgOrig ⊢; exact hgOrig
                  · simp only [hnotT, Bool.false_eq_true, ↓reduceIte] at hgOrig ⊢
                    obtain ⟨huOrigEq, hiuO, huOLt, _⟩ := htokFn (by
                      rw [shiftElem_isToken]; cases heT : eOrig.isToken <;> simp [heT] at hnotT ⊢)
                    have hgSub := hgOrig hiuO huOLt
                    dsimp only [Tree.goalAt] at hgSub
                    dsimp only [tCov, Tree.goalAt]
                    rw [← hgoalKidsEq _ hiuO, huOrigEq, Nat.add_sub_cancel_left] at hgSub
                    exact hgSub
                exact ⟨elsShifted, hscansSh, hgoalsNew, hfiltSh, fun _ _ => rfl⟩
            obtain ⟨elsSub, hscansSub, hgoalsSubCov, hfiltSub, hspEqSub⟩ := helsSubEx
            -- Build `NodeRel Impl st src (tokenSpan elsSub toksSub) r tCov`:
            have hspanSubAll : ∀ u v, i ≤ u → u ≤ v → v ≤ j → u < j →
                Ecma.Grammar.tokenSpan elsSub toksSub (u - i) (v - i) =
                  ((Ecma.Grammar.tokenSpan els toks u v).1 - loN, (Ecma.Grammar.tokenSpan els toks u v).2 - loN) ∧
                loN ≤ (Ecma.Grammar.tokenSpan els toks u v).1 ∧
                (Ecma.Grammar.tokenSpan els toks u v).1 ≤ (Ecma.Grammar.tokenSpan els toks u v).2 ∧
                (Ecma.Grammar.tokenSpan els toks u v).2 ≤ hiN := by
              intro u v hiu huv hvj huj
              rw [hspEqSub]
              exact hspanSh u v hiu huv hvj huj
            have hspRootCov : Ecma.Grammar.tokenSpan elsSub toksSub 0 toksSub.length = (0, hiN - loN) := by
              rw [hsubLen]
              have h0 := (hspanSubAll i j (Nat.le_refl i) (Nat.le_of_lt hij) (Nat.le_refl j) hij).1
              rwa [Nat.sub_self, hloEqSp, hhiEqSp, Nat.sub_self] at h0
            have hcsLen : cs.size = hiN - loN := by
              rw [← Array.length_toList, hcsSlice, slice_length_eq fullSrc (Nat.le_of_lt hlhSp) hhiLeSp]
            have hsrcSliceSelf : slice src 0 (hiN - loN) = src := by
              have hlenS : src.length = hiN - loN := slice_length_eq fullSrc (Nat.le_of_lt hlhSp) hhiLeSp
              unfold slice; rw [List.drop_zero, ← hlenS, Nat.sub_zero, List.take_length]
            have hrKidsMap : Impl.nodeKids r =
                (Impl.nodeKids (.mk stN loN hiN p ntIdx psN kidsN tN)).map (Relabel.shift st loN cs) := by
              rw [← hrEq]
              apply Array.ext'
              simp only [Impl, Array.toList_filterMap, Array.toList_map]
              have hgen : ∀ l : List (NtId × Option Node),
                  (l.map fun (m, c) => (m, c.map (Relabel.shift st loN cs))).filterMap Prod.snd =
                  (l.filterMap Prod.snd).map (Relabel.shift st loN cs) := by
                intro l; induction l with
                | nil => rfl
                | cons hd tl ih => rcases hd with ⟨_, _ | _⟩ <;> simp [ih]
              exact hgen kidsN.toList
            have hnrelCov : Ecma.Model.NodeRel Impl st src (Ecma.Grammar.tokenSpan elsSub toksSub) r tCov := by
              obtain ⟨_, _, _, _, _, _, _, hklenOrig, hkgetOrig, hkidsRelOrig⟩ := nodeRel_node_inv hnrelSub
              refine .node
                (by rw [← hrEq]; exact hgoalIdxEq.symm)
                (by rw [← hrEq])
                (by rw [← hrEq]; exact hpArgsIff)
                (by rw [← hrEq])
                (by rw [← hrEq, hspRootCov])
                ?_ ?_ ?_ ?_ ?_
              · rw [hspRootCov, hsrcSliceSelf, ← hrEq]
                change MathVal.int ((Engine.Parse.view cs 0 cs.size).toArray.map _).size = _
                rw [Array.size_map, view_toArray_eq_extract, Array.size_extract,
                    Nat.min_self, Nat.sub_zero, hcsLen,
                    slice_length_eq fullSrc (Nat.le_of_lt hlhSp) hhiLeSp]
              · intro k
                rw [hspRootCov, hsrcSliceSelf, ← hrEq, impl_seqGet_nat]
                change ((Engine.Parse.view cs 0 cs.size).toArray.map (fun (c : Nat) => MathVal.int c))[k]? = _
                rw [Array.getElem?_map, view_toArray_eq_extract, ← Array.getElem?_toList,
                    extract_toList_eq_slice, hcsLen, hcsSlice, hsrcSliceSelf]
              · show MathVal.int (Impl.nodeKids r).size = _
                rw [hrKidsMap, Array.size_map, hlenKidsCov]; exact hklenOrig
              · intro k
                rw [impl_seqGet_nat, hrKidsMap, Array.getElem?_map, hlenKidsCov]
                have hk0 := hkgetOrig k
                rw [impl_seqGet_nat] at hk0
                simp only [Option.isSome_map]
                rw [hk0, decide_eq_true_eq]
              · intro idx tcCov cR htcCov hcR
                rw [impl_seqGet_nat, hrKidsMap, Array.getElem?_map] at hcR
                obtain ⟨c0, hc0, rfl⟩ := Option.map_eq_some_iff.mp hcR
                have idxLtCov : idx < (kidsCov.filter (!·.isLeaf)).length := (List.getElem?_eq_some_iff.mp htcCov).1
                have idxLtOrig : idx < (kidsT.filter (!·.isLeaf)).length := hlenKidsCov ▸ idxLtCov
                have hc0Seq : Impl.seqGet (Impl.nodeKids (.mk stN loN hiN p ntIdx psN kidsN tN)) (Impl.ofNat idx) = some c0 := by
                  rwa [impl_seqGet_nat]
                have hrel0 := hkidsRelOrig idx _ c0 (List.getElem?_eq_getElem idxLtOrig) hc0Seq
                dsimp only [src]
                rw [← hcsSlice]
                exact hchildRelFn elsSub hspanSubAll htokHiSh idx c0 _ tcCov
                  (List.getElem?_eq_getElem idxLtOrig) htcCov hc0Seq hrel0
            -- Obtain `NonStrictOk`:
            let Gpc : GrammarCtx := { gl := Ecma.Spec.gl, cx := gx, P := Engine.Model.codePrims, strict := pc.strict }
            have hnsCov : NonStrictOk Ecma.Spec.gl (Gpc.StrictIn src elsSub toksSub) [] tCov := by
              rcases Bool.or_eq_true_iff.mp hstrictB with hnoB | hslTrue
              · exact Strict.nonStrictOk_of_not_annexB hok hnoB _ tCov [] (Nat.le_refl _) hposCov
              · rw [beq_iff_eq, hrEq] at hslTrue
                exact Strict.sloppyOk_true_sound hok hscansSub hfiltSub (Nat.le_refl _) hposCov hnrelCov hslTrue
            -- Assemble `CoverIs` and `SynSub pc r`:
            have hsrcNodeN : Impl.nodeSource (.mk stN loN hiN p ntIdx psN kidsN tN) = Impl.seqOfNats src := by
              rw [nodeSource_eq_seqOfNats_of_nodeRel hnrelSub, hloEqSp, hhiEqSp]
            refine ⟨goal, src, tCov, hgoalIdxEq, hsrcNodeN, ?_, ?_⟩
            · unfold GrammarCtx.CoverIs
              simp only [hhasSynGoal, ↓reduceIte]
              exact ⟨elsSub, toksSub, hscansSub, hgoalsSubCov, hfiltSub, hallSh, hsentCov, hfheCov', hnsCov, hnrelCov⟩
            · refine ⟨st, src, elsSub, toksSub, goal, p', ps, 0, toksSub.length, kidsCov, false,
                hok, hscansSub, hfiltSub, hallSh, ?_, Nat.le_refl _, hsentCov, hfheCov', hnrelCov⟩
              intro k eSub hkSub
              simp only [Bool.and_false, Bool.false_eq_true, ↓reduceIte]
              have hgC := hgoalsSubCov k eSub hkSub
              have hgoalNotSM : (goal == .Script || goal == .Module) = false := by
                rcases hpairCases with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> rfl
              simp only [hgoalNotSM, Bool.and_false, Bool.false_eq_true, ↓reduceIte] at hgC
              by_cases hnotT : (!eSub.isToken) = true
              · simp only [hnotT, ↓reduceIte] at hgC ⊢; exact hgC
              · simp only [hnotT, Bool.false_eq_true, ↓reduceIte] at hgC ⊢
                intro _ _; exact hgC

/-! ## Section 8: `ParsedInv` on `Model.Parsed` and `Engine.Impl.coverLaws` -/

private theorem parsedInv_kid {pc : ParseCx} {nd c : Node}
    (h : ParsedInv pc nd) (hc : c ∈ (kidsOf nd).toList) :
    ParsedInv pc c := by
  rcases h with hnoCov | hsyn
  · exact Or.inl (noCoverSub_of_kid hnoCov hc)
  · obtain ⟨st0, fullSrc, els, toks, subNt, p, subPs, i, j, kidsT, firstRoot,
      hok, hscans, hfilt, hall, hgoalsSub, hjLe, hderSub, hfheSub, hnrelSub⟩ := hsyn
    rw [← nodeKids_eq] at hc
    obtain ⟨idx, hidxLt, rfl⟩ := List.getElem_of_mem hc
    have hgetC : Impl.seqGet (Impl.nodeKids nd) (Impl.ofNat idx) = some (Impl.nodeKids nd)[idx] := by
      rw [impl_seqGet_nat, ← Array.getElem?_toList, List.getElem?_eq_getElem hidxLt]; rfl
    obtain ⟨_, _, _, _, _, _, _, _, hkget, hkidsRel⟩ := nodeRel_node_inv hnrelSub
    have hsomeC : (Impl.seqGet (Impl.nodeKids nd) (Impl.ofNat idx)).isSome = true := by rw [hgetC]; rfl
    have hidxT : idx < (kidsT.filter (!·.isLeaf)).length := by
      have hk0 := (hkget idx).symm
      rw [hsomeC, decide_eq_true_iff] at hk0
      exact hk0
    let tc := (kidsT.filter (!·.isLeaf))[idx]'hidxT
    have htcGet : (kidsT.filter (!·.isLeaf))[idx]? = some tc := List.getElem?_eq_getElem hidxT
    have hrelC := hkidsRel idx tc _ htcGet hgetC
    obtain ⟨K, hK⟩ := hderSub
    have hst0 := hK (max K 1) (Nat.le_max_left K 1)
    obtain ⟨k0, hk0⟩ : ∃ k0, max K 1 = k0 + 1 := ⟨max K 1 - 1, by omega⟩
    rw [hk0] at hst0
    cases htcCase : tc with
    | leaf aC bC =>
      exfalso
      have hmemF : Tree.leaf aC bC ∈ kidsT.filter (!·.isLeaf) := htcCase ▸ List.getElem_mem hidxT
      simp [Tree.isLeaf] at hmemF
    | lex kLex subLex =>
      rw [htcCase] at htcGet hrelC
      cases hst0 with
      | node _ _ _ _ hseq0 =>
        obtain ⟨_, hlx⟩ := seq_child_extract hseq0 idx _ htcGet
        obtain ⟨mL, tokL, _, hderLex⟩ := hlx kLex subLex rfl
        have hrelSub := nodeRel_lex_inv hrelC
        exact Or.inl (noCoverSub_of_code_derives lexical_mem_codeGrammars hderLex hrelSub)
    | node mC idC psC aC bC ksC =>
      rw [htcCase] at htcGet hrelC
      cases hst0 with
      | node _ _ _ _ hseq0 =>
        obtain ⟨hnd0, _⟩ := seq_child_extract hseq0 idx _ htcGet
        obtain ⟨hiaC, habC, hbCj, _, hgoalInC⟩ := hnd0 mC idC psC aC bC ksC rfl
        have hderC : Derives Ecma.Spec.gl (Engine.grammarCx pc) .syntactic
            (tokenAlphabet Ecma.Spec.gl (Engine.grammarCx pc) Engine.Model.codePrims)
            toks mC psC aC bC (.node mC idC psC aC bC ksC) := by
          refine ⟨max K 1, fun k hk => ?_⟩
          have hsk := hK k (Nat.le_trans (Nat.le_max_left K 1) hk)
          obtain ⟨km, rfl⟩ : ∃ km, k = km + 1 := ⟨k - 1, by omega⟩
          cases hsk with
          | node _ _ _ _ hseqK =>
            exact ((seq_child_extract hseqK idx _ htcGet).1 mC idC psC aC bC ksC rfl).2.2.2.1
        have hfheC : ForHeadersExplicit toks (.node mC idC psC aC bC ksC) := by
          have hmemK : Tree.node mC idC psC aC bC ksC ∈ kidsT :=
            (List.mem_filter.mp (List.mem_of_getElem? htcGet)).1
          exact (forHeadersExplicit_all_iff _).mp hfheSub.2 _ hmemK
        refine Or.inr ⟨st0, fullSrc, els, toks, mC, idC, psC, aC, bC, ksC, firstRoot,
          hok, hscans, hfilt, hall, ?_, by omega, hderC, hfheC, hrelC⟩
        intro k e hk
        have hg0 := hgoalsSub k e hk
        by_cases hc1 : (k == 0 && firstRoot) = true
        · simp only [hc1, ↓reduceIte] at hg0 ⊢; exact hg0
        · simp only [hc1, Bool.false_eq_true, ↓reduceIte] at hg0 ⊢
          by_cases hc2 : (!e.isToken) = true
          · simp only [hc2, ↓reduceIte] at hg0 ⊢; exact hg0
          · simp only [hc2, Bool.false_eq_true, ↓reduceIte] at hg0 ⊢
            intro hu1 hu2
            have hgParent := hg0 (by omega) (by omega)
            dsimp only [Tree.goalAt] at hgParent
            rw [hgoalInC _ hu1 hu2] at hgParent
            exact hgParent

private theorem parsedInv_desc {pc : ParseCx} {nd d : Node}
    (h : ParsedInv pc nd) (hd : d ∈ seqList (Impl.nodeDescendants nd)) :
    ParsedInv pc d := by
  have hgen : ∀ (f : Nat) (m : Node), m.height ≤ f → ParsedInv pc m →
      ∀ d ∈ seqList (Impl.nodeDescendants m), ParsedInv pc d := by
    intro f
    induction f with
    | zero => intro m hf; obtain ⟨g, hg⟩ := height_pos m; omega
    | succ f ih =>
      intro m hf hm d hdMem
      obtain ⟨c, hc, hdc⟩ := (mem_descendants m d).mp hdMem
      have hcInv := parsedInv_kid hm hc
      rcases hdc with rfl | hdC
      · exact hcInv
      · exact ih c (by have := height_kid hc; omega) hcInv d hdC
  exact hgen nd.height nd (Nat.le_refl _) h d hd

private theorem parsedInv_of_parse {pc : ParseCx} {st : Nat} {srcSeq : Array MathVal}
    {goalIdx : NtId} {args : List (ParamId × Bool)} {n : Node}
    (hp : Engine.parse pc st srcSeq goalIdx args = some (some n)) :
    ParsedInv pc n := by
  unfold Engine.parse at hp
  by_cases hth : (!parseTablesOkThunk.get) = true
  · simp only [hth, ↓reduceIte] at hp; cases hp
  · have hthF : (!parseTablesOkThunk.get) = false := Bool.eq_false_iff.mpr hth
    have hok := parseTablesOk_of_thunk hthF
    simp only [hthF, Bool.false_eq_true, ↓reduceIte] at hp
    have hfallback : (match Engine.outcome 0 srcSeq goalIdx args (Engine.grammarCx pc) pc.strict with
        | .ok m => some (some (Engine.restamp st m))
        | .noParse => some none
        | .stop _ => none) = some (some n) → ParsedInv pc n := by
      intro hf
      cases ho : Engine.outcome 0 srcSeq goalIdx args (Engine.grammarCx pc) pc.strict with
      | noParse | stop _ => rw [ho] at hf; cases hf
      | ok m =>
        rw [ho] at hf; injection hf with hopt; injection hopt with hmEq; subst hmEq
        unfold Engine.outcome at ho
        rcases opt_none_or_some (Engine.codePointsOf srcSeq) with hcNone | ⟨cs, hcSome⟩
        · rw [hcNone] at ho; cases ho
        · rw [hcSome] at ho
          have hcp := codePointsOf_some_bound hcSome
          by_cases hfast : (Engine.noFirst goalIdx cs || Engine.noJSON goalIdx cs) = true
          · simp [hfast] at ho
          · simp only [hfast, Bool.false_eq_true, ↓reduceIte] at ho
            cases hpOut : Engine.Parse.parse Engine.builder (Engine.grammarCx pc) pc.strict 0 cs goalIdx args with
            | noParse | stop _ => rw [hpOut] at ho; cases ho
            | ok m0 =>
              rw [hpOut] at ho; dsimp only [Engine.checked] at ho
              by_cases hsh : Engine.shaped m0 = true
              · simp only [hsh, ↓reduceIte] at ho
                injection ho with hm0Eq; subst m0
                unfold Engine.Parse.parse at hpOut
                rcases opt_none_or_some (ruleNt .syntactic goalIdx) with hsynNone | ⟨lhs, hsynSome⟩
                · rw [hsynNone] at hpOut; dsimp only at hpOut
                  obtain ⟨⟨g, lhsC⟩, hmemGs, houtOk⟩ := fold_outcome_ok _ _ hpOut
                  dsimp only at houtOk
                  have hcRun : Code.run Engine.builder cs g (Engine.grammarCx pc) 0 lhsC (paramsOfArgs args) = .ok (some m) := by
                    rcases except_eq_err_or_ok (Code.run Engine.builder cs g (Engine.grammarCx pc) 0 lhsC (paramsOfArgs args)) with ⟨err, herr⟩ | ⟨optN, hokR⟩
                    · rw [herr] at houtOk; cases houtOk
                    · cases optN with
                      | none => rw [hokR] at houtOk; cases houtOk
                      | some n0 => rw [hokR] at houtOk; injection houtOk with heq; subst n0; exact hokR
                  rw [List.mem_filterMap] at hmemGs
                  obtain ⟨g0, hgMem, hmapEq⟩ := hmemGs
                  rcases opt_none_or_some (ruleNt g0 goalIdx) with hn0 | ⟨m1, hm1⟩
                  · rw [hn0] at hmapEq; cases hmapEq
                  · rw [hm1] at hmapEq; injection hmapEq with hpEq; injection hpEq with hgEq _; subst g0
                    obtain ⟨t0, hpc0, hrel0⟩ := code_run_some_spec hok hgMem hcRun
                    have hrelSt := nodeRel_restamp st hrel0
                    unfold ParsesCode at hpc0
                    by_cases hord : Ecma.Spec.gl.ordered (Engine.grammarCx pc) g = true
                    · simp only [hord, ↓reduceIte] at hpc0
                      exact Or.inl (noCoverSub_of_code_derives hgMem hpc0.1 hrelSt)
                    · simp only [hord, Bool.false_eq_true, ↓reduceIte] at hpc0
                      exact Or.inl (noCoverSub_of_code_derives hgMem hpc0 hrelSt)
                · rw [hsynSome] at hpOut; dsimp only at hpOut
                  obtain ⟨_, hhasSyn⟩ := ruleNt_some_imp hok hsynSome
                  rcases except_eq_err_or_ok (Syntax.run Engine.builder cs (Engine.grammarCx pc) 0 lhs (paramsOfArgs args)) with ⟨err, herr⟩ | ⟨optN, hsRun⟩
                  · rw [herr] at hpOut; cases hpOut
                  · cases optN with
                    | none => rw [hsRun] at hpOut; cases hpOut
                    | some n0 =>
                      rw [hsRun] at hpOut; dsimp only at hpOut
                      have hn0Eq : n0 = m := by
                        by_cases hnoB : (!(Engine.grammarCx pc).annexB.any) = true
                        · simp only [hnoB, ↓reduceIte] at hpOut; injection hpOut
                        · simp only [hnoB, Bool.false_eq_true, ↓reduceIte] at hpOut
                          cases hsl : Strict.sloppyOk Engine.builder (Syntax.depth cs.size + 1) pc.strict (Syntax.depth cs.size + 1) [] n0 with
                          | none => rw [hsl] at hpOut; cases hpOut
                          | some b =>
                            cases b with
                            | false => rw [hsl] at hpOut; cases hpOut
                            | true => rw [hsl] at hpOut; injection hpOut
                      subst n0
                      obtain ⟨els, toks, t, hsc, hgl, hfi, hal, _, hsn, hfh, hnrel0, _, _, _⟩ :=
                        syntax_run_some_spec hok hcp hhasSyn hsRun
                      have hnrelSt := nodeRel_restamp st hnrel0
                      obtain ⟨id0, kids0, rfl, _⟩ := sentence_congr_params (fun _ => Iff.rfl) hhasSyn hok hsn
                      refine Or.inr ⟨st, cs.toList, els, toks, lhs, id0, paramsOfArgs args, 0, toks.length, kids0,
                        (lhs == .Script || lhs == .Module), hok, hsc, hfi, hal, ?_, Nat.le_refl _, hsn, hfh, hnrelSt⟩
                      intro k e hk
                      have hg := hgl k e hk
                      by_cases hc1 : (k == 0 && (lhs == .Script || lhs == .Module)) = true
                      · simp only [hc1, ↓reduceIte] at hg ⊢; exact hg
                      · simp only [hc1, Bool.false_eq_true, ↓reduceIte] at hg ⊢
                        by_cases hc2 : (!e.isToken) = true
                        · simp only [hc2, ↓reduceIte] at hg ⊢; exact hg
                        · simp only [hc2, Bool.false_eq_true, ↓reduceIte] at hg ⊢
                          intro _ _; exact hg
              · simp [hsh] at ho
    by_cases hnum : (goalIdx == NT.StringNumericLiteral.ctorIdx || goalIdx == NT.StringIntegerLiteral.ctorIdx) = true
    · simp only [hnum, ↓reduceIte] at hp
      rcases opt_none_or_some (Engine.codePointsOf srcSeq) with hcNone | ⟨cs, hcSome⟩
      · rw [hcNone] at hp; exact hfallback hp
      · rw [hcSome] at hp
        rcases opt_none_or_some (Engine.parseNumeric st srcSeq goalIdx args) with hpNone | ⟨optM, hpSome⟩
        · rw [hpNone] at hp; exact hfallback hp
        · rw [hpSome] at hp
          cases optM with
          | none => exact hfallback hp
          | some m =>
            dsimp only at hp
            by_cases hchk : (Engine.shaped m && (Engine.builder.nt m == goalIdx &&
                Engine.builder.args m == paramsOfArgs args && Engine.builder.span m == (0, cs.size) &&
                (Engine.verifyCodeNode cs (Engine.grammarCx pc) .numericString st (m.height + 1) m).isSome)) = true
            · simp only [hchk, ↓reduceIte] at hp
              injection hp with hopt; injection hopt with hmEq; subst m
              simp only [Bool.and_eq_true, beq_iff_eq, Option.isSome_iff_exists] at hchk
              obtain ⟨_, ⟨⟨⟨hntM, _⟩, hspM⟩, ⟨t0, hv⟩⟩⟩ := hchk
              have hgoalOr : ∃ goal : NT, goal.ctorIdx = goalIdx := by
                rcases Bool.or_eq_true_iff.mp hnum with h1 | h2
                · exact ⟨.StringNumericLiteral, (beq_iff_eq.mp h1).symm⟩
                · exact ⟨.StringIntegerLiteral, (beq_iff_eq.mp h2).symm⟩
              obtain ⟨goalN, hgoalNEq⟩ := hgoalOr
              obtain ⟨t', hder, hrel⟩ := verifyCodeNode_sound (goal := goalN) (ps := Engine.builder.args n)
                hok (hntM.trans hgoalNEq.symm) (fun _ => Iff.rfl) hspM hv
              exact Or.inl (noCoverSub_of_code_derives (by simp [codeGrammars]) hder hrel)
            · simp only [hchk, Bool.false_eq_true, ↓reduceIte] at hp; cases hp
    · simp only [hnum, Bool.false_eq_true, ↓reduceIte] at hp
      exact hfallback hp

private theorem parsed_inv_gen {M : Ecma.Model} {pc : ParseCx} {d0 : M.Node}
    (hp : Ecma.Model.Parsed M pc d0) :
    ∀ {d : Node}, M = Impl → HEq d0 d → ParsedInv pc d := by
  induction hp with
  | parse hparse =>
    intro d hM hd; subst hM; cases hd
    exact parsedInv_of_parse hparse
  | cover _ hcov ih =>
    intro d hM hd; subst hM; cases hd
    obtain ⟨_, _, _, _, _, _, hsynR⟩ := relabel_core (ih rfl HEq.rfl) (fun _ => mem_paramsOfArgs_iff) hcov
    exact Or.inr hsynR
  | desc _ hdesc ih =>
    intro d hM hd; subst hM; cases hd
    exact parsedInv_desc (ih rfl HEq.rfl) hdesc

theorem parsed_inv {pc : ParseCx} {d : Node} (hp : Ecma.Model.Parsed Impl pc d) :
    ParsedInv pc d :=
  parsed_inv_gen hp rfl HEq.rfl

/-- `Impl`'s `Relabel.relabel` (`Model.cover`) satisfies `Ecma.Model.CoverLaws` (`sound`) over
`Engine.Impl.grammarCtx cx Engine.Model.codePrims strict`. -/
theorem coverLaws (cx : Ctx) (strict : Bool) :
    Ecma.Model.CoverLaws Impl (grammarCtx cx Engine.Model.codePrims strict) where
  sound pc st n goal args ps src r hparsed hps hsrc hcov := by
    obtain ⟨goal', src', tCov, hgoalEq, hsrc', hcovIs, _⟩ :=
      relabel_core (parsed_inv hparsed) hps hcov
    have hgEq : goal' = goal := nt_ctorIdx_inj hgoalEq
    subst hgEq
    have hsrcEq : src = src' := seqOfNats_inj (hsrc.symm.trans hsrc')
    subst hsrcEq
    exact ⟨tCov, hcovIs⟩

end Engine.Impl





