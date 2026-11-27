module

public import Engine.Proofs.Parse.SearchEnds

@[expose] public section

/-!
# Soundness and tree-uniqueness of top-down parse reconstruction (`Engine.Parse.Search.build`)

Proves `provItem_spec`, `provGo_spec`, `fwdOf_spec`, `pick_spec`, `splits_spec`, `phraseSplits_spec`,
`buildRhs_spec`, and `build_spec`. When `build` succeeds without throwing `.ambiguous`, the
resulting node `nd : N` matches a `ModeDerives true` derivation tree `t` via `DNodeRel` AND `t` is
the **unique** `ModeDerives true` tree over that `(n, ps, i, j)`.
-/

namespace Engine.Parse

open Ecma.Grammar Search

theorem sm_ite_throw_jp {T α : Type} {P : Prop} [Decidable P] {err : Stop} {jp : Unit → SM T α}
    {st : St T} {v : α} {st' : St T}
    (h : (if P then (do let r ← (throw err : SM T Unit); jp r) else jp ()).run st = .ok (v, st')) :
    ¬ P ∧ (jp ()).run st = .ok (v, st') := by
  by_cases hp : P
  · simp only [hp, ↓reduceIte] at h
    obtain ⟨_, _, ht, _⟩ := sm_bind_ok h; cases ht
  · simp only [hp, ↓reduceIte] at h
    exact ⟨hp, h⟩

theorem sm_unless_throw_jp {T α : Type} {b : Bool} {err : Stop} {jp : Unit → SM T α}
    {st : St T} {v : α} {st' : St T}
    (h : (if b = true then jp () else (do let r ← (throw err : SM T Unit); jp r)).run st = .ok (v, st')) :
    b = true ∧ (jp ()).run st = .ok (v, st') := by
  cases b with
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h
    obtain ⟨_, _, ht, _⟩ := sm_bind_ok h; cases ht
  | true =>
    simp only [↓reduceIte] at h
    exact ⟨rfl, h⟩

theorem length_ge_two_of_ne_mem {α : Type} {l : List α} {x y : α}
    (hx : x ∈ l) (hy : y ∈ l) (hne : x ≠ y) : 2 ≤ l.length := by
  cases l with
  | nil => cases hx
  | cons a tl =>
    cases tl with
    | nil =>
      simp only [List.mem_singleton] at hx hy
      exact absurd (hx.trans hy.symm) hne
    | cons b tl' => simp only [List.length_cons]; omega

theorem foldl_prov_spec (xs : List Nat) (h : Nat) (m : Std.HashMap Nat (List Nat)) (cur : Nat) :
    let m' := xs.foldl (fun acc j => acc.insert j (acc.getD j [] ++ [h])) m
    (∀ x ∈ m'.getD cur [], x ∈ m.getD cur [] ∨ (cur ∈ xs ∧ x = h)) ∧
    (∀ x ∈ m.getD cur [], x ∈ m'.getD cur []) ∧
    (cur ∈ xs → h ∈ m'.getD cur []) := by
  induction xs generalizing m with
  | nil =>
    exact ⟨fun x hx => Or.inl hx, fun x hx => hx, fun hc => nomatch hc⟩
  | cons j rest ih =>
    let m1 := m.insert j (m.getD j [] ++ [h])
    have hm1 : ∀ q, m1.getD q [] = if j == q then m.getD q [] ++ [h] else m.getD q [] := by
      intro q
      dsimp only [m1]
      cases hjq : j == q with
      | true =>
        have hjeq : j = q := beq_iff_eq.mp hjq
        subst hjeq
        simp only [↓reduceIte]
        rw [hm_getD, hm_insert_eq, Option.getD_some]
      | false =>
        have hjne : j ≠ q := fun heq => by subst heq; rw [beq_self_eq_true] at hjq; cases hjq
        simp only [Bool.false_eq_true, ↓reduceIte]
        rw [hm_getD, hm_insert_ne _ _ hjne, ← hm_getD]
    obtain ⟨hsub, hsup, hin⟩ := ih m1
    refine ⟨fun x hx => ?_, fun x hx => ?_, fun hc => ?_⟩
    · rcases hsub x hx with hx1 | ⟨hcr, rfl⟩
      · rw [hm1 cur] at hx1
        cases hjc : j == cur with
        | true =>
          simp only [hjc, ↓reduceIte, List.mem_append, List.mem_singleton] at hx1
          rw [beq_iff_eq] at hjc
          exact hx1.elim Or.inl (fun xeq => Or.inr ⟨hjc ▸ List.mem_cons_self .., xeq⟩)
        | false =>
          simp only [hjc, Bool.false_eq_true, ↓reduceIte] at hx1
          exact Or.inl hx1
      · exact Or.inr ⟨List.mem_cons_of_mem _ hcr, rfl⟩
    · apply hsup
      rw [hm1 cur]
      cases hjc : j == cur <;> simp only [Bool.false_eq_true, ↓reduceIte, List.mem_append, hx, true_or]
    · rcases List.mem_cons.mp hc with rfl | hcr
      · apply hsup
        rw [hm1 cur]; simp only [beq_self_eq_true, ↓reduceIte]
        exact List.mem_append.mpr (Or.inr (List.mem_singleton.mpr rfl))
      · exact hin hcr

namespace AlphaSpec

variable {N T : Type} {B : Builder N} {A : Alpha N T} {size : Nat} (S : AlphaSpec B A size)

/-! ## `ProvMapValid`, `ProvListValid`, `FwdInv`, `BuildInv`, and `paramBits` invariance -/

def itemHasProv : Item → Bool
  | .sym .. | .butNot .. | .phrase _ => true
  | _ => false

def ProvMapValid (R : NT → List Param → Nat → Nat → Prop) (s : Src) (k : Nat) (ps : List Param)
    (it : Item) (next : Option Item) (before : Ends) (pm : Std.HashMap Nat (List Nat)) : Prop :=
  itemHasProv it = true →
    ∀ cur,
      (∀ h ∈ pm.getD cur [], before.mem h = true) ∧
      (∀ h, before.mem h = true → S.ItemStep R s k ps it next h cur → h ∈ pm.getD cur [])

inductive ProvListValid (R : NT → List Param → Nat → Nat → Prop) (s : Src) (ps : List Param) :
    Nat → List Item → List Ends → List (Std.HashMap Nat (List Nat)) → Prop where
  | nil {k sets} : ProvListValid R s ps k [] sets []
  | cons {k it rest before restSets pm restProvs} :
      S.ProvMapValid R s k ps it rest.head? before pm →
      ProvListValid R s ps (k + 1) rest restSets restProvs →
      ProvListValid R s ps k (it :: rest) (before :: restSets) (pm :: restProvs)

def OptProvValid (R : NT → List Param → Nat → Nat → Prop) (s : Src) (ps : List Param)
    (k : Nat) (is : List Item) (sets : List Ends) :
    Option (List (Std.HashMap Nat (List Nat))) → Prop
  | none => True
  | some pms => S.ProvListValid R s ps k is sets pms

theorem itemMatch_span_paramBits {allow : NT → List Param → Nat → Src → Prop}
    {ps1 ps2 : List Param} (hp : paramBits ps1 = paramBits ps2)
    {s k it next h j} :
    S.ItemMatch (S.SpanOfAllow allow) s k ps1 it next h j ↔
    S.ItemMatch (S.SpanOfAllow allow) s k ps2 it next h j := by
  have hc := contains_eq_of_paramBits hp
  cases it with
  | sym x o =>
    cases x with
    | t _ => exact Iff.rfl
    | nt m args => simp only [ItemMatch, applyArgs_eq_of_contains hc]
  | butNot base ex =>
    cases base with
    | t _ => simp only [ItemMatch, S.exclHolds_paramBits hp]
    | nt m args => simp only [ItemMatch, applyArgs_eq_of_contains hc, S.exclHolds_paramBits hp]
  | _ => exact Iff.rfl

theorem itemStep_span_paramBits {allow : NT → List Param → Nat → Src → Prop}
    {ps1 ps2 : List Param} (hp : paramBits ps1 = paramBits ps2)
    {s k it next h j} :
    S.ItemStep (S.SpanOfAllow allow) s k ps1 it next h j ↔
    S.ItemStep (S.SpanOfAllow allow) s k ps2 it next h j := by
  cases it with
  | sym x o => simp only [ItemStep, S.itemMatch_span_paramBits hp]
  | butNot _ _ => exact S.itemMatch_span_paramBits hp
  | _ => exact Iff.rfl

theorem fwdSetsValid_paramBits {allow : NT → List Param → Nat → Src → Prop}
    {ps1 ps2 : List Param} (hp : paramBits ps1 = paramBits ps2)
    {s k is P sets last}
    (hf : S.FwdSetsValid (S.SpanOfAllow allow) s ps1 k is P sets last) :
    S.FwdSetsValid (S.SpanOfAllow allow) s ps2 k is P sets last := by
  induction hf with
  | nil heq => exact .nil heq
  | cons P' hb hP' _ ih =>
    exact .cons P' hb
      (fun j => (hP' j).trans ⟨fun ⟨h, hh, hs⟩ => ⟨h, hh, (S.itemStep_span_paramBits hp).mp hs⟩,
                               fun ⟨h, hh, hs⟩ => ⟨h, hh, (S.itemStep_span_paramBits hp).mpr hs⟩⟩)
      ih

theorem provListValid_paramBits {allow : NT → List Param → Nat → Src → Prop}
    {ps1 ps2 : List Param} (hp : paramBits ps1 = paramBits ps2)
    {s k is sets pms}
    (hpv : S.ProvListValid (S.SpanOfAllow allow) s ps1 k is sets pms) :
    S.ProvListValid (S.SpanOfAllow allow) s ps2 k is sets pms := by
  induction hpv with
  | nil => exact .nil
  | cons hpm _ ih =>
    exact .cons (fun hkind cur => ⟨(hpm hkind cur).1,
      fun h hh hs => (hpm hkind cur).2 h hh ((S.itemStep_span_paramBits hp).mpr hs)⟩)
      ih

def FwdInv (st : St T) : Prop :=
  ∀ (ck : Key × Nat × Nat) (e : Src) sets last prov,
    st.fwd[ck]? = some (e, sets, last, prov) →
    ∀ n ps i, ck = (key A true n ps i, e.grammar.ctorIdx, e.idx) →
      S.FwdSetsValid (S.SpanOfAllow (S.CommitAllow true)) e ps 0 e.alt.rhs (.single i) sets last ∧
      S.ProvListValid (S.SpanOfAllow (S.CommitAllow true)) e ps 0 e.alt.rhs sets prov

structure BuildInv (st : St T) : Prop where
  memo : S.MemoInv none st
  no_active : ∀ x, st.active.contains x = false
  fwd : S.FwdInv st

theorem BuildInv.of_memo_eq_fwd {S : AlphaSpec B A size} {st st' : St T} (hb : S.BuildInv st)
    (hm : S.MemoInv none st') (hna : ∀ x, st'.active.contains x = false) (hfw : st'.fwd = st.fwd) :
    S.BuildInv st' :=
  ⟨hm, hna, fun ck e sets last prov h => hb.fwd ck e sets last prov (hfw ▸ h)⟩

theorem BuildInv.of_alpha_eq {S : AlphaSpec B A size} {st st' : St T} (hb : S.BuildInv st) (hi' : S.Inv st')
    (hm : st'.memo = st.memo) (ha : st'.active = st.active)
    (hfw : st'.fwd = st.fwd) (hfi : st'.first = st.first) (hfar : st'.far = st.far) :
    S.BuildInv st' :=
  ⟨MemoInv.of_alpha_eq hb.memo hi' hm ha hfi hfar,
   fun x => ha ▸ hb.no_active x,
   fun ck e sets last prov h => hb.fwd ck e sets last prov (hfw ▸ h)⟩

theorem BuildInv.of_fresh_after_finalEnds {S : AlphaSpec B A size} {ft : Option (NT × List Param)} {st : St T}
    (hm : S.MemoInv ft st) (hna : ∀ x, st.active.contains x = false) (hfw : st.fwd = {}) :
    S.BuildInv st :=
  ⟨hm.drop_far, hna, fun ck _ _ _ _ h => by rw [hfw, hm_empty] at h; cases h⟩

/-! ## `provItem_spec`, `provGo_spec`, and `fwdOf_spec` -/

theorem provItem_spec (hok : parseTablesOk = true) (hg : A.g = .syntactic ∨ A.g ∈ codeGrammars)
    (D : Nat) (s : Src) (k : Nat) (ps : List Param) (it : Item) (next : Option Item)
    (hwf : ItemWF A it) :
    ∀ (hs : List Nat) (m : Std.HashMap Nat (List Nat)) (st : St T) (out : Std.HashMap Nat (List Nat)) (st' : St T),
      S.BuildInv st →
      (provItem A (finalEnds A size D) s k ps it next hs m).run st = .ok (out, st') →
      S.BuildInv st' ∧
      ∀ cur,
        (∀ x ∈ out.getD cur [], x ∈ m.getD cur [] ∨ x ∈ hs) ∧
        (∀ x ∈ m.getD cur [], x ∈ out.getD cur []) ∧
        (∀ h ∈ hs, S.ItemStep (S.SpanOfAllow (S.CommitAllow true)) s k ps it next h cur → h ∈ out.getD cur []) := by
  intro hs
  induction hs with
  | nil =>
    intro m st out st' hb hrun
    unfold provItem at hrun
    obtain ⟨rfl, rfl⟩ := sm_pure_ok hrun
    exact ⟨hb, fun _ => ⟨fun x hx => Or.inl hx, fun x hx => hx, fun _ hh => nomatch hh⟩⟩
  | cons h rest ih =>
    intro m st out st' hb hrun
    unfold provItem at hrun
    obtain ⟨js, st1, hstep, hr1⟩ := sm_bind_ok hrun
    have hrecFE : S.RecSpec true none (finalEnds A size D) :=
      { run_spec := fun n' ps' h' st0 es0 st0' hi0 ha0 ho0 hfer => by
          unfold finalEnds finalEndsAt at hfer
          obtain ⟨esE, stE, hends, hchk⟩ := sm_bind_ok hfer
          have ⟨hiE, haE, hmE, hfE, hfwE, hfarE, huE, rsE, VE, ME, hrdE, hpfE, hlE, hvE⟩ :=
            S.ends_spec hok hg D true none (fun x => nomatch x) n' ps' h' st0 esE stE hi0 ha0 ho0 hends
          have hmchk := sm_get_bind_ok hchk
          have hmOk : esE = es0 ∧ st0' = stE := by
            cases hm1 : stE.memo[key A true n' ps' h']? with
            | none => rw [hm1] at hmchk; dsimp only at hmchk; rw [sm_run_throw] at hmchk; cases hmchk
            | some e =>
              rw [hm1] at hmchk; dsimp only at hmchk
              cases hfe : e.final with
              | false => simp only [hfe, Bool.false_eq_true, ↓reduceIte] at hmchk; rw [sm_run_throw] at hmchk; cases hmchk
              | true => simp only [hfe, ↓reduceIte] at hmchk; exact sm_pure_ok hmchk
          obtain ⟨rfl, rfl⟩ := hmOk
          exact ⟨hiE, haE, hmE, hfE, hfwE, hfarE, huE, rsE, VE, ME, hrdE, hpfE, hlE, hvE⟩ }
    have hstepIdle : S.BuildInv st1 ∧
        (∀ j, js.mem j = true ↔ S.ItemStep (S.SpanOfAllow (S.CommitAllow true)) s k ps it next h j) := by
      have hnextEq : next = next.toList.head? := by cases next <;> rfl
      rw [hnextEq] at hstep ⊢
      have ⟨hi1, ha1, _, _, hfw1, _, hu1, rs1, _, M1, _, hpf1, hl1, _⟩ :=
        S.stepItem_spec hrecFE s k ps it next.toList (.single h) st js st1 hb.memo
          (fun _ k_a hk => by rw [hb.no_active k_a] at hk; cases hk)
          hwf (fun _ _ hx => nomatch hx) hstep
      have hna1 : ∀ x, st1.active.contains x = false := fun x => (ha1 x).trans (hb.no_active x)
      have hrsF : ∀ x, rs1 x = false := fun x => by
        cases hrx : rs1 x with
        | false => rfl
        | true => have := hpf1.rs_sub_active x hrx; rw [hna1 x] at this; cases this
      have hcl : ∀ k1, S.OneStepClosed true M1 k1 := fun k1 => hpf1.closed_outside k1 (hrsF k1)
      have hSpToM : ∀ n1 ps1 a1 b1, S.SpanOfAllow (S.CommitAllow true) n1 ps1 a1 b1 → S.OfKey true M1 n1 ps1 a1 b1 :=
        fun _ _ _ _ ⟨t, hd⟩ => S.global_postFix_complete hcl hd
      refine ⟨hb.of_memo_eq_fwd hi1 hna1 hfw1, fun j => ⟨?_, ?_⟩⟩
      · intro hj; obtain ⟨h0, hh0, hs0⟩ := hu1 j hj
        rw [Ends.mem_single, beq_iff_eq] at hh0; subst hh0; exact hs0
      · intro hs0
        exact hl1 h j (by simp [Ends.mem_single]) (S.itemStep_mono hSpToM hs0)
    obtain ⟨hb1, hjsIff⟩ := hstepIdle
    have ⟨hb2, houtSpec⟩ := ih _ st1 out st' hb1 hr1
    refine ⟨hb2, fun cur => ?_⟩
    obtain ⟨hfSub, hfSup, hfIn⟩ := foldl_prov_spec js.toList h m cur
    obtain ⟨hrSub, hrSup, hrIn⟩ := houtSpec cur
    refine ⟨fun x hx => ?_, fun x hx => hrSup x (hfSup x hx), fun h' hh' hs' => ?_⟩
    · rcases hrSub x hx with hxm' | hxr
      · rcases hfSub x hxm' with hxm | ⟨_, rfl⟩
        · exact Or.inl hxm
        · exact Or.inr (List.mem_cons_self ..)
      · exact Or.inr (List.mem_cons_of_mem _ hxr)
    · rcases List.mem_cons.mp hh' with rfl | hhr
      · exact hrSup h' (hfIn ((Ends.mem_toList js cur).mpr ((hjsIff cur).mpr hs')))
      · exact hrIn h' hhr hs'

theorem provGo_spec (hok : parseTablesOk = true) (hg : A.g = .syntactic ∨ A.g ∈ codeGrammars)
    (D : Nat) (s : Src) (ps : List Param) :
    ∀ (k : Nat) (is : List Item) (sets : List Ends) (st : St T)
      (pms : List (Std.HashMap Nat (List Nat))) (st' : St T),
      S.BuildInv st →
      (∀ it ∈ is, ItemWF A it) →
      sets.length = is.length →
      (provGo A (finalEnds A size D) s ps k is sets).run st = .ok (pms, st') →
      S.BuildInv st' ∧
      S.ProvListValid (S.SpanOfAllow (S.CommitAllow true)) s ps k is sets pms := by
  intro k is
  induction is generalizing k with
  | nil =>
    intro sets st pms st' hb _ _ hrun
    unfold provGo at hrun
    obtain ⟨rfl, rfl⟩ := sm_pure_ok hrun
    exact ⟨hb, .nil⟩
  | cons it rest ih =>
    intro sets st pms st' hb hwf hlen hrun
    cases sets with
    | nil => simp at hlen
    | cons before restSets =>
      dsimp only [provGo] at hrun
      have ⟨pm, st1, hb1, hpmV, hr1⟩ : ∃ pm st1,
          S.BuildInv st1 ∧
          S.ProvMapValid (S.SpanOfAllow (S.CommitAllow true)) s k ps it rest.head? before pm ∧
          (do let ms ← provGo A (finalEnds A size D) s ps (k + 1) rest restSets; pure (pm :: ms)).run st1 =
            .ok (pms, st') := by
        cases it with
        | sym _ _ | butNot _ _ | phrase _ =>
          dsimp only at hrun
          obtain ⟨pm, st1, hpmRun, hr1⟩ := sm_bind_ok hrun
          have ⟨hb1, hpv⟩ := S.provItem_spec hok hg D s k ps _ rest.head?
            (hwf _ (List.mem_cons_self ..)) before.toList {} st pm st1 hb hpmRun
          refine ⟨pm, st1, hb1, fun _ cur => ?_, hr1⟩
          obtain ⟨hsub, _, hin⟩ := hpv cur
          refine ⟨fun h hh => ?_, fun h hh hs => hin h ((Ends.mem_toList before h).mpr hh) hs⟩
          rcases hsub h hh with hmt | hhL
          · rw [hm_getD, hm_empty] at hmt; cases hmt
          · exact (Ends.mem_toList before h).mp hhL
        | lookahead _ | noLT | empty | onlyIf _ =>
          dsimp only at hrun
          obtain ⟨pm, st1, hpmRun, hr1⟩ := sm_bind_ok hrun
          obtain ⟨rfl, hst1⟩ := sm_pure_ok hpmRun; subst st1
          exact ⟨_, st, hb, (fun h => nomatch h), hr1⟩
      obtain ⟨ms, st2, hmsRun, hr2⟩ := sm_bind_ok hr1
      obtain ⟨hpmsEq, hst2⟩ := sm_pure_ok hr2; subst hpmsEq; subst st2
      have ⟨hb2, hmsV⟩ := ih (k + 1) restSets st1 ms st' hb1
        (fun it' h => hwf it' (List.mem_cons_of_mem _ h)) (Nat.succ.inj hlen) hmsRun
      exact ⟨hb2, .cons hpmV hmsV⟩

theorem forward_build_spec (hok : parseTablesOk = true) (hg : A.g = .syntactic ∨ A.g ∈ codeGrammars)
    (c : Bool) (D : Nat) (s : Src) (ps : List Param) (i : Nat)
    (st : St T) (sets : List Ends) (last : Ends) (st' : St T)
    (hb : S.BuildInv st)
    (hwf : ∀ it ∈ s.alt.rhs, ItemWF A it)
    (hrun : (forward A (finalEndsAt A size c D) s ps i s.alt.rhs).run st = .ok ((sets, last), st')) :
    S.BuildInv st' ∧
    sets.length = s.alt.rhs.length ∧
    S.FwdSetsValid (S.SpanOfAllow (S.CommitAllow c)) s ps 0 s.alt.rhs (.single i) sets last ∧
    (∀ j, last.mem j = true ↔ S.SeqRel (S.SpanOfAllow (S.CommitAllow c)) s ps 0 s.alt.rhs i j) := by
  have hrecFA : S.RecSpec c none (finalEndsAt A size c D) :=
    { run_spec := fun n' ps' h' st0 es0 st0' hi0 ha0 ho0 hfer => by
        unfold finalEndsAt at hfer
        obtain ⟨esE, stE, hends, hchk⟩ := sm_bind_ok hfer
        have ⟨hiE, haE, hmE, hfE, hfwE, hfarE, huE, rsE, VE, ME, hrdE, hpfE, hlE, hvE⟩ :=
          S.ends_spec hok hg D c none (fun x => nomatch x) n' ps' h' st0 esE stE hi0 ha0 ho0 hends
        have hmchk := sm_get_bind_ok hchk
        have hmOk : esE = es0 ∧ st0' = stE := by
          cases hm1 : stE.memo[key A c n' ps' h']? with
          | none => rw [hm1] at hmchk; dsimp only at hmchk; rw [sm_run_throw] at hmchk; cases hmchk
          | some e =>
            rw [hm1] at hmchk; dsimp only at hmchk
            cases hfe : e.final with
            | false => simp only [hfe, Bool.false_eq_true, ↓reduceIte] at hmchk; rw [sm_run_throw] at hmchk; cases hmchk
            | true => simp only [hfe, ↓reduceIte] at hmchk; exact sm_pure_ok hmchk
        obtain ⟨rfl, rfl⟩ := hmOk
        exact ⟨hiE, haE, hmE, hfE, hfwE, hfarE, huE, rsE, VE, ME, hrdE, hpfE, hlE, hvE⟩ }
  -- Prove by induction over `is` (generalizing `k` and `P`) for `forwardGo` from `BuildInv`:
  have hfg : ∀ (k : Nat) (P : Ends) (is : List Item) (st0 : St T) (sets0 : List Ends) (last0 : Ends) (st1 : St T),
      S.BuildInv st0 → (∀ it ∈ is, ItemWF A it) →
      (forwardGo A (finalEndsAt A size c D) s ps k P is).run st0 = .ok ((sets0, last0), st1) →
      S.BuildInv st1 ∧ sets0.length = is.length ∧
      S.FwdSetsValid (S.SpanOfAllow (S.CommitAllow c)) s ps k is P sets0 last0 ∧
      (∀ j, last0.mem j = true ↔ ∃ h, P.mem h = true ∧ S.SeqRel (S.SpanOfAllow (S.CommitAllow c)) s ps k is h j) := by
    intro k P is
    induction is generalizing k P with
    | nil =>
      intro st0 sets0 last0 st1 hb0 _ hr0
      dsimp only [forwardGo] at hr0
      obtain ⟨hpEq, rfl⟩ := sm_pure_ok hr0
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj hpEq.symm
      exact ⟨hb0, rfl, .nil (fun _ => rfl),
        fun j => ⟨fun hj => ⟨j, hj, .nil⟩, fun ⟨_, hh, hsr⟩ => by cases hsr; exact hh⟩⟩
    | cons it rest ih =>
      intro st0 sets0 last0 st1 hb0 hwf0 hr0
      dsimp only [forwardGo] at hr0
      obtain ⟨P', stM, hsRun, hr1⟩ := sm_bind_ok hr0
      obtain ⟨rPair, stE, hrr, hr2⟩ := sm_bind_ok hr1
      rcases rPair with ⟨rSets, rLast⟩
      dsimp only at hr2
      obtain ⟨hpEq, rfl⟩ := sm_pure_ok hr2
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj hpEq.symm
      have ⟨hiM, haM, _, _, hfwM, _, huM, rsM, _, MM, _, hpfM, hlM, _⟩ :=
        S.stepItem_spec hrecFA s k ps it rest P st0 P' stM hb0.memo
          (fun _ k_a hk => by rw [hb0.no_active k_a] at hk; cases hk)
          (hwf0 it (List.mem_cons_self ..)) (fun _ _ hx => nomatch hx) hsRun
      have hnaM : ∀ x, stM.active.contains x = false := fun x => (haM x).trans (hb0.no_active x)
      have hrsF : ∀ x, rsM x = false := fun x => by
        cases hrx : rsM x with
        | false => rfl
        | true => have := hpfM.rs_sub_active x hrx; rw [hnaM x] at this; cases this
      have hcl : ∀ k1, S.OneStepClosed c MM k1 := fun k1 => hpfM.closed_outside k1 (hrsF k1)
      have hSpToM : ∀ n1 ps1 a1 b1, S.SpanOfAllow (S.CommitAllow c) n1 ps1 a1 b1 → S.OfKey c MM n1 ps1 a1 b1 :=
        fun _ _ _ _ ⟨t, hd⟩ => S.global_postFix_complete hcl hd
      have hP'Iff : ∀ j, P'.mem j = true ↔ ∃ h, P.mem h = true ∧ S.ItemStep (S.SpanOfAllow (S.CommitAllow c)) s k ps it rest.head? h j :=
        fun j => ⟨huM j, fun ⟨h, hh, hs0⟩ => hlM h j hh (S.itemStep_mono hSpToM hs0)⟩
      have hbM : S.BuildInv stM := hb0.of_memo_eq_fwd hiM hnaM hfwM
      have ⟨hbE, hlenE, hfsvE, hlastE⟩ :=
        ih (k + 1) P' stM rSets last0 st1 hbM (fun it' h => hwf0 it' (List.mem_cons_of_mem _ h)) hrr
      refine ⟨hbE, by simp [hlenE], .cons P' (fun _ => rfl) hP'Iff hfsvE, fun j => ?_⟩
      rw [hlastE j]
      constructor
      · rintro ⟨h1, hh1, hsr1⟩
        obtain ⟨h0, hh0, hs0⟩ := (hP'Iff h1).mp hh1
        exact ⟨h0, hh0, .cons hs0 hsr1⟩
      · rintro ⟨h0, hh0, hsr⟩
        cases hsr with
        | cons hs0 hsr1 => exact ⟨_, (hP'Iff _).mpr ⟨h0, hh0, hs0⟩, hsr1⟩
  have ⟨hb', hlen, hfsv, hlast⟩ := hfg 0 (.single i) s.alt.rhs st sets last st' hb hwf hrun
  refine ⟨hb', hlen, hfsv, fun j => ?_⟩
  rw [hlast j]
  constructor
  · rintro ⟨h, hh, hsr⟩; rw [Ends.mem_single, beq_iff_eq] at hh; subst hh; exact hsr
  · intro hsr; exact ⟨i, by simp [Ends.mem_single], hsr⟩

theorem fwdOf_spec (hok : parseTablesOk = true) (hg : A.g = .syntactic ∨ A.g ∈ codeGrammars)
    (D : Nat) (n : NT) (ps : List Param) (i : Nat) (e : Src)
    (he : e ∈ altsOf A.cx A.g n)
    (st : St T) (fw : Fwd) (st' : St T)
    (hb : S.BuildInv st)
    (hrun : (fwdOf A (finalEnds A size D) n ps i e).run st = .ok (fw, st')) :
    S.BuildInv st' ∧
    S.FwdSetsValid (S.SpanOfAllow (S.CommitAllow true)) e ps 0 e.alt.rhs (.single i) fw.sets fw.last ∧
    S.OptProvValid (S.SpanOfAllow (S.CommitAllow true)) e ps 0 e.alt.rhs fw.sets fw.prov ∧
    (∀ j, fw.last.mem j = true ↔ S.SeqRel (S.SpanOfAllow (S.CommitAllow true)) e ps 0 e.alt.rhs i j) := by
  have hwf : ∀ it ∈ e.alt.rhs, ItemWF A it := fun it hit => itemWF_of_mem A hok hg he hit
  have hfsvLast : ∀ {sets last},
      S.FwdSetsValid (S.SpanOfAllow (S.CommitAllow true)) e ps 0 e.alt.rhs (.single i) sets last →
      ∀ j, last.mem j = true ↔ S.SeqRel (S.SpanOfAllow (S.CommitAllow true)) e ps 0 e.alt.rhs i j := by
    intro sets last hfsv
    have hgen : ∀ {k P is sets0 last0},
        S.FwdSetsValid (S.SpanOfAllow (S.CommitAllow true)) e ps k is P sets0 last0 →
        ∀ j, last0.mem j = true ↔ ∃ h, P.mem h = true ∧ S.SeqRel (S.SpanOfAllow (S.CommitAllow true)) e ps k is h j := by
      intro k P is sets0 last0 hf
      induction hf with
      | nil heq =>
        intro j; rw [heq]
        exact ⟨fun hj => ⟨j, hj, .nil⟩, fun ⟨_, hh, hsr⟩ => by cases hsr; exact hh⟩
      | cons P' _ hP' _ ih =>
        intro j; rw [ih j]
        constructor
        · rintro ⟨h1, hh1, hsr1⟩
          obtain ⟨h0, hh0, hs0⟩ := (hP' h1).mp hh1
          exact ⟨h0, hh0, .cons hs0 hsr1⟩
        · rintro ⟨h0, hh0, hsr⟩
          cases hsr with
          | cons hs0 hsr1 => exact ⟨_, (hP' _).mpr ⟨h0, hh0, hs0⟩, hsr1⟩
    intro j; rw [hgen hfsv j]
    constructor
    · rintro ⟨h, hh, hsr⟩; rw [Ends.mem_single, beq_iff_eq] at hh; subst hh; exact hsr
    · intro hsr; exact ⟨i, by simp [Ends.mem_single], hsr⟩
  dsimp only [fwdOf] at hrun
  cases hlr : leftRec n ps e with
  | false =>
    simp only [hlr, Bool.not_false, ↓reduceIte] at hrun
    obtain ⟨fPair, st1, hfwr, hp⟩ := sm_bind_ok hrun
    rcases fPair with ⟨sets, last⟩
    dsimp only at hp
    obtain ⟨hfwEq, hst1⟩ := sm_pure_ok hp; subst hfwEq; subst st1
    have ⟨hb1, _, hfsv, hlast⟩ := S.forward_build_spec hok hg true D e ps i st sets last st' hb hwf hfwr
    exact ⟨hb1, hfsv, trivial, hlast⟩
  | true =>
    simp only [hlr, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hrun
    let ck := (key A true n ps i, e.grammar.ctorIdx, e.idx)
    have hmiss : ∀ hmissRun :
        (do
          let (sets, last) ← forward A (finalEnds A size D) e ps i e.alt.rhs
          let prov ← provGo A (finalEnds A size D) e ps 0 e.alt.rhs sets
          modify fun (s : St T) => { s with fwd := s.fwd.insert ck (e, sets, last, prov) }
          pure (Fwd.mk sets last (some prov))).run st = .ok (fw, st'),
        S.BuildInv st' ∧
        S.FwdSetsValid (S.SpanOfAllow (S.CommitAllow true)) e ps 0 e.alt.rhs (.single i) fw.sets fw.last ∧
        S.OptProvValid (S.SpanOfAllow (S.CommitAllow true)) e ps 0 e.alt.rhs fw.sets fw.prov ∧
        (∀ j, fw.last.mem j = true ↔ S.SeqRel (S.SpanOfAllow (S.CommitAllow true)) e ps 0 e.alt.rhs i j) := by
      intro hmissRun
      obtain ⟨fPair, st1, hfwr, hr1⟩ := sm_bind_ok hmissRun
      rcases fPair with ⟨sets, last⟩
      dsimp only at hr1
      obtain ⟨prov, st2, hpgr, hr2⟩ := sm_bind_ok hr1
      obtain ⟨_, st3, hmod, hr3⟩ := sm_bind_ok hr2
      obtain ⟨_, hst3⟩ := sm_pure_ok hmod; subst st3
      obtain ⟨hfwEq, hst'⟩ := sm_pure_ok hr3; subst hfwEq; subst st'
      have ⟨hb1, hlen, hfsv, hlast⟩ := S.forward_build_spec hok hg true D e ps i st sets last st1 hb hwf hfwr
      have ⟨hb2, hpv⟩ := S.provGo_spec hok hg D e ps 0 e.alt.rhs sets st1 prov st2 hb1 hwf hlen hpgr
      have hi3 : S.MemoInv none { st2 with fwd := st2.fwd.insert ck (e, sets, last, prov) } :=
        MemoInv.of_alpha_eq hb2.memo (S.inv_mono_memo st2 _ _ _ _ _ _ hb2.memo.inv) rfl rfl rfl rfl
      have hfwd3 : S.FwdInv { st2 with fwd := st2.fwd.insert ck (e, sets, last, prov) } := by
        intro ck' e' sets' last' prov' hget n' ps' i' hck'
        dsimp only at hget
        by_cases hcc : ck = ck'
        · subst hcc; rw [hm_insert_eq] at hget; cases hget
          have hkEq : key A true n ps i = key A true n' ps' i' := by
            injection hck'
          obtain ⟨rfl, hpbits, rfl, _⟩ := key_inj hkEq
          exact ⟨S.fwdSetsValid_paramBits hpbits hfsv, S.provListValid_paramBits hpbits hpv⟩
        · rw [hm_insert_ne _ _ hcc] at hget
          exact hb2.fwd ck' e' sets' last' prov' hget n' ps' i' hck'
      exact ⟨⟨hi3, hb2.no_active, hfwd3⟩, hfsv, hpv, hlast⟩
    have hr0 := sm_get_bind_ok hrun
    cases hfc : st.fwd[ck]? with
    | none =>
      rw [show st.fwd[(key A true n ps i, e.grammar.ctorIdx, e.idx)]? = none from hfc] at hr0
      dsimp only at hr0
      exact hmiss hr0
    | some entry =>
      rcases entry with ⟨e', sets0, last0, prov0⟩
      rw [show st.fwd[(key A true n ps i, e.grammar.ctorIdx, e.idx)]? = some (e', sets0, last0, prov0) from hfc] at hr0
      dsimp only at hr0
      by_cases hee : e' = e
      · subst hee
        simp only [↓reduceIte] at hr0
        obtain ⟨hfwEq, rfl⟩ := sm_pure_ok hr0; subst hfwEq
        obtain ⟨hfsv0, hpv0⟩ := hb.fwd ck e' sets0 last0 prov0 hfc n ps i rfl
        exact ⟨hb, hfsv0, hpv0, hfsvLast hfsv0⟩
      · simp only [hee, ↓reduceIte] at hr0
        exact hmiss hr0

/-! ## `pickLoop_spec` and `pick_spec` -/

theorem pickLoop_some_spec (hok : parseTablesOk = true) (hg : A.g = .syntactic ∨ A.g ∈ codeGrammars)
    (D : Nat) (n : NT) (ps : List Param) (i j : Nat) :
    ∀ (rem : List Src) (p0 res : Option (Src × Fwd)) (ef : Src) (fwf : Fwd) (st st' : St T),
      p0 = some (ef, fwf) →
      S.BuildInv st →
      (∀ x ∈ rem, x ∈ altsOf A.cx A.g n) →
      (pickLoop A (finalEnds A size D) n ps i j rem p0).run st = .ok (res, st') →
      S.BuildInv st' ∧ res = some (ef, fwf) ∧
      ∀ x ∈ rem, x.alt.guard.all (Guard.holds ps) = true →
        ¬ S.SeqRel (S.SpanOfAllow (S.CommitAllow true)) x ps 0 x.alt.rhs i j := by
  intro rem
  induction rem with
  | nil =>
    intro p0 res ef fwf st st' hp0 hb _ hrun; subst hp0
    unfold pickLoop at hrun
    obtain ⟨rfl, rfl⟩ := sm_pure_ok hrun
    exact ⟨hb, rfl, fun _ hx => nomatch hx⟩
  | cons e es ih =>
    intro p0 res ef fwf st st' hp0 hb hrem hrun; subst hp0
    unfold pickLoop at hrun
    cases hgrd : e.alt.guard.all (Guard.holds ps) with
    | false =>
      simp only [hgrd, Bool.not_false, ↓reduceIte] at hrun
      have ⟨hb', hres, hno⟩ := ih _ res ef fwf st st' rfl hb
        (fun x hx => hrem x (List.mem_cons_of_mem _ hx)) hrun
      refine ⟨hb', hres, fun x hx hgx => ?_⟩
      rcases List.mem_cons.mp hx with rfl | hx
      · rw [hgrd] at hgx; cases hgx
      · exact hno x hx hgx
    | true =>
      simp only [hgrd, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hrun
      obtain ⟨fw, st1, hfwr, hr1⟩ := sm_bind_ok hrun
      have ⟨hb1, _, _, hlast⟩ := S.fwdOf_spec hok hg D n ps i e (hrem e (List.mem_cons_self ..)) st fw st1 hb hfwr
      cases hmem : fw.last.mem j with
      | false =>
        simp only [hmem, Bool.not_false, ↓reduceIte] at hr1
        have ⟨hb', hres, hno⟩ := ih _ res ef fwf st1 st' rfl hb1
          (fun x hx => hrem x (List.mem_cons_of_mem _ hx)) hr1
        refine ⟨hb', hres, fun x hx hgx => ?_⟩
        rcases List.mem_cons.mp hx with rfl | hx
        · intro hsr; rw [(hlast j).mpr hsr] at hmem; cases hmem
        · exact hno x hx hgx
      | true =>
        simp only [hmem, Bool.not_true, Bool.false_eq_true, ↓reduceIte, Option.isSome_some] at hr1
        obtain ⟨_, _, ht, _⟩ := sm_bind_ok hr1; cases ht

theorem pickLoop_none_spec (hok : parseTablesOk = true) (hg : A.g = .syntactic ∨ A.g ∈ codeGrammars)
    (D : Nat) (n : NT) (ps : List Param) (i j : Nat) :
    ∀ (rem : List Src) (ef : Src) (fwf : Fwd) (st st' : St T),
      S.BuildInv st →
      (∀ x ∈ rem, x ∈ altsOf A.cx A.g n) →
      (pickLoop A (finalEnds A size D) n ps i j rem none).run st = .ok (some (ef, fwf), st') →
      S.BuildInv st' ∧
      ef ∈ rem ∧
      ef.alt.guard.all (Guard.holds ps) = true ∧
      fwf.last.mem j = true ∧
      S.FwdSetsValid (S.SpanOfAllow (S.CommitAllow true)) ef ps 0 ef.alt.rhs (.single i) fwf.sets fwf.last ∧
      S.OptProvValid (S.SpanOfAllow (S.CommitAllow true)) ef ps 0 ef.alt.rhs fwf.sets fwf.prov ∧
      ∀ x ∈ rem, x.alt.guard.all (Guard.holds ps) = true →
        S.SeqRel (S.SpanOfAllow (S.CommitAllow true)) x ps 0 x.alt.rhs i j → x = ef := by
  intro rem
  induction rem with
  | nil =>
    intro _ _ _ _ _ _ hrun
    unfold pickLoop at hrun; obtain ⟨h, _⟩ := sm_pure_ok hrun; cases h
  | cons e es ih =>
    intro ef fwf st st' hb hrem hrun
    unfold pickLoop at hrun
    cases hgrd : e.alt.guard.all (Guard.holds ps) with
    | false =>
      simp only [hgrd, Bool.not_false, ↓reduceIte] at hrun
      have ⟨hb', hmemEf, hgEf, hjEf, hfsv, hpv, huniq⟩ :=
        ih ef fwf st st' hb (fun x hx => hrem x (List.mem_cons_of_mem _ hx)) hrun
      refine ⟨hb', List.mem_cons_of_mem _ hmemEf, hgEf, hjEf, hfsv, hpv, fun x hx hgx hsr => ?_⟩
      rcases List.mem_cons.mp hx with rfl | hx
      · rw [hgrd] at hgx; cases hgx
      · exact huniq x hx hgx hsr
    | true =>
      simp only [hgrd, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hrun
      obtain ⟨fw, st1, hfwr, hr1⟩ := sm_bind_ok hrun
      have ⟨hb1, hfsv0, hpv0, hlast0⟩ :=
        S.fwdOf_spec hok hg D n ps i e (hrem e (List.mem_cons_self ..)) st fw st1 hb hfwr
      cases hmem : fw.last.mem j with
      | false =>
        simp only [hmem, Bool.not_false, ↓reduceIte] at hr1
        have ⟨hb', hmemEf, hgEf, hjEf, hfsv, hpv, huniq⟩ :=
          ih ef fwf st1 st' hb1 (fun x hx => hrem x (List.mem_cons_of_mem _ hx)) hr1
        refine ⟨hb', List.mem_cons_of_mem _ hmemEf, hgEf, hjEf, hfsv, hpv, fun x hx hgx hsr => ?_⟩
        rcases List.mem_cons.mp hx with rfl | hx
        · exfalso; rw [(hlast0 j).mpr hsr] at hmem; cases hmem
        · exact huniq x hx hgx hsr
      | true =>
        simp only [hmem, Bool.not_true, Bool.false_eq_true, ↓reduceIte, Option.isSome_none] at hr1
        have ⟨hb', hEq, hnoRest⟩ :=
          S.pickLoop_some_spec hok hg D n ps i j es (some (e, fw)) (some (ef, fwf)) e fw st1 st' rfl hb1
            (fun x hx => hrem x (List.mem_cons_of_mem _ hx)) hr1
        injection hEq with hPair
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj hPair.symm
        refine ⟨hb', List.mem_cons_self .., hgrd, hmem, hfsv0, hpv0, fun x hx hgx hsr => ?_⟩
        rcases List.mem_cons.mp hx with rfl | hx
        · rfl
        · exact absurd hsr (hnoRest x hx hgx)

theorem pick_spec (hok : parseTablesOk = true) (hg : A.g = .syntactic ∨ A.g ∈ codeGrammars)
    (D : Nat) (n : NT) (ps : List Param) (i j : Nat)
    (st : St T) (e : Src) (fw : Fwd) (st' : St T)
    (hb : S.BuildInv st)
    (hrun : (pick A (finalEnds A size D) (finalEndsAt A size false D) n ps i j (altsOf A.cx A.g n)).run st =
      .ok (some (e, fw), st')) :
    S.BuildInv st' ∧
    e ∈ altsOf A.cx A.g n ∧
    S.CommitAllow true n ps i e ∧
    e.alt.guard.all (Guard.holds ps) = true ∧
    fw.last.mem j = true ∧
    S.FwdSetsValid (S.SpanOfAllow (S.CommitAllow true)) e ps 0 e.alt.rhs (.single i) fw.sets fw.last ∧
    S.OptProvValid (S.SpanOfAllow (S.CommitAllow true)) e ps 0 e.alt.rhs fw.sets fw.prov ∧
    (∀ e' ∈ altsOf A.cx A.g n, S.CommitAllow true n ps i e' →
      e'.alt.guard.all (Guard.holds ps) = true →
      S.SeqRel (S.SpanOfAllow (S.CommitAllow true)) e' ps 0 e'.alt.rhs i j → e' = e) := by
  dsimp only [pick] at hrun
  cases hordNt : (orderedNtsBy A.cx A.g).contains n with
  | false =>
    simp only [hordNt, Bool.false_eq_true, ↓reduceIte] at hrun
    obtain ⟨es0, st0, hp0, hloop⟩ := sm_bind_ok hrun
    obtain ⟨rfl, hst0⟩ := sm_pure_ok hp0; subst st0
    have ⟨hb', heMem, heGrd, hjMem, hfsv, hpv, huniq⟩ :=
      S.pickLoop_none_spec hok hg D n ps i j (altsOf A.cx A.g n) e fw st st' hb (fun _ h => h) hloop
    have hca : S.CommitAllow true n ps i e := by
      unfold CommitAllow; simp only [Bool.true_and, hordNt, Bool.false_eq_true, ↓reduceIte]
    exact ⟨hb', heMem, hca, heGrd, hjMem, hfsv, hpv, fun e' he' _ hge' hsr' => huniq e' he' hge' hsr'⟩
  | true =>
    simp only [hordNt, ↓reduceIte] at hrun
    obtain ⟨ro, st1, hfaRun, hrRest⟩ := sm_bind_ok hrun
    obtain ⟨es0, st1', hp0, hloop⟩ := sm_bind_ok hrRest
    obtain ⟨rfl, hst1'⟩ := sm_pure_ok hp0; subst st1'
    have hrecFA : S.RecSpec false none (finalEndsAt A size false D) :=
      { run_spec := fun n' ps' h' st0 esA st0' hi0 ha0 ho0 hfer => by
          unfold finalEndsAt at hfer
          obtain ⟨esE, stE, hends, hchk⟩ := sm_bind_ok hfer
          have ⟨hiE, haE, hmE, hfE, hfwE, hfarE, huE, rsE, VE, ME, hrdE, hpfE, hlE, hvE⟩ :=
            S.ends_spec hok hg D false none (fun x => nomatch x) n' ps' h' st0 esE stE hi0 ha0 ho0 hends
          have hmchk := sm_get_bind_ok hchk
          have hmOk : esE = esA ∧ st0' = stE := by
            cases hm1 : stE.memo[key A false n' ps' h']? with
            | none => rw [hm1] at hmchk; dsimp only at hmchk; rw [sm_run_throw] at hmchk; cases hmchk
            | some ef =>
              rw [hm1] at hmchk; dsimp only at hmchk
              cases hfe : ef.final with
              | false => simp only [hfe, Bool.false_eq_true, ↓reduceIte] at hmchk; rw [sm_run_throw] at hmchk; cases hmchk
              | true => simp only [hfe, ↓reduceIte] at hmchk; exact sm_pure_ok hmchk
          obtain ⟨rfl, rfl⟩ := hmOk
          exact ⟨hiE, haE, hmE, hfE, hfwE, hfarE, huE, rsE, VE, ME, hrdE, hpfE, hlE, hvE⟩ }
    have ⟨hi1, ha1, _, _, _, hfw1, _, hroSpec⟩ :=
      S.firstAlt_spec hok hg hrecFA n ps i st ro st1 rfl hb.memo
        (fun k_a hk => by rw [hb.no_active k_a] at hk; cases hk) hfaRun
    have hb1 : S.BuildInv st1 := hb.of_memo_eq_fwd hi1 (fun x => (ha1 x).trans (hb.no_active x)) hfw1
    cases ro with
    | none =>
      unfold pickLoop at hloop; obtain ⟨h, _⟩ := sm_pure_ok hloop; cases h
    | some s0 =>
      obtain ⟨pre0, post0, halts0, _, _⟩ := id hroSpec
      have hs0Mem : s0 ∈ altsOf A.cx A.g n := halts0 ▸ List.mem_append.mpr (Or.inr (List.mem_cons_self ..))
      have ⟨hb', heMem, heGrd, hjMem, hfsv, hpv, _⟩ :=
        S.pickLoop_none_spec hok hg D n ps i j [s0] e fw st1 st' hb1
          (fun x hx => by simp only [List.mem_singleton] at hx; subst hx; exact hs0Mem) hloop
      simp only [List.mem_singleton] at heMem; subst heMem
      have hca : S.CommitAllow true n ps i e := by
        unfold CommitAllow; simp only [Bool.true_and, hordNt, ↓reduceIte]; exact hroSpec
      refine ⟨hb', hs0Mem, hca, heGrd, hjMem, hfsv, hpv, fun e' _ hca' _ _ => ?_⟩
      unfold CommitAllow at hca'
      simp only [Bool.true_and, hordNt, ↓reduceIte] at hca'
      exact S.isFirstAlt_unique hca' hroSpec

/-! ## `splits_spec`, `phraseSplits_spec`, `buildRhs_spec`, and `build_spec` -/

def ChildSpec (stamp : Nat) (child : NT → List Param → Nat → Nat → SM T N) : Prop :=
  ∀ m ps h j st nd st',
    S.BuildInv st →
    (child m ps h j).run st = .ok (nd, st') →
    S.BuildInv st' ∧
    B.nt nd = m.ctorIdx ∧
    B.args nd = ps ∧
    ∃ t,
      S.ModeDerives true m ps h j t ∧
      S.DNodeRel stamp nd t ∧
      (∀ t', S.ModeDerives true m ps h j t' → t' = t)

def MkPieceSpec (stamp : Nat) (ps : List Param) (x : Sym) (h cur : Nat)
    (mkPiece : SM T (Piece N)) : Prop :=
  ∀ st pc st',
    S.BuildInv st →
    mkPiece.run st = .ok (pc, st') →
    S.BuildInv st' ∧
    S.PieceValid (S.CommitAllow true) stamp pc ∧
    match x with
    | .t _ => pc = .span h cur
    | .nt m args =>
      if !(altsOf A.cx A.g m).isEmpty then
        ∃ c t_c, pc = .kid c h cur ∧
          S.ModeDerives true m (applyArgs ps args) h cur t_c ∧
          (∀ t', S.ModeDerives true m (applyArgs ps args) h cur t' → t' = t_c)
      else
        ∃ c, pc = .kid c h cur

def itemOfSplit (x : Sym) (o : Bool) : Option Exclusion → Item
  | none => .sym x o
  | some e => .butNot x e

theorem sm_ite_true {T α : Type} {b : Bool} {m1 m2 : SM T α} {st : St T} {v : α} {st' : St T}
    (h : (if b = true then m1 else m2).run st = .ok (v, st')) (hb : b = true) :
    m1.run st = .ok (v, st') := by rw [hb] at h; exact h

theorem sm_ite_false {T α : Type} {b : Bool} {m1 m2 : SM T α} {st : St T} {v : α} {st' : St T}
    (h : (if b = true then m1 else m2).run st = .ok (v, st')) (hb : b = false) :
    m2.run st = .ok (v, st') := by rw [hb] at h; simp only [Bool.false_eq_true, ↓reduceIte] at h; exact h

def OptExclRes {T α : Type} (A : Alpha N T) (s : Src) (k : Nat) (ps : List Param) (h cur : Nat)
    (jp : Bool → SM T α) (st : St T) (v : α) (st' : St T) : Option Exclusion → Prop
  | none => (jp false).run st = .ok (v, st')
  | some e => ∃ skip st1, (excluded A s k ps h cur e).run st = .ok (skip, st1) ∧ (jp skip).run st1 = .ok (v, st')

theorem sm_opt_excl {T α : Type} (A : Alpha N T) (s : Src) (k : Nat) (ps : List Param) (h cur : Nat)
    (ex : Option Exclusion) (jp : Bool → SM T α) {st : St T} {v : α} {st' : St T}
    (hrun : (match ex with
             | some e => do let skip ← excluded A s k ps h cur e; jp skip
             | none => do let skip ← pure false; jp skip).run st = .ok (v, st')) :
    OptExclRes A s k ps h cur jp st v st' ex := by
  cases ex with
  | none =>
    dsimp only at hrun
    obtain ⟨skip, st1, hp, hr⟩ := sm_bind_ok hrun
    obtain ⟨rfl, hst1⟩ := sm_pure_ok hp; subst st1
    exact hr
  | some e =>
    dsimp only at hrun
    exact sm_bind_ok hrun

theorem splits_spec (hok : parseTablesOk = true) (hg : A.g = .syntactic ∨ A.g ∈ codeGrammars)
    (D stamp : Nat) {child : NT → List Param → Nat → Nat → SM T N} (hchild : S.ChildSpec stamp child)
    (s : Src) (k : Nat) (ps : List Param) (x : Sym) (o : Bool) (next : Option Item)
    (cur : Nat) (ex : Option Exclusion)
    (hexWf : match ex with | none => True | some e => ExclWF A e ∧ next = none)
    (hstmp : S.LeafStamp.all (· == stamp) = true := by rfl) :
    ∀ (cands : List Nat) (st : St T) (present : List (Nat × SM T (Piece N))) (st' : St T),
      S.BuildInv st →
      (splits A (finalEnds A size D) child s k ps x next cur ex cands).run st = .ok (present, st') →
      S.BuildInv st' ∧
      (∀ p ∈ present, p.1 ∈ cands ∧
        S.ItemMatch (S.SpanOfAllow (S.CommitAllow true)) s k ps (itemOfSplit x o ex) next p.1 cur ∧
        S.MkPieceSpec stamp ps x p.1 cur p.2) ∧
      (∀ h ∈ cands,
        S.ItemMatch (S.SpanOfAllow (S.CommitAllow true)) s k ps (itemOfSplit x o ex) next h cur →
        ∃ mkp, (h, mkp) ∈ present) := by
  intro cands
  induction cands with
  | nil =>
    intro st present st' hb hrun
    dsimp only [splits] at hrun
    obtain ⟨rfl, rfl⟩ := sm_pure_ok hrun
    exact ⟨hb, (fun _ hp => nomatch hp), (fun _ hh => nomatch hh)⟩
  | cons h hs ih =>
    intro st present st' hb hrun
    dsimp only [splits] at hrun
    have hoe := sm_opt_excl A s k ps h cur ex _ hrun
    have ⟨skip, st1, hb1, hskipIff, hr1⟩ : ∃ skip st1,
        S.BuildInv st1 ∧
        (skip = true ↔ match ex with | none => False | some e => S.ExclHolds s k ps h cur e) ∧
        (if skip = true then splits A (finalEnds A size D) child s k ps x next cur ex hs
         else
           have __do_jp := fun (hit? : Option (SM T (Piece N))) => do
             let rest ← splits A (finalEnds A size D) child s k ps x next cur ex hs
             pure (match hit? with | some mkPiece => (h, mkPiece) :: rest | none => rest)
           match x with
           | .t t => do
             let r ← A.term s k t h
             if (r == some cur) = true then do let hit? ← pure (some (pure (Piece.span h cur))); __do_jp hit?
             else do let hit? ← pure none; __do_jp hit?
           | .nt m args =>
             have ps' := applyArgs ps args
             have isRule := !(altsOf A.cx A.g m).isEmpty
             have __do_jp1 := fun (ok : Bool) =>
               have __do_jp2 := fun (cr : Bool) =>
                 have ok := ok && A.keep s.rule.lhs m cur && cr
                 if ok = true then do
                   let hit? ← pure (some (if isRule = true then return Piece.kid (← child m ps' h cur) h cur
                                          else return Piece.kid (← A.leafNode m h cur) h cur))
                   __do_jp hit?
                 else do let hit? ← pure none; __do_jp hit?
               match next with
               | some (.onlyIf c) =>
                 if ok = true then do let cr ← A.cond c h cur; __do_jp2 cr
                 else do let cr ← pure true; __do_jp2 cr
               | _ => do let cr ← pure true; __do_jp2 cr
             if isRule = true then do
               let es ← finalEnds A size D m ps' h
               let ok ← pure (es.mem cur)
               __do_jp1 ok
             else do
               let r ← A.leaf m h
               let ok ← pure (r == some cur)
               __do_jp1 ok).run st1 = .ok (present, st') := by
      cases ex with
      | none => exact ⟨false, st, hb, by simp, hoe⟩
      | some e =>
        obtain ⟨skip, st1, hexRun, hr1⟩ := hoe
        have ⟨hi1, hm1, ha1, _, hfw1, hfi1, hfar1, hexIff⟩ :=
          excluded_spec S s k ps h cur e st hb.memo.inv hexWf.1 skip st1 hexRun
        exact ⟨skip, st1, hb.of_alpha_eq hi1 hm1 ha1 hfw1 hfi1 hfar1, hexIff, hr1⟩
    cases skip with
    | true =>
      have hr1' := sm_ite_true hr1 rfl
      have ⟨hb', hsound, hcomp⟩ := ih st1 present st' hb1 hr1'
      refine ⟨hb',
        fun p hp => ⟨List.mem_cons_of_mem _ (hsound p hp).1, (hsound p hp).2⟩,
        fun h' hh' hm' => ?_⟩
      rcases List.mem_cons.mp hh' with rfl | hh'
      · exfalso
        have hexH := hskipIff.mp rfl
        cases ex with
        | none => exact hexH
        | some e =>
          cases x with
          | t _ => exact hm'.2 hexH
          | nt _ _ => exact hm'.2.1 hexH
      · exact hcomp h' hh' hm'
    | false =>
      have hr1' := sm_ite_false hr1 rfl
      have hnotEx : match ex with | none => True | some e => ¬ S.ExclHolds s k ps h cur e := by
        cases ex with
        | none => trivial
        | some e => intro hh; exact Bool.false_ne_true (hskipIff.mpr hh)
      have hfinish : ∀ (hit? : Option (SM T (Piece N))) (st2 : St T),
          S.BuildInv st2 →
          (match hit? with
           | some mkp =>
             S.ItemMatch (S.SpanOfAllow (S.CommitAllow true)) s k ps (itemOfSplit x o ex) next h cur ∧
             S.MkPieceSpec stamp ps x h cur mkp
           | none =>
             ¬ S.ItemMatch (S.SpanOfAllow (S.CommitAllow true)) s k ps (itemOfSplit x o ex) next h cur) →
          (do let rest ← splits A (finalEnds A size D) child s k ps x next cur ex hs
              pure (match hit? with | some mkPiece => (h, mkPiece) :: rest | none => rest)).run st2 =
            .ok (present, st') →
          S.BuildInv st' ∧
          (∀ p ∈ present, p.1 ∈ h :: hs ∧
            S.ItemMatch (S.SpanOfAllow (S.CommitAllow true)) s k ps (itemOfSplit x o ex) next p.1 cur ∧
            S.MkPieceSpec stamp ps x p.1 cur p.2) ∧
          (∀ h' ∈ h :: hs,
            S.ItemMatch (S.SpanOfAllow (S.CommitAllow true)) s k ps (itemOfSplit x o ex) next h' cur →
            ∃ mkp, (h', mkp) ∈ present) := by
        intro hit? st2 hb2 hhSpec hr2
        obtain ⟨rest, st3, hrestRun, hr3⟩ := sm_bind_ok hr2
        obtain ⟨hpresEq, hst3⟩ := sm_pure_ok hr3; subst hpresEq; subst st3
        have ⟨hb3, hrestSound, hrestComp⟩ := ih st2 rest st' hb2 hrestRun
        cases hit? with
        | some mkp =>
          refine ⟨hb3, fun p hp => ?_, fun h' hh' hm' => ?_⟩
          · rcases List.mem_cons.mp hp with rfl | hp
            · exact ⟨List.mem_cons_self .., hhSpec.1, hhSpec.2⟩
            · exact ⟨List.mem_cons_of_mem _ (hrestSound p hp).1, (hrestSound p hp).2⟩
          · rcases List.mem_cons.mp hh' with rfl | hh'
            · exact ⟨mkp, List.mem_cons_self ..⟩
            · obtain ⟨mkp', hmp'⟩ := hrestComp h' hh' hm'
              exact ⟨mkp', List.mem_cons_of_mem _ hmp'⟩
        | none =>
          refine ⟨hb3,
            fun p hp => ⟨List.mem_cons_of_mem _ (hrestSound p hp).1, (hrestSound p hp).2⟩,
            fun h' hh' hm' => ?_⟩
          rcases List.mem_cons.mp hh' with rfl | hh'
          · exact absurd hm' hhSpec
          · exact hrestComp h' hh' hm'
      cases x with
      | t tm =>
        dsimp only at hr1'
        obtain ⟨to0, stT, htr, htp⟩ := sm_bind_ok hr1'
        have ⟨hiT, hmT, haT, _, hfwT, hfiT, hfarT, hto⟩ := S.term_spec s k tm h st1 hb1.memo.inv to0 stT htr
        have hbT : S.BuildInv stT := hb1.of_alpha_eq hiT hmT haT hfwT hfiT hfarT
        cases heq : to0 == some cur with
        | true =>
          have htp' := sm_ite_true htp heq
          obtain ⟨hit?, st2, hpHit, hr2⟩ := sm_bind_ok htp'
          obtain ⟨rfl, hst2⟩ := sm_pure_ok hpHit; subst st2
          rw [beq_iff_eq] at heq
          have htm : S.Term s k tm h cur := by
            rcases hto with ⟨j0, hj0, htj0⟩ | ⟨hnone, _⟩
            · cases hj0.symm.trans heq; exact htj0
            · rw [hnone] at heq; cases heq
          refine hfinish (some _) stT hbT ⟨?_, ?_⟩ hr2
          · cases ex with
            | none => exact htm
            | some _ => exact ⟨htm, hnotEx⟩
          · intro stP pc stP' hbP hpr
            obtain ⟨rfl, rfl⟩ := sm_pure_ok hpr
            exact ⟨hbP, .span h cur, rfl⟩
        | false =>
          have htp' := sm_ite_false htp heq
          obtain ⟨hit?, st2, hpHit, hr2⟩ := sm_bind_ok htp'
          obtain ⟨rfl, hst2⟩ := sm_pure_ok hpHit; subst st2
          have hntm : ¬ S.Term s k tm h cur := by
            intro htm
            rcases hto with ⟨j0, rfl, htj0⟩ | ⟨_, hno⟩
            · have := S.term_det s k tm h j0 cur htj0 htm; subst this; simp at heq
            · exact hno cur htm
          refine hfinish none stT hbT ?_ hr2
          cases ex with
          | none => exact hntm
          | some _ => exact fun hm => hntm hm.1
      | nt m args =>
        dsimp only at hr1'
        let ps' := applyArgs ps args
        let mkP : SM T (Piece N) :=
          if (!(altsOf A.cx A.g m).isEmpty) = true then do
            let c ← child m ps' h cur
            pure (Piece.kid c h cur)
          else do
            let c ← A.leafNode m h cur
            pure (Piece.kid c h cur)
        have hmkP : S.MkPieceSpec stamp ps (.nt m args) h cur mkP := by
          intro stP pc stP' hbP hpr
          dsimp only [mkP] at hpr
          cases hem : (altsOf A.cx A.g m).isEmpty with
          | false =>
            have hpr' := sm_ite_true hpr (by rw [hem]; rfl)
            simp only [hem, Bool.not_false, ↓reduceIte]
            obtain ⟨ndC, stC, hcRun, hpC⟩ := sm_bind_ok hpr'
            obtain ⟨rfl, hstC⟩ := sm_pure_ok hpC; subst stC
            have ⟨hbC, hntC, hargsC, t_c, hderC, hdrelC, huniqC⟩ :=
              hchild m ps' h cur stP ndC stP' hbP hcRun
            exact ⟨hbC, .kidRule hem hntC (hargsC.symm ▸ hderC) hdrelC, ndC, t_c, rfl, hderC, huniqC⟩
          | true =>
            have hpr' := sm_ite_false hpr (by rw [hem]; rfl)
            simp only [hem, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
            obtain ⟨ndL, stL, hlRun, hpL⟩ := sm_bind_ok hpr'
            obtain ⟨rfl, hstL⟩ := sm_pure_ok hpL; subst stL
            have ⟨hiL, hmL, haL, _, hfwL, hfiL, hfarL, hntL, hargsL, hspL, hstL, _, hlrel⟩ :=
              S.leafNode_spec stamp m h cur stP hstmp hbP.memo.inv ndL stP' hlRun
            exact ⟨hbP.of_alpha_eq hiL hmL haL hfwL hfiL hfarL,
              .kidLeaf hem hntL (.lex hntL hargsL hspL hstL hlrel), ndL, rfl⟩
        have hafterCond : ∀ (ok0 cr : Bool) (stB : St T),
            S.BuildInv stB →
            (ok0 = true ↔ if !(altsOf A.cx A.g m).isEmpty then S.SpanOfAllow (S.CommitAllow true) m ps' h cur else S.Leaf m h cur) →
            ((ok0 && A.keep s.rule.lhs m cur && cr) = true ↔
              (ok0 = true ∧ A.keep s.rule.lhs m cur = true ∧ S.CondOpt next h cur)) →
            (if (ok0 && A.keep s.rule.lhs m cur && cr) = true then do
               let hit? ← pure (some mkP)
               do let rest ← splits A (finalEnds A size D) child s k ps (.nt m args) next cur ex hs
                  pure (match hit? with | some mkPiece => (h, mkPiece) :: rest | none => rest)
             else do
               let hit? ← pure none
               do let rest ← splits A (finalEnds A size D) child s k ps (.nt m args) next cur ex hs
                  pure (match hit? with | some mkPiece => (h, mkPiece) :: rest | none => rest)).run stB =
              .ok (present, st') →
            S.BuildInv st' ∧
            (∀ p ∈ present, p.1 ∈ h :: hs ∧
              S.ItemMatch (S.SpanOfAllow (S.CommitAllow true)) s k ps (itemOfSplit (.nt m args) o ex) next p.1 cur ∧
              S.MkPieceSpec stamp ps (.nt m args) p.1 cur p.2) ∧
            (∀ h' ∈ h :: hs,
              S.ItemMatch (S.SpanOfAllow (S.CommitAllow true)) s k ps (itemOfSplit (.nt m args) o ex) next h' cur →
              ∃ mkp, (h', mkp) ∈ present) := by
          intro ok0 cr stB hbB hok0Iff hfullIff hrB
          cases hokFull : (ok0 && A.keep s.rule.lhs m cur && cr) with
          | true =>
            have hrB' := sm_ite_true hrB hokFull
            obtain ⟨hit?, st2, hpHit, hr2⟩ := sm_bind_ok hrB'
            obtain ⟨rfl, hst2⟩ := sm_pure_ok hpHit; subst st2
            obtain ⟨hok0T, hkeepT, hcoT⟩ := hfullIff.mp hokFull
            have hspanOrLeaf := hok0Iff.mp hok0T
            refine hfinish (some mkP) stB hbB ⟨?_, hmkP⟩ hr2
            cases ex with
            | none => exact ⟨hkeepT, hcoT, hspanOrLeaf⟩
            | some _ => exact ⟨hkeepT, hnotEx, hspanOrLeaf⟩
          | false =>
            have hrB' := sm_ite_false hrB hokFull
            obtain ⟨hit?, st2, hpHit, hr2⟩ := sm_bind_ok hrB'
            obtain ⟨rfl, hst2⟩ := sm_pure_ok hpHit; subst st2
            refine hfinish none stB hbB (fun hm => ?_) hr2
            apply Bool.false_ne_true (hokFull.symm.trans (hfullIff.mpr ?_))
            cases ex with
            | none =>
              obtain ⟨hkT, hcT, hrT⟩ := hm
              exact ⟨hok0Iff.mpr hrT, hkT, hcT⟩
            | some _ =>
              obtain ⟨hkT, _, hrT⟩ := hm
              exact ⟨hok0Iff.mpr hrT, hkT, hexWf.2 ▸ trivial⟩
        have hafterOk : ∀ (ok0 : Bool) (stA : St T),
            S.BuildInv stA →
            (ok0 = true ↔ if !(altsOf A.cx A.g m).isEmpty then S.SpanOfAllow (S.CommitAllow true) m ps' h cur else S.Leaf m h cur) →
            (have __do_jp2 := fun (cr : Bool) =>
               have ok := ok0 && A.keep s.rule.lhs m cur && cr
               if ok = true then do
                 let hit? ← pure (some mkP)
                 do let rest ← splits A (finalEnds A size D) child s k ps (.nt m args) next cur ex hs
                    pure (match hit? with | some mkPiece => (h, mkPiece) :: rest | none => rest)
               else do
                 let hit? ← pure none
                 do let rest ← splits A (finalEnds A size D) child s k ps (.nt m args) next cur ex hs
                    pure (match hit? with | some mkPiece => (h, mkPiece) :: rest | none => rest)
             match next with
             | some (.onlyIf c) =>
               if ok0 = true then do let cr ← A.cond c h cur; __do_jp2 cr
               else do let cr ← pure true; __do_jp2 cr
             | _ => do let cr ← pure true; __do_jp2 cr).run stA = .ok (present, st') →
            S.BuildInv st' ∧
            (∀ p ∈ present, p.1 ∈ h :: hs ∧
              S.ItemMatch (S.SpanOfAllow (S.CommitAllow true)) s k ps (itemOfSplit (.nt m args) o ex) next p.1 cur ∧
              S.MkPieceSpec stamp ps (.nt m args) p.1 cur p.2) ∧
            (∀ h' ∈ h :: hs,
              S.ItemMatch (S.SpanOfAllow (S.CommitAllow true)) s k ps (itemOfSplit (.nt m args) o ex) next h' cur →
              ∃ mkp, (h', mkp) ∈ present) := by
          intro ok0 stA hbA hok0Iff hrA
          cases next with
          | none =>
            dsimp only at hrA
            obtain ⟨cr, stB, hcr, hrB⟩ := sm_bind_ok hrA
            obtain ⟨rfl, hstB⟩ := sm_pure_ok hcr; subst stB
            exact hafterCond ok0 true stA hbA hok0Iff
              (by simp only [CondOpt, Bool.and_true, Bool.and_eq_true, and_true]) hrB
          | some nx =>
            cases nx with
            | onlyIf cd =>
              dsimp only at hrA
              cases ok0 with
              | false =>
                have hrA' := sm_ite_false hrA rfl
                obtain ⟨cr, stB, hcr, hrB⟩ := sm_bind_ok hrA'
                obtain ⟨rfl, hstB⟩ := sm_pure_ok hcr; subst stB
                exact hafterCond false true stA hbA hok0Iff
                  (by simp only [Bool.false_and, Bool.false_eq_true, false_and]) hrB
              | true =>
                have hrA' := sm_ite_true hrA rfl
                obtain ⟨cr, stB, hcr, hrB⟩ := sm_bind_ok hrA'
                have ⟨hiC, hmC, haC, _, hfwC, hfiC, hfarC, hcIff⟩ :=
                  S.cond_spec cd h cur stA hbA.memo.inv cr stB hcr
                exact hafterCond true cr stB (hbA.of_alpha_eq hiC hmC haC hfwC hfiC hfarC) hok0Iff
                  (by simp only [CondOpt, Bool.true_and, Bool.and_eq_true, true_and, hcIff]) hrB
            | sym _ _ | lookahead _ | noLT | empty | butNot _ _ | phrase _ =>
              dsimp only at hrA
              obtain ⟨cr, stB, hcr, hrB⟩ := sm_bind_ok hrA
              obtain ⟨rfl, hstB⟩ := sm_pure_ok hcr; subst stB
              exact hafterCond ok0 true stA hbA hok0Iff
                (by simp only [CondOpt, Bool.and_true, Bool.and_eq_true, and_true]) hrB
        cases hem : (altsOf A.cx A.g m).isEmpty with
        | false =>
          have hr1'' := sm_ite_true hr1' (by rw [hem]; rfl)
          obtain ⟨esM, stF, hfeRun, hpF⟩ := sm_bind_ok hr1''
          obtain ⟨ok0, stA, hpOk, hrA⟩ := sm_bind_ok hpF
          obtain ⟨rfl, hstA⟩ := sm_pure_ok hpOk; subst stA
          have ⟨hiF, hnaF, hfwF, hesIff⟩ :=
            S.finalEndsAt_spec hok hg true D m ps' h st1 esM stF hb1.memo hb1.no_active hfeRun
          exact hafterOk _ stF (hb1.of_memo_eq_fwd hiF hnaF hfwF)
            (by simp only [hem, Bool.not_false, ↓reduceIte]; exact hesIff cur) hrA
        | true =>
          have hr1'' := sm_ite_false hr1' (by rw [hem]; rfl)
          obtain ⟨lo0, stL, hlfRun, hpL⟩ := sm_bind_ok hr1''
          obtain ⟨ok0, stA, hpOk, hrA⟩ := sm_bind_ok hpL
          obtain ⟨rfl, hstA⟩ := sm_pure_ok hpOk; subst stA
          have ⟨hiL, hmL, haL, _, hfwL, hfiL, hfarL, hlo⟩ := S.leaf_spec m h st1 hb1.memo.inv lo0 stL hlfRun
          refine hafterOk _ stL (hb1.of_alpha_eq hiL hmL haL hfwL hfiL hfarL) ?_ hrA
          simp only [hem, Bool.not_true, Bool.false_eq_true, ↓reduceIte, beq_iff_eq]
          rcases hlo with ⟨j0, rfl, hlj0⟩ | ⟨rfl, hno⟩
          · simp only [Option.some.injEq]
            exact ⟨fun he => he ▸ hlj0, fun hlc => S.leaf_det m h j0 cur hlj0 hlc⟩
          · simp only [reduceCtorEq, false_iff]; exact hno cur

theorem phraseSplits_spec (p : Ecma.Grammar.Phrase) (cur : Nat) :
    ∀ (cands : List Nat) (st : St T) (hs : List Nat) (st' : St T),
      S.BuildInv st →
      (phraseSplits A p cur cands).run st = .ok (hs, st') →
      S.BuildInv st' ∧
      (∀ h, h ∈ hs ↔ (h ∈ cands ∧ S.Phrase p h cur)) := by
  intro cands
  induction cands with
  | nil =>
    intro st hs st' hb hrun
    dsimp only [phraseSplits] at hrun
    obtain ⟨rfl, rfl⟩ := sm_pure_ok hrun
    exact ⟨hb, fun _ => by simp⟩
  | cons h restCands ih =>
    intro st hs st' hb hrun
    dsimp only [phraseSplits] at hrun
    obtain ⟨po, st1, hph, hr1⟩ := sm_bind_ok hrun
    obtain ⟨restHs, st2, hrest, hr2⟩ := sm_bind_ok hr1
    obtain ⟨hhsEq, hst2⟩ := sm_pure_ok hr2; subst hhsEq; subst st2
    have ⟨hi1, hm1, ha1, _, hfw1, hfi1, hfar1, hpo⟩ := S.phrase_spec p h st hb.memo.inv po st1 hph
    have hb1 : S.BuildInv st1 := hb.of_alpha_eq hi1 hm1 ha1 hfw1 hfi1 hfar1
    have ⟨hb2, hrestIff⟩ := ih st1 restHs st' hb1 hrest
    have hhitIff : (po == some cur) = true ↔ S.Phrase p h cur := by
      rw [beq_iff_eq]
      rcases hpo with ⟨j0, rfl, hpj0⟩ | ⟨rfl, hno⟩
      · simp only [Option.some.injEq]
        exact ⟨fun he => he ▸ hpj0, fun hpc => S.phrase_det p h j0 cur hpj0 hpc⟩
      · simp only [reduceCtorEq, false_iff]; exact hno cur
    refine ⟨hb2, fun y => ?_⟩
    cases hhit : po == some cur with
    | true =>
      simp only [↓reduceIte, List.mem_cons, hrestIff]
      have hphT := hhitIff.mp hhit
      constructor
      · rintro (rfl | ⟨hy, hpy⟩)
        · exact ⟨Or.inl rfl, hphT⟩
        · exact ⟨Or.inr hy, hpy⟩
      · rintro ⟨rfl | hy, hpy⟩
        · exact Or.inl rfl
        · exact Or.inr ⟨hy, hpy⟩
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte, List.mem_cons, hrestIff]
      constructor
      · rintro ⟨hy, hpy⟩; exact ⟨Or.inr hy, hpy⟩
      · rintro ⟨rfl | hy, hpy⟩
        · exact absurd (hhitIff.mpr hpy) (by simp [hhit])
        · exact ⟨hy, hpy⟩

def candsOf (provs : Option (List (Std.HashMap Nat (List Nat)))) (before : Ends) (c0 : Nat) : List Nat :=
  match provs with
  | some (pm :: _) => pm.getD c0 []
  | _ => before.toList

def ProvsStepSpec (provs restProvs : Option (List (Std.HashMap Nat (List Nat)))) : Prop :=
  match provs with
  | none => restProvs = none
  | some (_ :: ps') => restProvs = some ps'
  | some [] => False

theorem sm_uncons_provs_ex {T α : Type}
    (provs : Option (List (Std.HashMap Nat (List Nat))))
    (jp : Option (List (Std.HashMap Nat (List Nat))) → SM T α)
    {st : St T} {v : α} {st' : St T}
    (h : (match provs with
          | none => do let r ← pure none; jp r
          | some (_ :: ps') => do let r ← pure (some ps'); jp r
          | some [] => do let r ← (throw (Stop.check "missing provenance set") : SM T _); jp r).run st = .ok (v, st')) :
    ∃ restProvs, ProvsStepSpec provs restProvs ∧ (jp restProvs).run st = .ok (v, st') := by
  cases provs with
  | none =>
    dsimp only at h
    obtain ⟨rp, st0, hp, hr⟩ := sm_bind_ok h
    obtain ⟨rfl, hst0⟩ := sm_pure_ok hp; subst st0
    exact ⟨none, rfl, hr⟩
  | some pms =>
    cases pms with
    | nil =>
      dsimp only at h
      obtain ⟨_, _, ht, _⟩ := sm_bind_ok h; cases ht
    | cons pm ps' =>
      dsimp only at h
      obtain ⟨rp, st0, hp, hr⟩ := sm_bind_ok h
      obtain ⟨rfl, hst0⟩ := sm_pure_ok hp; subst st0
      exact ⟨some ps', rfl, hr⟩

theorem buildRhs_sym (hok : parseTablesOk = true) (hg : A.g = .syntactic ∨ A.g ∈ codeGrammars)
    (D stamp : Nat) {child : NT → List Param → Nat → Nat → SM T N} (hchild : S.ChildSpec stamp child)
    (n : NT) (e : Src) (ps : List Param) (j k : Nat)
    (x : Sym) (o : Bool) (rest : List Item) (P before : Ends)
    (cands : List Nat) (cur1 : Nat) (pieces1 : List (Piece N)) (mask1 : List Bool) (ts1 : List DTree)
    (st1 : St T) (cur : Nat) (pieces : List (Piece N)) (mask : List Bool) (st' : St T)
    (hb1 : S.BuildInv st1)
    (hbefore : ∀ z, before.mem z = P.mem z)
    (candsSound : ∀ h ∈ cands, before.mem h = true)
    (candsComp : ∀ h, before.mem h = true →
      S.ItemStep (S.SpanOfAllow (S.CommitAllow true)) e k ps (.sym x o) rest.head? h cur1 → h ∈ cands)
    (hpcs1 : ∀ pc ∈ pieces1, S.PieceValid (S.CommitAllow true) stamp pc)
    (hsw1 : S.SeqWith (S.CommitAllow true) e ps (k + 1) rest cur1 j mask1 ts1)
    (hmidEq : ∀ (h0 mid : Nat) (m_r : List Bool) (ts_r : List DTree),
      P.mem h0 = true →
      S.ItemStep (S.SpanOfAllow (S.CommitAllow true)) e k ps (.sym x o) rest.head? h0 mid →
      S.SeqWith (S.CommitAllow true) e ps (k + 1) rest mid j m_r ts_r →
      mid = cur1 ∧ m_r = mask1 ∧ ts_r = ts1)
    (hr2 : (do
              let absent := o && before.mem cur1
              let present ← splits A (finalEnds A size D) child e k ps x rest.head? cur1 none cands
              if (if absent then 1 else 0) + present.length > 1 then
                throw (Stop.ambiguous s!"{n.name}: two parses of an item")
              if absent then
                return (cur1, Piece.absent :: pieces1, false :: mask1)
              else
                let some (h, mkPiece) := present.head? | throw (Stop.check "no split for a symbol")
                let pc ← mkPiece
                return (h, pc :: pieces1, if o then true :: mask1 else mask1)).run st1 = .ok ((cur, pieces, mask), st'))
    (hstmp : S.LeafStamp.all (· == stamp) = true := by rfl) :
    S.BuildInv st' ∧
    P.mem cur = true ∧
    (∀ pc ∈ pieces, S.PieceValid (S.CommitAllow true) stamp pc) ∧
    ∃ ts,
      S.SeqWith (S.CommitAllow true) e ps k (.sym x o :: rest) cur j mask ts ∧
      (∀ h0 m0 ts0, P.mem h0 = true → S.SeqWith (S.CommitAllow true) e ps k (.sym x o :: rest) h0 j m0 ts0 →
        h0 = cur ∧ m0 = mask ∧ ts0 = ts) := by
  obtain ⟨present, st2, hspRun, hr3⟩ := sm_bind_ok hr2
  have ⟨hb2, hpresSound, hpresComp⟩ :=
    S.splits_spec hok hg D stamp hchild e k ps x o rest.head? cur1 none trivial hstmp cands st1 present st2 hb1 hspRun
  obtain ⟨hnotGt1, hr4⟩ :=
    sm_ite_throw_jp hr3
  have hlenBound : (if (o && before.mem cur1) = true then 1 else 0) + present.length ≤ 1 := Nat.le_of_not_gt hnotGt1
  cases habs : (o && before.mem cur1) with
  | true =>
    simp only [habs, ↓reduceIte] at hr4 hlenBound
    obtain ⟨hpEq, hst2⟩ := sm_pure_ok hr4; subst st2
    obtain ⟨hcurEq, hpEq2⟩ := Prod.mk.inj hpEq.symm; subst cur
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj hpEq2
    have hpresNil : present = [] := by cases present with | nil => rfl | cons _ _ => simp only [List.length_cons] at hlenBound; omega
    simp only [Bool.and_eq_true] at habs
    obtain ⟨rfl, hbefCur⟩ := habs
    have hPCur : P.mem cur1 = true := (hbefore cur1) ▸ hbefCur
    refine ⟨hb2, hPCur,
      fun pc hpc => (List.mem_cons.mp hpc).elim (fun heq => heq ▸ .absent) (hpcs1 pc),
      ts1, .absent hsw1, fun h0 m0 ts0 hh0 hsw0 => ?_⟩
    have hbef0 : before.mem h0 = true := (hbefore h0).symm ▸ hh0
    cases hsw0 with
    | absent hswR =>
      obtain ⟨rfl, rfl, rfl⟩ := hmidEq h0 _ _ _ hh0 (Or.inl ⟨rfl, rfl⟩) hswR
      exact ⟨rfl, rfl, rfl⟩
    | term ht hswR =>
      obtain ⟨rfl, _, _⟩ := hmidEq h0 _ _ _ hh0 (Or.inr ht) hswR
      obtain ⟨mkp, hmp⟩ := hpresComp h0 (candsComp h0 hbef0 (Or.inr ht)) ht
      rw [hpresNil] at hmp; cases hmp
    | @nt _ _ _ m0 a0 _ _ _ mid0 _ _ _ _ hne hd hk hch hswR =>
      have hm0 : S.ItemMatch (S.SpanOfAllow (S.CommitAllow true)) e k ps (.sym (.nt m0 a0) true) rest.head? h0 mid0 :=
        ⟨hk, (S.condOpt_head rest h0 mid0).mpr hch, by simp only [hne, Bool.not_false, ↓reduceIte]; exact ⟨_, hd⟩⟩
      obtain ⟨rfl, _, _⟩ := hmidEq h0 _ _ _ hh0 (Or.inr hm0) hswR
      obtain ⟨mkp, hmp⟩ := hpresComp h0 (candsComp h0 hbef0 (Or.inr hm0)) hm0
      rw [hpresNil] at hmp; cases hmp
    | @leaf _ _ _ m0 a0 _ _ _ mid0 _ _ _ hem hl hk hch hswR =>
      have hm0 : S.ItemMatch (S.SpanOfAllow (S.CommitAllow true)) e k ps (.sym (.nt m0 a0) true) rest.head? h0 mid0 :=
        ⟨hk, (S.condOpt_head rest h0 mid0).mpr hch, by simp only [hem, Bool.not_true, Bool.false_eq_true, ↓reduceIte]; exact hl⟩
      obtain ⟨rfl, _, _⟩ := hmidEq h0 _ _ _ hh0 (Or.inr hm0) hswR
      obtain ⟨mkp, hmp⟩ := hpresComp h0 (candsComp h0 hbef0 (Or.inr hm0)) hm0
      rw [hpresNil] at hmp; cases hmp
  | false =>
    simp only [habs, Bool.false_eq_true, ↓reduceIte, Nat.zero_add] at hr4 hlenBound
    cases hprList : present with
    | nil =>
      rw [hprList] at hr4; dsimp only [List.head?] at hr4; rw [sm_run_throw] at hr4; cases hr4
    | cons hd tl =>
      have htlNil : tl = [] := by
        rw [hprList] at hlenBound
        cases tl with | nil => rfl | cons _ _ => simp only [List.length_cons] at hlenBound; omega
      subst htlNil
      rcases hd with ⟨h, mkPiece⟩
      rw [hprList] at hr4; dsimp only [List.head?] at hr4
      obtain ⟨pc, st3, hmkRun, hr5⟩ := sm_bind_ok hr4
      obtain ⟨hpEq, hst3⟩ := sm_pure_ok hr5; subst st3
      obtain ⟨hcurEq, hpEq2⟩ := Prod.mk.inj hpEq.symm; subst cur
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj hpEq2
      obtain ⟨hhCands, hmH, hmkSpec⟩ := hpresSound (h, mkPiece) (hprList ▸ List.mem_cons_self ..)
      have hPh : P.mem h = true := (hbefore h) ▸ (candsSound h hhCands)
      have ⟨hb3, hpcV, hpcKind⟩ := hmkSpec st2 pc st' hb2 hmkRun
      have hpcsAll : ∀ p ∈ pc :: pieces1, S.PieceValid (S.CommitAllow true) stamp p :=
        fun p hp => (List.mem_cons.mp hp).elim (fun heq => heq ▸ hpcV) (hpcs1 p)
      have huniqH : ∀ h0, P.mem h0 = true →
          S.ItemMatch (S.SpanOfAllow (S.CommitAllow true)) e k ps (.sym x o) rest.head? h0 cur1 →
          h0 = h := by
        intro h0 hh0 hm0
        have hbef0 : before.mem h0 = true := (hbefore h0).symm ▸ hh0
        obtain ⟨mk0, hmp0⟩ := hpresComp h0 (candsComp h0 hbef0 (Or.inr hm0)) hm0
        rw [hprList, List.mem_singleton] at hmp0
        exact (Prod.mk.inj hmp0).1
      cases x with
      | t tm =>
        refine ⟨hb3, hPh, hpcsAll, .leaf h cur1 :: ts1, .term hmH hsw1, fun h0 m0 ts0 hh0 hsw0 => ?_⟩
        cases hsw0 with
        | absent hswR =>
          obtain ⟨rfl, _, _⟩ := hmidEq h0 _ _ _ hh0 (Or.inl ⟨rfl, rfl⟩) hswR
          have hbef0 : before.mem h0 = true := (hbefore h0).symm ▸ hh0
          simp only [hbef0, Bool.and_true] at habs; cases habs
        | term ht hswR =>
          obtain ⟨rfl, rfl, rfl⟩ := hmidEq h0 _ _ _ hh0 (Or.inr ht) hswR
          obtain rfl := huniqH h0 hh0 ht
          exact ⟨rfl, rfl, rfl⟩
      | nt m args =>
        obtain ⟨hkH, hcH, hrH⟩ := hmH
        have hchH := (S.condOpt_head rest h cur1).mp hcH
        cases hem : (altsOf A.cx A.g m).isEmpty with
        | false =>
          simp only [hem, Bool.not_false, ↓reduceIte] at hpcKind hrH
          obtain ⟨cNd, t_c, _, hderC, huniqC⟩ := hpcKind
          refine ⟨hb3, hPh, hpcsAll, t_c :: ts1, .nt hem hderC hkH hchH hsw1, fun h0 m0 ts0 hh0 hsw0 => ?_⟩
          cases hsw0 with
          | absent hswR =>
            obtain ⟨rfl, _, _⟩ := hmidEq h0 _ _ _ hh0 (Or.inl ⟨rfl, rfl⟩) hswR
            have hbef0 : before.mem h0 = true := (hbefore h0).symm ▸ hh0
            simp only [hbef0, Bool.and_true] at habs; cases habs
          | nt _ hd0 hk0 hch0 hswR =>
            have hm0 : S.ItemMatch (S.SpanOfAllow (S.CommitAllow true)) e k ps (.sym (.nt m args) o) rest.head? h0 _ :=
              ⟨hk0, (S.condOpt_head rest h0 _).mpr hch0, by simp only [hem, Bool.not_false, ↓reduceIte]; exact ⟨_, hd0⟩⟩
            obtain ⟨rfl, rfl, rfl⟩ := hmidEq h0 _ _ _ hh0 (Or.inr hm0) hswR
            obtain rfl := huniqH h0 hh0 hm0
            obtain rfl := huniqC _ hd0
            exact ⟨rfl, rfl, rfl⟩
          | leaf hem0 _ _ _ _ => rw [hem] at hem0; cases hem0
        | true =>
          simp only [hem, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hrH
          refine ⟨hb3, hPh, hpcsAll, .lex m h cur1 :: ts1, .leaf hem hrH hkH hchH hsw1, fun h0 m0 ts0 hh0 hsw0 => ?_⟩
          cases hsw0 with
          | absent hswR =>
            obtain ⟨rfl, _, _⟩ := hmidEq h0 _ _ _ hh0 (Or.inl ⟨rfl, rfl⟩) hswR
            have hbef0 : before.mem h0 = true := (hbefore h0).symm ▸ hh0
            simp only [hbef0, Bool.and_true] at habs; cases habs
          | nt hne0 _ _ _ _ => rw [hem] at hne0; cases hne0
          | leaf _ hl0 hk0 hch0 hswR =>
            have hm0 : S.ItemMatch (S.SpanOfAllow (S.CommitAllow true)) e k ps (.sym (.nt m args) o) rest.head? h0 _ :=
              ⟨hk0, (S.condOpt_head rest h0 _).mpr hch0, by simp only [hem, Bool.not_true, Bool.false_eq_true, ↓reduceIte]; exact hl0⟩
            obtain ⟨rfl, rfl, rfl⟩ := hmidEq h0 _ _ _ hh0 (Or.inr hm0) hswR
            obtain rfl := huniqH h0 hh0 hm0
            exact ⟨rfl, rfl, rfl⟩

theorem buildRhs_butNot (hok : parseTablesOk = true) (hg : A.g = .syntactic ∨ A.g ∈ codeGrammars)
    (D stamp : Nat) {child : NT → List Param → Nat → Nat → SM T N} (hchild : S.ChildSpec stamp child)
    (n : NT) (e : Src) (ps : List Param) (j k : Nat)
    (base : Sym) (ex : Exclusion) (rest : List Item) (P before : Ends)
    (cands : List Nat) (cur1 : Nat) (pieces1 : List (Piece N)) (mask1 : List Bool) (ts1 : List DTree)
    (st1 : St T) (cur : Nat) (pieces : List (Piece N)) (mask : List Bool) (st' : St T)
    (hb1 : S.BuildInv st1)
    (hexWf : ExclWF A ex)
    (hbefore : ∀ z, before.mem z = P.mem z)
    (candsSound : ∀ h ∈ cands, before.mem h = true)
    (candsComp : ∀ h, before.mem h = true →
      S.ItemStep (S.SpanOfAllow (S.CommitAllow true)) e k ps (.butNot base ex) rest.head? h cur1 → h ∈ cands)
    (hpcs1 : ∀ pc ∈ pieces1, S.PieceValid (S.CommitAllow true) stamp pc)
    (hsw1 : S.SeqWith (S.CommitAllow true) e ps (k + 1) rest cur1 j mask1 ts1)
    (hmidEq : ∀ (h0 mid : Nat) (m_r : List Bool) (ts_r : List DTree),
      P.mem h0 = true →
      S.ItemStep (S.SpanOfAllow (S.CommitAllow true)) e k ps (.butNot base ex) rest.head? h0 mid →
      S.SeqWith (S.CommitAllow true) e ps (k + 1) rest mid j m_r ts_r →
      mid = cur1 ∧ m_r = mask1 ∧ ts_r = ts1)
    (hr2 : (do
              let present ← splits A (finalEnds A size D) child e k ps base none cur1 (some ex) cands
              if present.length > 1 then throw (Stop.ambiguous s!"{n.name}: two parses of an item")
              let some (h, mkPiece) := present.head? | throw (Stop.check "no split for a but-not item")
              let pc ← mkPiece
              return (h, pc :: pieces1, mask1)).run st1 = .ok ((cur, pieces, mask), st'))
    (hstmp : S.LeafStamp.all (· == stamp) = true := by rfl) :
    S.BuildInv st' ∧
    P.mem cur = true ∧
    (∀ pc ∈ pieces, S.PieceValid (S.CommitAllow true) stamp pc) ∧
    ∃ ts,
      S.SeqWith (S.CommitAllow true) e ps k (.butNot base ex :: rest) cur j mask ts ∧
      (∀ h0 m0 ts0, P.mem h0 = true → S.SeqWith (S.CommitAllow true) e ps k (.butNot base ex :: rest) h0 j m0 ts0 →
        h0 = cur ∧ m0 = mask ∧ ts0 = ts) := by
  obtain ⟨present, st2, hspRun, hr3⟩ := sm_bind_ok hr2
  have ⟨hb2, hpresSound, hpresComp⟩ :=
    S.splits_spec hok hg D stamp hchild e k ps base false none cur1 (some ex)
      ⟨hexWf, rfl⟩ hstmp cands st1 present st2 hb1 hspRun
  obtain ⟨hnotGt1, hr4⟩ := sm_ite_throw_jp hr3
  have hlenBound : present.length ≤ 1 := Nat.le_of_not_gt hnotGt1
  cases hprList : present with
  | nil =>
    rw [hprList] at hr4; dsimp only [List.head?] at hr4; rw [sm_run_throw] at hr4; cases hr4
  | cons hd tl =>
    have htlNil : tl = [] := by
      rw [hprList] at hlenBound
      cases tl with | nil => rfl | cons _ _ => simp only [List.length_cons] at hlenBound; omega
    subst htlNil
    rcases hd with ⟨h, mkPiece⟩
    rw [hprList] at hr4; dsimp only [List.head?] at hr4
    obtain ⟨pc, st3, hmkRun, hr5⟩ := sm_bind_ok hr4
    obtain ⟨hpEq, hst3⟩ := sm_pure_ok hr5; subst st3
    obtain ⟨hcurEq, hpEq2⟩ := Prod.mk.inj hpEq.symm; subst cur
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj hpEq2
    obtain ⟨hhCands, hmH, hmkSpec⟩ := hpresSound (h, mkPiece) (hprList ▸ List.mem_cons_self ..)
    have hPh : P.mem h = true := (hbefore h) ▸ (candsSound h hhCands)
    have ⟨hb3, hpcV, hpcKind⟩ := hmkSpec st2 pc st' hb2 hmkRun
    have hpcsAll : ∀ p ∈ pc :: pieces1, S.PieceValid (S.CommitAllow true) stamp p :=
      fun p hp => (List.mem_cons.mp hp).elim (fun heq => heq ▸ hpcV) (hpcs1 p)
    have huniqH : ∀ h0, P.mem h0 = true →
        S.ItemMatch (S.SpanOfAllow (S.CommitAllow true)) e k ps (.butNot base ex) none h0 cur1 →
        h0 = h := by
      intro h0 hh0 hm0
      have hbef0 : before.mem h0 = true := (hbefore h0).symm ▸ hh0
      have hs0 : S.ItemStep (S.SpanOfAllow (S.CommitAllow true)) e k ps (.butNot base ex) rest.head? h0 cur1 := by
        cases base <;> exact hm0
      obtain ⟨mk0, hmp0⟩ := hpresComp h0 (candsComp h0 hbef0 hs0) hm0
      rw [hprList, List.mem_singleton] at hmp0
      exact (Prod.mk.inj hmp0).1
    cases base with
    | t tm =>
      refine ⟨hb3, hPh, hpcsAll, .leaf h cur1 :: ts1, .butNotT hmH.1 hmH.2 hsw1, fun h0 m0 ts0 hh0 hsw0 => ?_⟩
      cases hsw0 with
      | butNotT ht hex hswR =>
        obtain ⟨rfl, rfl, rfl⟩ := hmidEq h0 _ _ _ hh0 ⟨ht, hex⟩ hswR
        obtain rfl := huniqH h0 hh0 ⟨ht, hex⟩
        exact ⟨rfl, rfl, rfl⟩
    | nt m args =>
      obtain ⟨hkH, hexH, hrH⟩ := hmH
      cases hem : (altsOf A.cx A.g m).isEmpty with
      | false =>
        simp only [hem, Bool.not_false, ↓reduceIte] at hpcKind hrH
        obtain ⟨cNd, t_c, _, hderC, huniqC⟩ := hpcKind
        refine ⟨hb3, hPh, hpcsAll, t_c :: ts1, .butNotN hem hderC hkH hexH hsw1, fun h0 m0 ts0 hh0 hsw0 => ?_⟩
        cases hsw0 with
        | butNotN _ hd0 hk0 hex0 hswR =>
          have hm0 : S.ItemMatch (S.SpanOfAllow (S.CommitAllow true)) e k ps (.butNot (.nt m args) ex) none h0 _ :=
            ⟨hk0, hex0, by simp only [hem, Bool.not_false, ↓reduceIte]; exact ⟨_, hd0⟩⟩
          obtain ⟨rfl, rfl, rfl⟩ := hmidEq h0 _ _ _ hh0 hm0 hswR
          obtain rfl := huniqH h0 hh0 hm0
          obtain rfl := huniqC _ hd0
          exact ⟨rfl, rfl, rfl⟩
        | butNotLeaf hem0 _ _ _ _ => rw [hem] at hem0; cases hem0
      | true =>
        simp only [hem, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hrH
        refine ⟨hb3, hPh, hpcsAll, .lex m h cur1 :: ts1, .butNotLeaf hem hrH hkH hexH hsw1, fun h0 m0 ts0 hh0 hsw0 => ?_⟩
        cases hsw0 with
        | butNotN hne0 _ _ _ _ => rw [hem] at hne0; cases hne0
        | butNotLeaf _ hl0 hk0 hex0 hswR =>
          have hm0 : S.ItemMatch (S.SpanOfAllow (S.CommitAllow true)) e k ps (.butNot (.nt m args) ex) none h0 _ :=
            ⟨hk0, hex0, by simp only [hem, Bool.not_true, Bool.false_eq_true, ↓reduceIte]; exact hl0⟩
          obtain ⟨rfl, rfl, rfl⟩ := hmidEq h0 _ _ _ hh0 hm0 hswR
          obtain rfl := huniqH h0 hh0 hm0
          exact ⟨rfl, rfl, rfl⟩

theorem buildRhs_spec (hok : parseTablesOk = true) (hg : A.g = .syntactic ∨ A.g ∈ codeGrammars)
    (D stamp : Nat) {child : NT → List Param → Nat → Nat → SM T N} (hchild : S.ChildSpec stamp child)
    (n : NT) (e : Src) (ps : List Param) (j : Nat)
    (hstmp : S.LeafStamp.all (· == stamp) = true := by rfl) :
    ∀ (k : Nat) (is : List Item) (P : Ends) (sets : List Ends) (last : Ends)
      (provs : Option (List (Std.HashMap Nat (List Nat))))
      (st : St T) (cur : Nat) (pieces : List (Piece N)) (mask : List Bool) (st' : St T),
      S.BuildInv st →
      (∀ it ∈ is, ItemWF A it) →
      S.FwdSetsValid (S.SpanOfAllow (S.CommitAllow true)) e ps k is P sets last →
      S.OptProvValid (S.SpanOfAllow (S.CommitAllow true)) e ps k is sets provs →
      last.mem j = true →
      (buildRhs A (finalEnds A size D) child n e ps j k is sets provs).run st = .ok ((cur, pieces, mask), st') →
      S.BuildInv st' ∧
      P.mem cur = true ∧
      (∀ pc ∈ pieces, S.PieceValid (S.CommitAllow true) stamp pc) ∧
      ∃ ts,
        S.SeqWith (S.CommitAllow true) e ps k is cur j mask ts ∧
        (∀ h0 m0 ts0, P.mem h0 = true → S.SeqWith (S.CommitAllow true) e ps k is h0 j m0 ts0 →
          h0 = cur ∧ m0 = mask ∧ ts0 = ts) := by
  intro k is
  induction is generalizing k with
  | nil =>
    intro P sets last provs st cur pieces mask st' hb _ hfsv _ hlastJ hrun
    dsimp only [buildRhs] at hrun
    obtain ⟨hpEq, hst⟩ := sm_pure_ok hrun; subst st'
    obtain ⟨hcurEq, hpEq2⟩ := Prod.mk.inj hpEq.symm; subst cur
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj hpEq2
    cases hfsv with
    | nil heq =>
      refine ⟨hb, (heq _) ▸ hlastJ, (fun _ hp => nomatch hp), [], .nil, fun h0 m0 ts0 _ hsw0 => ?_⟩
      cases hsw0; exact ⟨rfl, rfl, rfl⟩
  | cons it rest ih =>
    intro P sets last provs st cur pieces mask st' hb hwf hfsv hopv hlastJ hrun
    cases sets with
    | nil => cases hfsv
    | cons before restSets =>
      cases hfsv with
      | cons P' hbefore hP' hfsvRest =>
        dsimp only [buildRhs] at hrun
        obtain ⟨restProvs, hpspec, hr1⟩ := sm_uncons_provs_ex provs _ hrun
        have ⟨hopvRest, hcandsSpec⟩ :
            S.OptProvValid (S.SpanOfAllow (S.CommitAllow true)) e ps (k + 1) rest restSets restProvs ∧
            (itemHasProv it = true →
              ∀ c0 : Nat,
                (∀ h ∈ candsOf provs before c0, before.mem h = true) ∧
                (∀ h, before.mem h = true →
                  S.ItemStep (S.SpanOfAllow (S.CommitAllow true)) e k ps it rest.head? h c0 → h ∈ candsOf provs before c0)) := by
          cases provs with
          | none =>
            dsimp only [ProvsStepSpec] at hpspec; subst hpspec
            exact ⟨trivial, fun _ c0 =>
              ⟨fun h hh => (Ends.mem_toList before h).mp hh,
               fun h hh _ => (Ends.mem_toList before h).mpr hh⟩⟩
          | some pms =>
            cases pms with
            | nil => exact False.elim hpspec
            | cons pm ps' =>
              dsimp only [ProvsStepSpec] at hpspec; subst hpspec
              cases hopv with
              | cons hpm hpms =>
                exact ⟨hpms, fun hkind c0 => hpm hkind c0⟩
        obtain ⟨rTriple, st1, hrecRun, hr2⟩ := sm_bind_ok hr1
        rcases rTriple with ⟨cur1, pieces1, mask1⟩
        have ⟨hb1, hcur1InP', hpcs1, ts1, hsw1, huniq1⟩ :=
          ih (k + 1) P' restSets last restProvs
            st cur1 pieces1 mask1 st1 hb (fun it' h => hwf it' (List.mem_cons_of_mem _ h))
            hfsvRest hopvRest hlastJ hrecRun
        have hmidEq : ∀ (h0 mid : Nat) (m_r : List Bool) (ts_r : List DTree),
            P.mem h0 = true →
            S.ItemStep (S.SpanOfAllow (S.CommitAllow true)) e k ps it rest.head? h0 mid →
            S.SeqWith (S.CommitAllow true) e ps (k + 1) rest mid j m_r ts_r →
            mid = cur1 ∧ m_r = mask1 ∧ ts_r = ts1 :=
          fun h0 mid m_r ts_r hh0 hs0 hswR => huniq1 mid m_r ts_r ((hP' mid).mpr ⟨h0, hh0, hs0⟩) hswR
        cases it with
        | sym x o =>
          dsimp only at hr2
          obtain ⟨candsSound, candsComp⟩ := hcandsSpec rfl cur1
          exact S.buildRhs_sym hok hg D stamp hchild n e ps j k x o rest P before _
            cur1 pieces1 mask1 ts1 st1 cur pieces mask st' hb1 hbefore candsSound candsComp hpcs1 hsw1 hmidEq hr2 hstmp
        | butNot base ex =>
          dsimp only at hr2
          obtain ⟨candsSound, candsComp⟩ := hcandsSpec rfl cur1
          exact S.buildRhs_butNot hok hg D stamp hchild n e ps j k base ex rest P before _
            cur1 pieces1 mask1 ts1 st1 cur pieces mask st' hb1 (hwf _ (List.mem_cons_self ..))
            hbefore candsSound candsComp hpcs1 hsw1 hmidEq hr2 hstmp
        | phrase p =>
          dsimp only at hr2
          obtain ⟨candsSound, candsComp⟩ := hcandsSpec rfl cur1
          obtain ⟨hs, st2, hphRun, hr3⟩ := sm_bind_ok hr2
          have ⟨hb2, hhsIff⟩ := S.phraseSplits_spec p cur1 _ st1 hs st2 hb1 hphRun
          obtain ⟨hnotGt1, hr4⟩ := sm_ite_throw_jp hr3
          have hlenBound : hs.length ≤ 1 := Nat.le_of_not_gt hnotGt1
          cases hhsList : hs with
          | nil =>
            rw [hhsList] at hr4; dsimp only [List.head?] at hr4; rw [sm_run_throw] at hr4; cases hr4
          | cons h tl =>
            have htlNil : tl = [] := by
              rw [hhsList] at hlenBound
              cases tl with | nil => rfl | cons _ _ => simp only [List.length_cons] at hlenBound; omega
            subst htlNil
            rw [hhsList] at hr4; dsimp only [List.head?] at hr4
            obtain ⟨hpEq, hst2⟩ := sm_pure_ok hr4; subst st2
            obtain ⟨hcurEq, hpEq2⟩ := Prod.mk.inj hpEq.symm; subst cur
            obtain ⟨rfl, rfl⟩ := Prod.mk.inj hpEq2
            obtain ⟨hhCands, hphH⟩ := (hhsIff h).mp (hhsList ▸ List.mem_cons_self ..)
            have hPh : P.mem h = true := (hbefore h) ▸ (candsSound h hhCands)
            refine ⟨hb2, hPh,
              fun pc hpc => (List.mem_cons.mp hpc).elim (fun heq => heq ▸ .span h cur1) (hpcs1 pc),
              .leaf h cur1 :: ts1, .phrase hphH hsw1, fun h0 m0 ts0 hh0 hsw0 => ?_⟩
            cases hsw0 with
            | phrase hph0 hswR =>
              obtain ⟨rfl, rfl, rfl⟩ := hmidEq h0 _ _ _ hh0 hph0 hswR
              have hbef0 : before.mem h0 = true := (hbefore h0).symm ▸ hh0
              have hh0InHs : h0 ∈ hs := (hhsIff h0).mpr ⟨candsComp h0 hbef0 hph0, hph0⟩
              rw [hhsList, List.mem_singleton] at hh0InHs; subst hh0InHs
              exact ⟨rfl, rfl, rfl⟩
        | lookahead l =>
          dsimp only at hr2
          obtain ⟨hbefCur, hr3⟩ := sm_unless_throw_jp hr2
          obtain ⟨hpEq, hst1⟩ := sm_pure_ok hr3; subst st1
          obtain ⟨hcurEq, hpEq2⟩ := Prod.mk.inj hpEq.symm; subst cur
          obtain ⟨rfl, rfl⟩ := Prod.mk.inj hpEq2
          obtain ⟨h0, hh0, rfl, hlk⟩ := (hP' cur1).mp hcur1InP'
          refine ⟨hb1, hh0,
            fun pc hpc => (List.mem_cons.mp hpc).elim (fun heq => heq ▸ .zero) (hpcs1 pc),
            ts1, .look hlk hsw1, fun h0' m0 ts0 hh0' hsw0 => ?_⟩
          cases hsw0 with
          | look hlk0 hswR =>
            obtain ⟨rfl, rfl, rfl⟩ := hmidEq h0' _ _ _ hh0' ⟨rfl, hlk0⟩ hswR
            exact ⟨rfl, rfl, rfl⟩
        | noLT =>
          dsimp only at hr2
          obtain ⟨hbefCur, hr3⟩ := sm_unless_throw_jp hr2
          obtain ⟨hpEq, hst1⟩ := sm_pure_ok hr3; subst st1
          obtain ⟨hcurEq, hpEq2⟩ := Prod.mk.inj hpEq.symm; subst cur
          obtain ⟨rfl, rfl⟩ := Prod.mk.inj hpEq2
          obtain ⟨h0, hh0, rfl, hnl⟩ := (hP' cur1).mp hcur1InP'
          refine ⟨hb1, hh0,
            fun pc hpc => (List.mem_cons.mp hpc).elim (fun heq => heq ▸ .zero) (hpcs1 pc),
            ts1, .noLT hnl hsw1, fun h0' m0 ts0 hh0' hsw0 => ?_⟩
          cases hsw0 with
          | noLT hnl0 hswR =>
            obtain ⟨rfl, rfl, rfl⟩ := hmidEq h0' _ _ _ hh0' ⟨rfl, hnl0⟩ hswR
            exact ⟨rfl, rfl, rfl⟩
        | empty =>
          dsimp only at hr2
          obtain ⟨hbefCur, hr3⟩ := sm_unless_throw_jp hr2
          obtain ⟨hpEq, hst1⟩ := sm_pure_ok hr3; subst st1
          obtain ⟨hcurEq, hpEq2⟩ := Prod.mk.inj hpEq.symm; subst cur
          obtain ⟨rfl, rfl⟩ := Prod.mk.inj hpEq2
          refine ⟨hb1, (hbefore cur1) ▸ hbefCur,
            fun pc hpc => (List.mem_cons.mp hpc).elim (fun heq => heq ▸ .zero) (hpcs1 pc),
            ts1, .empty hsw1, fun h0' m0 ts0 hh0' hsw0 => ?_⟩
          cases hsw0 with
          | empty hswR =>
            obtain ⟨rfl, rfl, rfl⟩ := hmidEq h0' _ _ _ hh0' rfl hswR
            exact ⟨rfl, rfl, rfl⟩
        | onlyIf cd =>
          dsimp only at hr2
          obtain ⟨hbefCur, hr3⟩ := sm_unless_throw_jp hr2
          obtain ⟨hpEq, hst1⟩ := sm_pure_ok hr3; subst st1
          obtain ⟨hcurEq, hpEq2⟩ := Prod.mk.inj hpEq.symm; subst cur
          obtain ⟨rfl, rfl⟩ := Prod.mk.inj hpEq2
          refine ⟨hb1, (hbefore cur1) ▸ hbefCur,
            fun pc hpc => (List.mem_cons.mp hpc).elim (fun heq => heq ▸ .zero) (hpcs1 pc),
            ts1, .onlyIf hsw1, fun h0' m0 ts0 hh0' hsw0 => ?_⟩
          cases hsw0 with
          | onlyIf hswR =>
            obtain ⟨rfl, rfl, rfl⟩ := hmidEq h0' _ _ _ hh0' rfl hswR
            exact ⟨rfl, rfl, rfl⟩

theorem prodIdOf_mem_unique (hok : parseTablesOk = true) {cx : Ctx} {g : GrammarId}
    {n : NT} {e : Src} {mask : List Bool} {p : Nat}
    (heMem : e ∈ altsOf cx g n)
    (hopts : mask ∈ masks ((e.alt.rhs.filter fun | .sym _ true => true | _ => false).length))
    (hpid : prodIdOf e mask = some p) :
    (∀ P' ef', prodOf p = some P' →
      (altsOf cx g P'.rule.lhs).find? (fun x => x.grammar == P'.grammar && x.idx == P'.alt && x.rule == P'.rule) = some ef' →
      P'.rule.lhs = n ∧ ef' = e) ∧
    (∀ n' ef' mask',
      ef' ∈ altsOf cx g n' →
      mask' ∈ masks ((ef'.alt.rhs.filter fun | .sym _ true => true | _ => false).length) →
      prodIdOf ef' mask' = some p →
      n' = n) := by
  have heSpec : e ∈ Ecma.Spec.gl.alts cx g n := (altsOf_eq hok cx g n) ▸ heMem
  obtain ⟨hlhs, hoptsEq⟩ := alt_lhs_and_opts hok heSpec
  have hmaskMem : mask ∈ masks e.alt.opts := hoptsEq ▸ hopts
  obtain ⟨hpeq, id0, P0, hid0, hpo0, _, hrule0, _, _, hfind0⟩ := prodIdOf_spec hok heSpec hmaskMem
  have hpId : id0 = p := Option.some.inj ((hpeq.trans hid0).symm.trans hpid)
  subst hpId
  refine ⟨fun P' ef' hpo' hfind' => ?_, fun n' ef' mask' hsMk hoptsMk hpidMk => ?_⟩
  · have hPEq : P0 = P' := Option.some.inj (hpo0.symm.trans hpo')
    subst hPEq
    rw [altsOf_eq hok] at hfind'
    exact ⟨(congrArg Rule.lhs hrule0).trans hlhs, Option.some.inj (hfind'.symm.trans hfind0)⟩
  · have hsMkSpec : ef' ∈ Ecma.Spec.gl.alts cx g n' := (altsOf_eq hok cx g n') ▸ hsMk
    obtain ⟨hlhsMk, hoptsEqMk⟩ := alt_lhs_and_opts hok hsMkSpec
    have hmMk : mask' ∈ masks ef'.alt.opts := hoptsEqMk ▸ hoptsMk
    obtain ⟨hpeqMk, idMk, PMk, hidMk, hpoMk, _, hruleMk, _⟩ := prodIdOf_spec hok hsMkSpec hmMk
    have hidEq : idMk = id0 := Option.some.inj ((hpeqMk.trans hidMk).symm.trans hpidMk)
    subst hidEq
    have hPMk : P0 = PMk := Option.some.inj (hpo0.symm.trans hpoMk)
    subst hPMk
    exact hlhsMk.symm.trans ((congrArg Rule.lhs hruleMk).symm.trans ((congrArg Rule.lhs hrule0).trans hlhs))

private theorem opt_eq_none_or_some {α : Type} (o : Option α) :
    o = none ∨ ∃ x, o = some x := by
  cases o with
  | none => exact Or.inl rfl
  | some x => exact Or.inr ⟨x, rfl⟩

private theorem build_zero (A : Alpha N T) (B : Builder N) (size D stamp : Nat)
    (n : NT) (ps : List Param) (i j : Nat) :
    build A B size D stamp 0 n ps i j = throw .depth := rfl

private theorem build_succ (A : Alpha N T) (B : Builder N) (size D stamp d : Nat)
    (n : NT) (ps : List Param) (i j : Nat) :
    build A B size D stamp (d + 1) n ps i j =
      buildStep A B size D stamp (build A B size D stamp d) n ps i j := rfl

/-- Main theorem for `Search.build`: when `build` succeeds without throwing `.ambiguous`, `nd`
corresponds via `DNodeRel` to the **unique** `ModeDerives true` tree over `(n, ps, i, j)`. -/
theorem build_spec (hok : parseTablesOk = true) (hB : BuilderSpec B)
    (hg : A.g = .syntactic ∨ A.g ∈ codeGrammars)
    (D stamp : Nat)
    (hstmp : S.LeafStamp.all (· == stamp) = true := by rfl) :
    ∀ (d : Nat) (n : NT) (ps : List Param) (i j : Nat) (st : St T) (nd : N) (st' : St T),
      S.BuildInv st →
      (build A B size D stamp d n ps i j).run st = .ok (nd, st') →
      S.BuildInv st' ∧
      B.nt nd = n.ctorIdx ∧
      B.args nd = ps ∧
      ∃ t,
        S.ModeDerives true n ps i j t ∧
        S.DNodeRel stamp nd t ∧
        (∀ t', S.ModeDerives true n ps i j t' → t' = t) := by
  intro d
  induction d with
  | zero =>
    intro _ _ _ _ _ _ _ _ hrun
    rw [build_zero, sm_run_throw] at hrun; cases hrun
  | succ d ih =>
    intro n ps i j st nd st' hb hrun
    rw [build_succ] at hrun
    unfold buildStep at hrun
    by_cases hem : (altsOf A.cx A.g n).isEmpty = true
    · have hrun' := sm_ite_true hrun hem
      rw [sm_run_throw] at hrun'; cases hrun'
    · have hemf : (altsOf A.cx A.g n).isEmpty = false := Bool.eq_false_iff.mpr hem
      have hr1 := sm_ite_false hrun hemf
      obtain ⟨found, st1, hpickRun, hr2⟩ := sm_bind_ok hr1
      rcases found with _ | ⟨e, fw⟩
      · rw [sm_run_throw] at hr2; cases hr2
      · have ⟨hb1, heMem, heAllow, heGrd, hjMem, hfsv, hopv, huniqAlt⟩ :=
          S.pick_spec hok hg D n ps i j st e fw st1 hb hpickRun
        have hchild : S.ChildSpec stamp (build A B size D stamp d) :=
          fun m ps' h c st0 nd0 st0' hb0 hcRun => ih m ps' h c st0 nd0 st0' hb0 hcRun
        obtain ⟨rTriple, st2, hrhsRun, hr3⟩ := sm_bind_ok hr2
        rcases rTriple with ⟨cur, pieces, mask⟩
        have ⟨hb2, hcurInI, hpcs, ts_built, hswBuilt, huniqSeq⟩ :=
          S.buildRhs_spec hok hg D stamp hchild n e ps j hstmp 0 e.alt.rhs (.single i) fw.sets fw.last fw.prov
            st1 cur pieces mask st2 hb1 (fun it hit => itemWF_of_mem A hok hg heMem hit)
            hfsv hopv hjMem hrhsRun
        rw [Ends.mem_single] at hcurInI
        have hr4 := sm_ite_true hr3 hcurInI
        rw [beq_iff_eq] at hcurInI; subst cur
        rcases opt_eq_none_or_some (prodIdOf e mask) with hnone | ⟨p, hpid⟩
        · rw [hnone, sm_run_throw] at hr4; cases hr4
        · rw [hpid] at hr4
          obtain ⟨hfindUniq, hlhsUniq⟩ := prodIdOf_mem_unique hok heMem (S.seqWith_masks hswBuilt) hpid
          have hallowMk : ∀ P' ef', prodOf p = some P' →
              (altsOf A.cx A.g P'.rule.lhs).find? (fun x => x.grammar == P'.grammar && x.idx == P'.alt && x.rule == P'.rule) = some ef' →
              prodIdOf ef' P'.mask = some p →
              S.CommitAllow true P'.rule.lhs ps i ef' := by
            intro P' ef' hpo' hfind' _
            obtain ⟨hlhsEq, rfl⟩ := hfindUniq P' ef' hpo' hfind'
            rw [hlhsEq]
            exact heAllow
          have ⟨hi3, hm3, ha3, _, hfw3, hfi3, hfar3, n_mk, ef_mk, mask_mk, kids_mk, hntNd, hderMk, hdrelMk⟩ :=
            mk_sound S hok hB hg hb2.memo.inv hpcs hallowMk hr4
          have hb3 : S.BuildInv st' := hb2.of_alpha_eq hi3 hm3 ha3 hfw3 hfi3 hfar3
          have hnEq : n_mk = n := by
            cases hderMk with
            | node _ hsMk _ _ hpidMk hswMk =>
              exact hlhsUniq n_mk ef_mk mask_mk hsMk (S.seqWith_masks hswMk) hpidMk
          subst n_mk
          have hargsNd : B.args nd = ps := by cases hdrelMk with | node _ _ hargs _ _ _ _ => exact hargs
          have htreeUniq : ∀ t', S.ModeDerives true n ps i j t' →
              t' = .node n p e ps i j mask ts_built := by
            intro t' hder'
            cases hder' with
            | node e' he' hal' hgrd' hpid' hsw' =>
              have hsr' : S.SeqRel (S.SpanOfAllow (S.CommitAllow true)) e' ps 0 e'.alt.rhs i j :=
                S.seqRel_iff_seqWith.mpr ⟨_, _, hsw'⟩
              have heEq : e' = e := huniqAlt e' he' hal' hgrd' hsr'
              subst heEq
              obtain ⟨_, rfl, rfl⟩ := huniqSeq i _ _ (by simp only [Ends.mem_single, beq_self_eq_true]) hsw'
              have hpEq : p = _ := Option.some.inj (hpid.symm.trans hpid')
              subst hpEq
              rfl
          have hmkEq := htreeUniq _ hderMk
          rw [hmkEq] at hderMk hdrelMk
          exact ⟨hb3, hntNd, hargsNd, _, hderMk, hdrelMk, htreeUniq⟩

end AlphaSpec

end Engine.Parse
