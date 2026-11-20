module

public import Ecma.Host.ForIn
public import Engine.Host.Strategy

@[expose] public section

/-!
# The ForIn strategy's law

`forInChoice` obeys the rules of EnumerateObjectProperties (`forInChoice_law`): the lemma both
hosts (`Engine.RefHost`, `JSSpec.Host`) prove their `forInStep` law with, out of the base.
-/

namespace Ecma

variable {M : Model}

section Proofs

variable (hs : ∀ a b, M.strEq a b = true ↔ a = b)
include hs

theorem anyStrEq_iff (vis : List M.Str) (x : M.Str) : vis.any (M.strEq · x) = true ↔ x ∈ vis := by
  simp only [List.any_eq_true, hs]
  exact ⟨fun ⟨v, hv, e⟩ => e ▸ hv, fun h => ⟨x, h, rfl⟩⟩

omit hs in
theorem cfiSkip_cons (vis : List M.Str) : ∀ rem k r, cfiSkip vis rem = k :: r →
    ∃ pre, rem = pre ++ k :: r ∧ (∀ x ∈ pre, vis.any (M.strEq · x) = true) ∧ vis.any (M.strEq · k) = false
  | [], _, _, h => by simp [cfiSkip] at h
  | x :: rem, k, r, h => by
    unfold cfiSkip at h
    split at h
    · obtain ⟨pre, e, hp, hk⟩ := cfiSkip_cons vis rem k r h
      refine ⟨x :: pre, by simp [e], ?_, hk⟩
      intro y hy
      rcases List.mem_cons.1 hy with rfl | hy
      · assumption
      · exact hp y hy
    · rename_i hn
      cases h
      exact ⟨[], rfl, by simp, by simpa using hn⟩

omit hs in
theorem cfiSkip_nil (vis : List M.Str) : ∀ rem, cfiSkip vis rem = [] → ∀ x ∈ rem, vis.any (M.strEq · x) = true
  | [], _, _, hx => by simp at hx
  | y :: rem, h, x, hx => by
    unfold cfiSkip at h
    split at h
    · rcases List.mem_cons.1 hx with rfl | hx
      · assumption
      · exact cfiSkip_nil vis rem h x hx
    · cases h

omit hs in
theorem chainObj_mono {obj : M.Addr} {es : List (ForInEntry M)} (e : ForInEntry M) {o : M.Addr}
    (h : chainObj obj es o) : chainObj obj (es ++ [e]) o := by
  rcases h with h | ⟨p, hp⟩
  · exact .inl h
  · exact .inr ⟨p, List.mem_append_left _ hp⟩

omit hs in
theorem accounted_mono {es : List (ForInEntry M)} (e : ForInEntry M) {k : M.Str}
    (h : accounted es k) : accounted (es ++ [e]) k := by
  rcases h with h | ⟨o, d, hm, hd⟩
  · exact .inl (List.mem_append_left _ h)
  · exact .inr ⟨o, d, List.mem_append_left _ hm, hd⟩

/-- What the replay keeps true of the entries so far. -/
structure CfiInv (obj : M.Addr) (st : CfiSt M) (es : List (ForInEntry M)) : Prop where
  curChain : ∀ o, st.cur = some o → chainObj obj es o
  noneWas : st.cur = none → st.was = false
  remNil : st.was = false → st.remaining = []
  remKeys : st.was = true → ∀ o, st.cur = some o → ∃ ks, ForInEntry.keys o ks ∈ es ∧ ∀ k ∈ st.remaining, Val.str k ∈ ks
  visOwn : ∀ o d k, ForInEntry.own o (.str k) (some d) ∈ es → k ∈ st.visited
  yieldVis : ∀ k, ForInEntry.yield k ∈ es → k ∈ st.visited
  visAcc : ∀ k ∈ st.visited, accounted es k ∨ st.pending = some k
  pend : ∀ k, st.pending = some k → ∃ es0 o, es = es0 ++ [.own o (.str k) (some true)] ∧ chainObj obj es0 o ∧
    (∀ o' d, ForInEntry.own o' (.str k) (some d) ∉ es0) ∧ ForInEntry.yield k ∉ es0
  noneProto : st.cur = none → ∃ o, chainObj obj es o ∧ ForInEntry.proto o none ∈ es
  chainKeys : ∀ o, chainObj obj es o → (∃ ks, ForInEntry.keys o ks ∈ es) ∨ (st.cur = some o ∧ st.was = false)
  keysAcc : ∀ o ks k, ForInEntry.keys o ks ∈ es → Val.str k ∈ ks →
    k ∈ st.remaining ∨ accounted es k ∨ st.pending = some k

omit hs in
theorem cfiInv_init (obj : M.Addr) : CfiInv obj (CfiSt.init obj) [] where
  curChain o h := by cases h; exact .inl rfl
  noneWas h := by cases h
  remNil _ := rfl
  remKeys h := by cases h
  visOwn _ _ _ h := by cases h
  yieldVis _ h := by cases h
  visAcc _ h := by cases h
  pend _ h := by cases h
  noneProto h := by cases h
  chainKeys o h := by
    rcases h with rfl | ⟨_, h⟩
    · exact .inr ⟨rfl, rfl⟩
    · cases h
  keysAcc _ _ _ h := by cases h

omit hs in
theorem CfiSt.next_cases (st : CfiSt M) :
    (∃ k, st.pending = some k ∧ st.next = .yield k) ∨
    (st.pending = none ∧ st.cur = none ∧ st.next = .done) ∨
    (∃ o, st.pending = none ∧ st.cur = some o ∧ st.was = false ∧ st.next = .keys o) ∨
    (∃ o k r, st.pending = none ∧ st.cur = some o ∧ st.was = true ∧
      cfiSkip st.visited st.remaining = k :: r ∧ st.next = .own o (.str k)) ∨
    (∃ o, st.pending = none ∧ st.cur = some o ∧ st.was = true ∧
      cfiSkip st.visited st.remaining = [] ∧ st.next = .proto o) := by
  rcases st with ⟨cur, was, vis, rem, pend⟩
  rcases pend with _ | k
  · rcases cur with _ | o
    · exact .inr (.inl ⟨rfl, rfl, rfl⟩)
    · cases was
      · exact .inr (.inr (.inl ⟨o, rfl, rfl, rfl, rfl⟩))
      · cases h : cfiSkip vis rem with
        | nil => exact .inr (.inr (.inr (.inr ⟨o, rfl, rfl, rfl, rfl, by simp [CfiSt.next, h]⟩)))
        | cons k r => exact .inr (.inr (.inr (.inl ⟨o, k, r, rfl, rfl, rfl, rfl, by simp [CfiSt.next, h]⟩)))
  · exact .inl ⟨k, rfl, rfl⟩

omit hs in
theorem chainObj_snoc {obj : M.Addr} {es : List (ForInEntry M)} {e : ForInEntry M} {o : M.Addr}
    (h : chainObj obj (es ++ [e]) o) : chainObj obj es o ∨ ∃ p, e = .proto p (some o) := by
  rcases h with h | ⟨p, hp⟩
  · exact .inl (.inl h)
  · rcases List.mem_append.1 hp with hp | hp
    · exact .inl (.inr ⟨p, hp⟩)
    · exact .inr ⟨p, (List.mem_singleton.1 hp).symm⟩

theorem cfiInv_step {obj : M.Addr} {st : CfiSt M} {es : List (ForInEntry M)} (I : CfiInv obj st es)
    (e : ForInEntry M) (he : e.act = st.next) : CfiInv obj (st.step e) (es ++ [e]) := by
  rcases st with ⟨cur, was, vis, rem, pnd⟩
  rcases CfiSt.next_cases ⟨cur, was, vis, rem, pnd⟩ with
    ⟨k, hp, hn⟩ | ⟨hp, hc, hn⟩ | ⟨o, hp, hc, hw, hn⟩ | ⟨o, k, r, hp, hc, hw, hk, hn⟩ | ⟨o, hp, hc, hw, hk, hn⟩
  · -- yield k
    simp only at hp; subst hp; rw [hn] at he
    cases e <;> simp only [ForInEntry.act, ForInAct.yield.injEq, reduceCtorEq] at he
    rename_i k'
    subst k'
    obtain ⟨es0, o, rfl, hch, hno, hny⟩ := I.pend k rfl
    simp only [CfiSt.step]
    exact {
      curChain := fun o' h => chainObj_mono _ (I.curChain o' h)
      noneWas := I.noneWas
      remNil := I.remNil
      remKeys := fun hw o' h => let ⟨ks, hm, hr⟩ := I.remKeys hw o' h; ⟨ks, List.mem_append_left _ hm, hr⟩
      visOwn := fun o' d k' h => by
        rcases List.mem_append.1 h with h | h
        · exact I.visOwn o' d k' h
        · simp at h
      yieldVis := fun k' h => by
        rcases List.mem_append.1 h with h | h
        · exact I.yieldVis k' h
        · cases List.mem_singleton.1 h
          exact I.visOwn o true k (by simp)
      visAcc := fun k' h => by
        rcases I.visAcc k' h with h | h
        · exact .inl (accounted_mono _ h)
        · cases h; exact .inl (.inl (by simp))
      pend := fun _ h => by cases h
      noneProto := fun h => let ⟨o', hc, hm⟩ := I.noneProto h; ⟨o', chainObj_mono _ hc, List.mem_append_left _ hm⟩
      chainKeys := fun o' h => by
        rcases chainObj_snoc h with h | ⟨_, h⟩
        · rcases I.chainKeys o' h with ⟨ks, hm⟩ | h
          · exact .inl ⟨ks, List.mem_append_left _ hm⟩
          · exact .inr h
        · cases h
      keysAcc := fun o' ks k' hm hk => by
        rcases List.mem_append.1 hm with hm | hm
        · rcases I.keysAcc o' ks k' hm hk with h | h | h
          · exact .inl h
          · exact .inr (.inl (accounted_mono _ h))
          · cases h; exact .inr (.inl (.inl (by simp)))
        · simp at hm }
  · -- done
    rw [hn] at he
    cases e <;> simp [ForInEntry.act] at he
  · -- keys o
    simp only at hp hc hw; subst hp hc hw; rw [hn] at he
    cases e <;> simp only [ForInEntry.act, ForInAct.keys.injEq, reduceCtorEq] at he
    rename_i o' ks
    subst o'
    have hr := I.remNil rfl
    simp only at hr
    subst hr
    simp only [CfiSt.step, List.nil_append]
    exact {
      curChain := fun o' h => chainObj_mono _ (I.curChain o' h)
      noneWas := fun h => by cases h
      remNil := fun h => by cases h
      remKeys := fun _ o' h => by
        cases h
        refine ⟨ks, by simp, fun k hk => ?_⟩
        simp only [strKeys, List.mem_filterMap] at hk
        obtain ⟨v, hv, hv'⟩ := hk
        cases v <;> simp at hv'
        subst hv'; exact hv
      visOwn := fun o' d k' h => by
        rcases List.mem_append.1 h with h | h
        · exact I.visOwn o' d k' h
        · simp at h
      yieldVis := fun k' h => by
        rcases List.mem_append.1 h with h | h
        · exact I.yieldVis k' h
        · simp at h
      visAcc := fun k' h => by
        rcases I.visAcc k' h with h | h
        · exact .inl (accounted_mono _ h)
        · cases h
      pend := fun _ h => by cases h
      noneProto := fun h => by cases h
      chainKeys := fun o' h => by
        rcases chainObj_snoc h with h | ⟨_, h⟩
        · rcases I.chainKeys o' h with ⟨ks', hm⟩ | ⟨h1, _⟩
          · exact .inl ⟨ks', List.mem_append_left _ hm⟩
          · cases h1; exact .inl ⟨ks, by simp⟩
        · cases h
      keysAcc := fun o' ks' k' hm hk => by
        rcases List.mem_append.1 hm with hm | hm
        · rcases I.keysAcc o' ks' k' hm hk with h | h | h
          · simp at h
          · exact .inr (.inl (accounted_mono _ h))
          · cases h
        · simp only [List.mem_singleton, ForInEntry.keys.injEq] at hm
          obtain ⟨rfl, rfl⟩ := hm
          refine .inl ?_
          simp only [strKeys, List.mem_filterMap]
          exact ⟨_, hk, rfl⟩ }
  · -- own o k
    simp only at hp hc hw hk; subst hp hc hw; rw [hn] at he
    cases e <;> simp only [ForInEntry.act, ForInAct.own.injEq, reduceCtorEq] at he
    rename_i o' k' d
    obtain ⟨h1, h2⟩ := he
    subst o' k'
    obtain ⟨pre, hrem, hpre, hk0⟩ := cfiSkip_cons vis rem k r hk
    have hkv : k ∉ vis := fun h => by rw [(anyStrEq_iff hs vis k).2 h] at hk0; cases hk0
    have hpv : ∀ x ∈ pre, x ∈ vis := fun x hx => (anyStrEq_iff hs vis x).1 (hpre x hx)
    have hs' : (CfiSt.step ⟨some o, true, vis, rem, none⟩ (.own o (.str k) d)) =
        ⟨some o, true, if d.isSome then vis ++ [k] else vis, r, if d = some true then some k else none⟩ := by
      simp [CfiSt.step, hk]
    rw [hs']
    have hacc : d ≠ some true → accounted (es ++ [.own o (.str k) d]) k :=
      fun hd => .inr ⟨o, d, by simp, hd⟩
    exact {
      curChain := fun o' h => chainObj_mono _ (I.curChain o' h)
      noneWas := fun h => by cases h
      remNil := fun h => by cases h
      remKeys := fun _ o' h => by
        obtain ⟨ks, hm, hr⟩ := I.remKeys rfl o' h
        exact ⟨ks, List.mem_append_left _ hm, fun x hx => hr x (by rw [hrem]; simp [hx])⟩
      visOwn := fun o' d' k' h => by
        rcases List.mem_append.1 h with h | h
        · have := I.visOwn o' d' k' h
          split <;> simp [this]
        · simp only [List.mem_singleton, ForInEntry.own.injEq, Val.str.injEq] at h
          obtain ⟨rfl, rfl, rfl⟩ := h
          simp
      yieldVis := fun k' h => by
        rcases List.mem_append.1 h with h | h
        · have := I.yieldVis k' h
          split <;> simp [this]
        · simp at h
      visAcc := fun k' h => by
        have h' : k' ∈ vis ∨ (d.isSome ∧ k' = k) := by
          split at h
          · rcases List.mem_append.1 h with h | h
            · exact .inl h
            · exact .inr ⟨‹_›, List.mem_singleton.1 h⟩
          · exact .inl h
        rcases h' with h' | ⟨_, rfl⟩
        · rcases I.visAcc k' h' with h | h
          · exact .inl (accounted_mono _ h)
          · cases h
        · by_cases hd : d = some true
          · exact .inr (by simp [hd])
          · exact .inl (hacc hd)
      pend := fun k' h => by
        by_cases hd : d = some true
        · rw [if_pos hd] at h
          cases h
          subst hd
          exact ⟨es, o, rfl, I.curChain o rfl, fun o' d' hm => hkv (I.visOwn o' d' _ hm),
            fun hm => hkv (I.yieldVis _ hm)⟩
        · rw [if_neg hd] at h
          cases h
      noneProto := fun h => by cases h
      chainKeys := fun o' h => by
        rcases chainObj_snoc h with h | ⟨_, h⟩
        · rcases I.chainKeys o' h with ⟨ks, hm⟩ | ⟨_, h2⟩
          · exact .inl ⟨ks, List.mem_append_left _ hm⟩
          · cases h2
        · cases h
      keysAcc := fun o' ks k' hm hk' => by
        rcases List.mem_append.1 hm with hm | hm
        · rcases I.keysAcc o' ks k' hm hk' with h | h | h
          · rw [hrem] at h
            rcases List.mem_append.1 h with h | h
            · rcases I.visAcc k' (hpv k' h) with h | h
              · exact .inr (.inl (accounted_mono _ h))
              · cases h
            · rcases List.mem_cons.1 h with rfl | h
              · by_cases hd : d = some true
                · exact .inr (.inr (by simp [hd]))
                · exact .inr (.inl (hacc hd))
              · exact .inl h
          · exact .inr (.inl (accounted_mono _ h))
          · cases h
        · simp at hm }
  · -- proto o
    simp only at hp hc hw hk; subst hp hc hw; rw [hn] at he
    cases e <;> simp only [ForInEntry.act, ForInAct.proto.injEq, reduceCtorEq] at he
    rename_i o' p
    subst o'
    have hall : ∀ x ∈ rem, x ∈ vis := fun x hx => (anyStrEq_iff hs vis x).1 (cfiSkip_nil vis rem hk x hx)
    simp only [CfiSt.step]
    exact {
      curChain := fun o' h => by
        cases h
        exact .inr ⟨o, by simp⟩
      noneWas := fun _ => rfl
      remNil := fun _ => rfl
      remKeys := fun h => by cases h
      visOwn := fun o' d k' h => by
        rcases List.mem_append.1 h with h | h
        · exact I.visOwn o' d k' h
        · simp at h
      yieldVis := fun k' h => by
        rcases List.mem_append.1 h with h | h
        · exact I.yieldVis k' h
        · simp at h
      visAcc := fun k' h => by
        rcases I.visAcc k' h with h | h
        · exact .inl (accounted_mono _ h)
        · cases h
      pend := fun _ h => by cases h
      noneProto := fun h => by
        subst h
        exact ⟨o, chainObj_mono _ (I.curChain o rfl), by simp⟩
      chainKeys := fun o' h => by
        rcases chainObj_snoc h with h | ⟨_, h⟩
        · rcases I.chainKeys o' h with ⟨ks, hm⟩ | ⟨h1, h2⟩
          · exact .inl ⟨ks, List.mem_append_left _ hm⟩
          · cases h2
        · simp only [ForInEntry.proto.injEq] at h
          obtain ⟨_, rfl⟩ := h
          exact .inr ⟨rfl, rfl⟩
      keysAcc := fun o' ks k' hm hk' => by
        rcases List.mem_append.1 hm with hm | hm
        · rcases I.keysAcc o' ks k' hm hk' with h | h | h
          · rcases I.visAcc k' (hall k' h) with h | h
            · exact .inr (.inl (accounted_mono _ h))
            · cases h
          · exact .inr (.inl (accounted_mono _ h))
          · cases h
        · simp at hm }

omit hs in
/-- The replay's next action obeys the rules. -/
theorem cfiInv_rules {obj : M.Addr} {st : CfiSt M} {es : List (ForInEntry M)} (I : CfiInv obj st es) :
    ForInRules obj es st.next := by
  rcases CfiSt.next_cases st with
    ⟨k, hp, hn⟩ | ⟨hp, hc, hn⟩ | ⟨o, hp, hc, hw, hn⟩ | ⟨o, k, r, hp, hc, hw, hk, hn⟩ | ⟨o, hp, hc, hw, hk, hn⟩ <;>
    rw [hn]
  · obtain ⟨es0, o, rfl, hch, hno, hny⟩ := I.pend k hp
    refine ⟨fun e he hey => ?_, es0.length, o, by simp, chainObj_mono _ hch, fun _ j hj o' d hjd => ?_⟩
    · subst hey
      rcases List.mem_append.1 he with h | h
      · exact hny h
      · simp at h
    · rw [List.getElem?_append_left hj] at hjd
      exact absurd (List.mem_of_getElem? hjd) (hno o' d)
  · refine ⟨I.noneProto hc, fun o h => ?_, fun o ks k hm hk => ?_⟩
    · rcases I.chainKeys o h with h | ⟨h, _⟩
      · exact h
      · rw [hc] at h; cases h
    · rcases I.keysAcc o ks k hm hk with h | h | h
      · rw [I.remNil (I.noneWas hc)] at h; cases h
      · exact h
      · rw [hp] at h; cases h
  · exact I.curChain o hc
  · obtain ⟨pre, hrem, _, _⟩ := cfiSkip_cons _ _ k r hk
    obtain ⟨ks, hm, hr⟩ := I.remKeys hw o hc
    exact ⟨I.curChain o hc, ks, hm, hr k (by rw [hrem]; simp)⟩
  · exact I.curChain o hc

theorem cfiInv_run {obj : M.Addr} : ∀ (es : List (ForInEntry M)) (st : CfiSt M) (pre : List (ForInEntry M)),
    CfiInv obj st pre → CfiOk st es → CfiInv obj (es.foldl CfiSt.step st) (pre ++ es)
  | [], _, pre, I, _ => by simpa using I
  | e :: es, st, pre, I, ⟨he, h⟩ => by
    have := cfiInv_run es (st.step e) (pre ++ [e]) (cfiInv_step hs I e he) h
    simpa using this

/-- On a run of CreateForInIterator's actions, its next action obeys the rules. -/
theorem cfiNext_rules (obj : M.Addr) (es : List (ForInEntry M)) (h : CfiOk (CfiSt.init obj) es) :
    ForInRules obj es (cfiNext obj es) := by
  have := cfiInv_run hs es (CfiSt.init obj) [] (cfiInv_init obj) h
  simp only [List.nil_append] at this
  exact cfiInv_rules this

omit hs in
theorem ForInAct.same_self_next (st : CfiSt M) (hs : ∀ a b, M.strEq a b = true ↔ a = b)
    (ha : ∀ a b, M.addrEq a b = true ↔ a = b) : st.next.same st.next = true := by
  rcases CfiSt.next_cases st with
    ⟨k, _, hn⟩ | ⟨_, _, hn⟩ | ⟨o, _, _, _, hn⟩ | ⟨o, k, r, _, _, _, _, hn⟩ | ⟨o, _, _, _, _, hn⟩ <;>
    rw [hn] <;> simp [ForInAct.same, hs, ha]

theorem ForInAct.same_sound (ha : ∀ a b, M.addrEq a b = true ↔ a = b) :
    ∀ a b : ForInAct M, a.same b = true → a = b
  | .keys _, .keys _, h | .proto _, .proto _, h => by simp_all [ForInAct.same]
  | .yield _, .yield _, h => by simp_all [ForInAct.same]
  | .done, .done, _ => rfl
  | .keys _, .own _ _, h | .keys _, .proto _, h | .keys _, .yield _, h | .keys _, .done, h => by
    simp [ForInAct.same] at h
  | .proto _, .keys _, h | .proto _, .own _ _, h | .proto _, .yield _, h | .proto _, .done, h => by
    simp [ForInAct.same] at h
  | .yield _, .keys _, h | .yield _, .own _ _, h | .yield _, .proto _, h | .yield _, .done, h => by
    simp [ForInAct.same] at h
  | .done, .keys _, h | .done, .own _ _, h | .done, .proto _, h | .done, .yield _, h => by
    simp [ForInAct.same] at h
  | .own _ _, .keys _, h | .own _ _, .proto _, h | .own _ _, .yield _, h | .own _ _, .done, h => by
    simp [ForInAct.same] at h
  | .own _ k, .own _ k', h => by cases k <;> cases k' <;> simp_all [ForInAct.same]

theorem cfiCheck_iff (ha : ∀ a b, M.addrEq a b = true ↔ a = b) :
    ∀ (es : List (ForInEntry M)) (st : CfiSt M), cfiCheck st es = true ↔ CfiOk st es
  | [], _ => by simp [cfiCheck, CfiOk]
  | e :: es, st => by
    simp only [cfiCheck, CfiOk, Bool.and_eq_true, cfiCheck_iff ha es]
    constructor
    · exact fun ⟨h1, h2⟩ => ⟨ForInAct.same_sound hs ha _ _ h1, h2⟩
    · exact fun ⟨h1, h2⟩ => ⟨h1 ▸ ForInAct.same_self_next st hs ha, h2⟩

/-- ForInStep by `forInChoice` meets its law: a new action Record, obeying the rules, and
CreateForInIterator's action where ¶3's conditions hold. -/
theorem forInChoice_law (ha : ∀ a b, M.addrEq a b = true ↔ a = b) (obj : M.Addr) (h : Val M)
    (s : State M) (r : Val M) (s' : State M) (hc : forInChoice [.obj obj, h] s = .ok r s')
    (es : List (ForInEntry M)) (he : forInHist s h = some es) :
    ∃ act, actRecord act s = .ok r s' ∧ ForInRules obj es act ∧
      (cfiApplies s obj h es → act = cfiNext obj es) := by
  unfold forInChoice forInChoiceBy at hc
  simp only [he] at hc
  refine ⟨forInAct obj es, hc, ?_, fun ⟨_, _, hok⟩ => ?_⟩
  · unfold forInAct
    split
    · exact cfiNext_rules hs obj es ((cfiCheck_iff hs ha es _).1 ‹_›)
    · exact .inl rfl
  · simp [forInAct, (cfiCheck_iff hs ha es _).2 hok]

end Proofs

end Ecma
