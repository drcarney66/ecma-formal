module

public import Engine.Proofs.Parse.Kernel

@[expose] public section

/-!
# Soundness and completeness of memoized fixpoint search (`Engine.Parse.Search.ends`)

Proves parameter-bit invariance of `DerivesWith` / `ModeDerives`, characterizes single-item and
sequence stepping (`ItemMatch`, `ItemStep`, `SeqRel`), and proves via Tarski post-fixpoint
closure (`PostFix`) that `finalEndsAt` computes exact `ModeDerives` end-sets and `finalEnds`
computes the exact furthest match `SpecHit` (`st.far`).
-/

namespace Engine.Parse

open Ecma.Grammar Search

/-! ## Container & List façade -/

theorem hm_empty {α β : Type} [BEq α] [Hashable α] (k : α) :
    ({} : Std.HashMap α β)[k]? = none := by simp

theorem hm_insert {α β : Type} [BEq α] [LawfulBEq α] [Hashable α] [LawfulHashable α]
    (m : Std.HashMap α β) (k k' : α) (v : β) :
    (m.insert k v)[k']? = if k == k' then some v else m[k']? := by
  simp [Std.HashMap.getElem?_insert]

theorem hm_insert_eq {α β : Type} [BEq α] [LawfulBEq α] [Hashable α] [LawfulHashable α]
    (m : Std.HashMap α β) (k : α) (v : β) :
    (m.insert k v)[k]? = some v := by
  rw [hm_insert]; simp

theorem hm_insert_ne {α β : Type} [BEq α] [LawfulBEq α] [Hashable α] [LawfulHashable α]
    (m : Std.HashMap α β) {k k' : α} (v : β) (hne : k ≠ k') :
    (m.insert k v)[k']? = m[k']? := by
  rw [hm_insert]
  have h : ¬ ((k == k') = true) := by rw [beq_iff_eq]; exact hne
  simp [h]

theorem sm_get_bind_ok {T α : Type} {f : St T → SM T α} {st : St T} {v : α} {st' : St T}
    (h : (get >>= f).run st = .ok (v, st')) : (f st).run st = .ok (v, st') := h

theorem hm_getD {α β : Type} [BEq α] [LawfulBEq α] [Hashable α] [LawfulHashable α]
    (m : Std.HashMap α β) (k : α) (d : β) :
    m.getD k d = (m[k]?).getD d := by
  simp [Std.HashMap.getD_eq_getD_getElem?]

theorem hs_empty {α : Type} [BEq α] [Hashable α] (k : α) :
    ({} : Std.HashSet α).contains k = false := by simp

theorem hs_insert {α : Type} [BEq α] [LawfulBEq α] [Hashable α] [LawfulHashable α]
    (s : Std.HashSet α) (k k' : α) :
    (s.insert k).contains k' = (k == k' || s.contains k') := by
  simp [Std.HashSet.contains_insert]

theorem hs_erase {α : Type} [BEq α] [LawfulBEq α] [Hashable α] [LawfulHashable α]
    (s : Std.HashSet α) (k k' : α) :
    (s.erase k).contains k' = (!(k == k') && s.contains k') := by
  simp [Std.HashSet.contains_erase]

theorem hs_isEmpty_iff {α : Type} [BEq α] [LawfulBEq α] [Hashable α] [LawfulHashable α]
    (s : Std.HashSet α) :
    s.isEmpty = true ↔ ∀ k, s.contains k = false := by
  simp [Std.HashSet.isEmpty_iff_forall_contains]

theorem hs_insertMany {α : Type} [BEq α] [LawfulBEq α] [Hashable α] [LawfulHashable α]
    (s : Std.HashSet α) (xs : List α) (k : α) :
    (s.insertMany xs).contains k = (s.contains k || xs.contains k) := by
  simp [Std.HashSet.contains_insertMany_list]

theorem hs_mem_toList {α : Type} [BEq α] [LawfulBEq α] [Hashable α] [LawfulHashable α]
    (s : Std.HashSet α) (k : α) :
    k ∈ s.toList ↔ s.contains k = true := by simp

theorem filter_split_first {α : Type} (p : α → Bool) :
    ∀ (xs pre rem : List α) (s : α),
      xs.filter p = pre ++ s :: rem →
      ∃ pre0 post0, xs = pre0 ++ s :: post0 ∧ p s = true ∧
        ∀ s' ∈ pre0, p s' = true → s' ∈ pre
  | [], pre, _, _, h => by cases pre <;> simp at h
  | x :: xs, pre, rem, s, h => by
    cases hpx : p x with
    | false =>
      rw [List.filter_cons_of_neg (by simp [hpx])] at h
      obtain ⟨pre0, post0, rfl, hps, hpre⟩ := filter_split_first p xs pre rem s h
      refine ⟨x :: pre0, post0, rfl, hps, fun s' hs' hps' => ?_⟩
      rcases List.mem_cons.mp hs' with rfl | hs'
      · rw [hpx] at hps'; cases hps'
      · exact hpre s' hs' hps'
    | true =>
      rw [List.filter_cons_of_pos hpx] at h
      cases pre with
      | nil =>
        simp only [List.nil_append, List.cons.injEq] at h
        obtain ⟨rfl, _⟩ := h
        exact ⟨[], xs, rfl, hpx, fun _ hs' => nomatch hs'⟩
      | cons y pre' =>
        simp only [List.cons_append, List.cons.injEq] at h
        obtain ⟨rfl, h'⟩ := h
        obtain ⟨pre0, post0, rfl, hps, hpre⟩ := filter_split_first p xs pre' rem s h'
        refine ⟨x :: pre0, post0, rfl, hps, fun s' hs' hps' => ?_⟩
        rcases List.mem_cons.mp hs' with rfl | hs'
        · exact List.mem_cons_self ..
        · exact List.mem_cons_of_mem _ (hpre s' hs' hps')

/-! ## Ordering & `key` lemmas -/

theorem orderedNts_nil_of_ordered_false (hok : parseTablesOk = true) {cx : Ctx} {g : GrammarId}
    (h : orderedBy cx g = false) :
    orderedNtsBy cx g = [] := by
  rw [orderedBy_eq hok] at h
  rw [orderedNtsBy_eq hok]
  unfold GL.ordered at h
  unfold GL.orderedNts
  rw [List.eq_nil_iff_forall_not_mem]
  intro n hn
  rw [List.mem_flatMap] at hn
  obtain ⟨⟨b, m⟩, hbm, hmem⟩ := hn
  rw [List.any_eq_false] at h
  have hbm' := h (b, m) hbm
  dsimp only at hmem hbm'
  split at hmem
  · next hkind => rw [hkind] at hbm'; exact hbm' rfl
  · cases hmem

theorem orderedBy_true_of_contains_orderedNts (hok : parseTablesOk = true) {cx : Ctx} {g : GrammarId} {n : NT}
    (h : (orderedNtsBy cx g).contains n = true) :
    orderedBy cx g = true := by
  cases ho : orderedBy cx g with
  | true => rfl
  | false =>
    rw [orderedNts_nil_of_ordered_false hok ho] at h
    cases h

theorem ordered_commit_eq (hok : parseTablesOk = true) (cx : Ctx) (g : GrammarId) (c : Bool) (n : NT) :
    ((c && orderedBy cx g) && (orderedNtsBy cx g).contains n) =
      (c && (orderedNtsBy cx g).contains n) := by
  cases ho : orderedBy cx g with
  | true => simp
  | false =>
    rw [orderedNts_nil_of_ordered_false hok ho]
    simp

theorem key_eq_false_of_ordered_false {N T : Type} {A : Alpha N T}
    (h : orderedBy A.cx A.g = false) (c : Bool) (n : NT) (ps : List Param) (i : Nat) :
    key A c n ps i = key A false n ps i := by
  simp [key, h]

theorem key_inj {N T : Type} {A : Alpha N T} {c1 c2 : Bool} {n1 n2 : NT} {ps1 ps2 : List Param} {i1 i2 : Nat}
    (h : key A c1 n1 ps1 i1 = key A c2 n2 ps2 i2) :
    n1 = n2 ∧ paramBits ps1 = paramBits ps2 ∧ i1 = i2 ∧
      (c1 && orderedBy A.cx A.g) = (c2 && orderedBy A.cx A.g) := by
  unfold key at h
  injection h with _ h1
  injection h1 with hn h2
  injection h2 with hp h3
  injection h3 with hi hc
  exact ⟨nt_ctorIdx_inj hn, hp, hi, hc⟩

theorem mem_altsUnder_iff {N T : Type} (A : Alpha N T) (n : NT) (ps : List Param) (s : Src) :
    s ∈ altsUnder A n ps ↔ s ∈ altsOf A.cx A.g n ∧ s.alt.guard.all (Guard.holds ps) = true := by
  simp [altsUnder, List.mem_filter]

namespace AlphaSpec

variable {N T : Type} {B : Builder N} {A : Alpha N T} {size : Nat} (S : AlphaSpec B A size)

/-! ## `masks` membership, `allow` monotonicity, `IsFirstAlt` uniqueness, & `paramBits` invariance -/

theorem isFirstAlt_unique {n : NT} {ps : List Param} {i : Nat} {s1 s2 : Src}
    (h1 : S.IsFirstAlt n ps i s1) (h2 : S.IsFirstAlt n ps i s2) :
    s1 = s2 := by
  obtain ⟨pre1, post1, halts1, hgrd1, hex1, hno1⟩ := h1
  obtain ⟨pre2, post2, halts2, hgrd2, hex2, hno2⟩ := h2
  have heq : pre1 ++ s1 :: post1 = pre2 ++ s2 :: post2 := halts1.symm.trans halts2
  have haux : ∀ (l1 l2 : List Src),
      l1 ++ s1 :: post1 = l2 ++ s2 :: post2 →
      (∀ s' ∈ l1, s'.alt.guard.all (Guard.holds ps) = true → ¬ ∃ h m kids, S.SeqWith (fun _ _ _ _ => True) s' ps 0 s'.alt.rhs i h m kids) →
      (∀ s' ∈ l2, s'.alt.guard.all (Guard.holds ps) = true → ¬ ∃ h m kids, S.SeqWith (fun _ _ _ _ => True) s' ps 0 s'.alt.rhs i h m kids) →
      s1 = s2 := by
    intro l1
    induction l1 with
    | nil =>
      intro l2 hl _ hn2
      cases l2 with
      | nil => injection hl
      | cons y l2' =>
        injection hl with hy _
        subst hy
        exact absurd hex1 (hn2 s1 (List.mem_cons_self ..) hgrd1)
    | cons x l1' ihl =>
      intro l2 hl hn1 hn2
      cases l2 with
      | nil =>
        injection hl with hx _
        subst hx
        exact absurd hex2 (hn1 x (List.mem_cons_self ..) hgrd2)
      | cons y l2' =>
        injection hl with _ htl
        exact ihl l2' htl (fun s' hs' => hn1 s' (List.mem_cons_of_mem _ hs'))
          (fun s' hs' => hn2 s' (List.mem_cons_of_mem _ hs'))
  exact haux pre1 pre2 heq hno1 hno2

mutual
theorem derivesWith_mono_allow (S : AlphaSpec B A size) {a1 a2 : NT → List Param → Nat → Src → Prop}
    (ha : ∀ n ps i s, a1 n ps i s → a2 n ps i s)
    {n : NT} {ps : List Param} {i j : Nat} {t : DTree}
    (hd : S.DerivesWith a1 n ps i j t) : S.DerivesWith a2 n ps i j t :=
  match hd with
  | .node s hs hal hgrd hpid hseq =>
    .node s hs (ha _ _ _ _ hal) hgrd hpid (seqWith_mono_allow S ha hseq)

theorem seqWith_mono_allow (S : AlphaSpec B A size) {a1 a2 : NT → List Param → Nat → Src → Prop}
    (ha : ∀ n ps i s, a1 n ps i s → a2 n ps i s)
    {s : Src} {ps : List Param} {k : Nat} {is : List Item} {i j : Nat} {m : List Bool} {ts : List DTree}
    (hs : S.SeqWith a1 s ps k is i j m ts) : S.SeqWith a2 s ps k is i j m ts :=
  match hs with
  | .nil => .nil
  | .absent hr => .absent (seqWith_mono_allow S ha hr)
  | .term ht hr => .term ht (seqWith_mono_allow S ha hr)
  | .nt hne hd hk hch hr => .nt hne (derivesWith_mono_allow S ha hd) hk hch (seqWith_mono_allow S ha hr)
  | .leaf he hl hk hch hr => .leaf he hl hk hch (seqWith_mono_allow S ha hr)
  | .butNotT ht hex hr => .butNotT ht hex (seqWith_mono_allow S ha hr)
  | .butNotN hne hd hk hex hr => .butNotN hne (derivesWith_mono_allow S ha hd) hk hex (seqWith_mono_allow S ha hr)
  | .butNotLeaf he hl hk hex hr => .butNotLeaf he hl hk hex (seqWith_mono_allow S ha hr)
  | .phrase hph hr => .phrase hph (seqWith_mono_allow S ha hr)
  | .look hlk hr => .look hlk (seqWith_mono_allow S ha hr)
  | .noLT hnl hr => .noLT hnl (seqWith_mono_allow S ha hr)
  | .empty hr => .empty (seqWith_mono_allow S ha hr)
  | .onlyIf hr => .onlyIf (seqWith_mono_allow S ha hr)
end

theorem seqWith_masks (S : AlphaSpec B A size) {allow : NT → List Param → Nat → Src → Prop}
    {s : Src} {ps : List Param} {k : Nat} {is : List Item} {i j : Nat} {m : List Bool} {ts : List DTree}
    (hsw : S.SeqWith allow s ps k is i j m ts) :
    m ∈ masks ((is.filter fun | .sym _ true => true | _ => false).length) :=
  match hsw with
  | .nil => by simp [masks]
  | .absent h => by
    rw [List.filter_cons_of_pos rfl, List.length_cons, masks]
    exact List.mem_append.mpr (Or.inl (List.mem_map.mpr ⟨_, seqWith_masks S h, rfl⟩))
  | .term (o := o) _ h => by
    cases o with
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte, List.filter_cons]
      exact seqWith_masks S h
    | true =>
      simp only [↓reduceIte, List.filter_cons, List.length_cons, masks]
      exact List.mem_append.mpr (Or.inr (List.mem_map.mpr ⟨_, seqWith_masks S h, rfl⟩))
  | .nt (o := o) _ _ _ _ h => by
    cases o with
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte, List.filter_cons]
      exact seqWith_masks S h
    | true =>
      simp only [↓reduceIte, List.filter_cons, List.length_cons, masks]
      exact List.mem_append.mpr (Or.inr (List.mem_map.mpr ⟨_, seqWith_masks S h, rfl⟩))
  | .leaf (o := o) _ _ _ _ h => by
    cases o with
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte, List.filter_cons]
      exact seqWith_masks S h
    | true =>
      simp only [↓reduceIte, List.filter_cons, List.length_cons, masks]
      exact List.mem_append.mpr (Or.inr (List.mem_map.mpr ⟨_, seqWith_masks S h, rfl⟩))
  | .butNotT _ _ h => by simp only [List.filter_cons, Bool.false_eq_true, ↓reduceIte]; exact seqWith_masks S h
  | .butNotN _ _ _ _ h => by simp only [List.filter_cons, Bool.false_eq_true, ↓reduceIte]; exact seqWith_masks S h
  | .butNotLeaf _ _ _ _ h => by simp only [List.filter_cons, Bool.false_eq_true, ↓reduceIte]; exact seqWith_masks S h
  | .phrase _ h => by simp only [List.filter_cons, Bool.false_eq_true, ↓reduceIte]; exact seqWith_masks S h
  | .look _ h => by simp only [List.filter_cons, Bool.false_eq_true, ↓reduceIte]; exact seqWith_masks S h
  | .noLT _ h => by simp only [List.filter_cons, Bool.false_eq_true, ↓reduceIte]; exact seqWith_masks S h
  | .empty h => by simp only [List.filter_cons, Bool.false_eq_true, ↓reduceIte]; exact seqWith_masks S h
  | .onlyIf h => by simp only [List.filter_cons, Bool.false_eq_true, ↓reduceIte]; exact seqWith_masks S h

theorem symHolds_paramBits {s : Src} {k : Nat} {ps1 ps2 : List Param} (hp : paramBits ps1 = paramBits ps2)
    {i h : Nat} {y : Sym} :
    S.SymHolds s k ps1 i h y ↔ S.SymHolds s k ps2 i h y := by
  have hc := contains_eq_of_paramBits hp
  cases y with
  | t _ => exact Iff.rfl
  | nt n args => simp only [SymHolds, applyArgs_eq_of_contains hc]

theorem exclHolds_paramBits {s : Src} {k : Nat} {ps1 ps2 : List Param} (hp : paramBits ps1 = paramBits ps2)
    {i h : Nat} {ex : Exclusion} :
    S.ExclHolds s k ps1 i h ex ↔ S.ExclHolds s k ps2 i h ex := by
  cases ex with
  | sym y => exact S.symHolds_paramBits hp
  | oneOf ys _ =>
    simp only [ExclHolds]
    exact ⟨fun ⟨y, hy, hs⟩ => ⟨y, hy, (S.symHolds_paramBits hp).mp hs⟩,
           fun ⟨y, hy, hs⟩ => ⟨y, hy, (S.symHolds_paramBits hp).mpr hs⟩⟩

theorem guardAll_paramBits (_ : AlphaSpec B A size) {ps1 ps2 : List Param} (hp : paramBits ps1 = paramBits ps2) (gs : List Guard) :
    gs.all (Guard.holds ps1) = gs.all (Guard.holds ps2) := by
  have hc := contains_eq_of_paramBits hp
  congr 1; funext g; exact guardHolds_eq_of_contains hc g

theorem altsUnder_paramBits (S : AlphaSpec B A size) {ps1 ps2 : List Param} (hp : paramBits ps1 = paramBits ps2) (n : NT) :
    altsUnder A n ps1 = altsUnder A n ps2 := by
  unfold altsUnder
  congr 1; funext s; exact S.guardAll_paramBits hp s.alt.guard

theorem seqWith_paramBits_imp (S : AlphaSpec B A size) {allow : NT → List Param → Nat → Src → Prop}
    {ps1 ps2 : List Param} (hp : paramBits ps1 = paramBits ps2)
    {s : Src} {k : Nat} {is : List Item} {i j : Nat} {m : List Bool} {ts : List DTree}
    (hsw : S.SeqWith allow s ps1 k is i j m ts) :
    S.SeqWith allow s ps2 k is i j m ts :=
  match hsw with
  | .nil => .nil
  | .absent h => .absent (seqWith_paramBits_imp S hp h)
  | .term ht h => .term ht (seqWith_paramBits_imp S hp h)
  | .nt hne hd hk hch h => by
    have hc := contains_eq_of_paramBits hp
    rw [applyArgs_eq_of_contains hc] at hd
    exact .nt hne hd hk hch (seqWith_paramBits_imp S hp h)
  | .leaf he hl hk hch h => .leaf he hl hk hch (seqWith_paramBits_imp S hp h)
  | .butNotT ht hex h =>
    .butNotT ht (fun hx => hex ((S.exclHolds_paramBits hp).mpr hx)) (seqWith_paramBits_imp S hp h)
  | .butNotN hne hd hk hex h => by
    have hc := contains_eq_of_paramBits hp
    rw [applyArgs_eq_of_contains hc] at hd
    exact .butNotN hne hd hk (fun hx => hex ((S.exclHolds_paramBits hp).mpr hx)) (seqWith_paramBits_imp S hp h)
  | .butNotLeaf he hl hk hex h =>
    .butNotLeaf he hl hk (fun hx => hex ((S.exclHolds_paramBits hp).mpr hx)) (seqWith_paramBits_imp S hp h)
  | .phrase hph h => .phrase hph (seqWith_paramBits_imp S hp h)
  | .look hlk h => .look hlk (seqWith_paramBits_imp S hp h)
  | .noLT hnl h => .noLT hnl (seqWith_paramBits_imp S hp h)
  | .empty h => .empty (seqWith_paramBits_imp S hp h)
  | .onlyIf h => .onlyIf (seqWith_paramBits_imp S hp h)

theorem seqWith_paramBits {allow : NT → List Param → Nat → Src → Prop}
    {ps1 ps2 : List Param} (hp : paramBits ps1 = paramBits ps2)
    {s : Src} {k : Nat} {is : List Item} {i j : Nat} {m : List Bool} {ts : List DTree} :
    S.SeqWith allow s ps1 k is i j m ts ↔ S.SeqWith allow s ps2 k is i j m ts :=
  ⟨S.seqWith_paramBits_imp hp, S.seqWith_paramBits_imp hp.symm⟩

theorem isFirstAlt_paramBits {ps1 ps2 : List Param} (hp : paramBits ps1 = paramBits ps2)
    {n : NT} {i : Nat} {s : Src} :
    S.IsFirstAlt n ps1 i s ↔ S.IsFirstAlt n ps2 i s := by
  constructor
  · rintro ⟨pre, post, halts, hgrd, ⟨h, m, kids, hseq⟩, hpre⟩
    refine ⟨pre, post, halts, S.guardAll_paramBits hp s.alt.guard ▸ hgrd,
      ⟨h, m, kids, (S.seqWith_paramBits hp).mp hseq⟩, fun s' hs' hgrd' ⟨h', m', k', hseq'⟩ => ?_⟩
    exact hpre s' hs' (S.guardAll_paramBits hp.symm s'.alt.guard ▸ hgrd')
      ⟨h', m', k', (S.seqWith_paramBits hp.symm).mp hseq'⟩
  · rintro ⟨pre, post, halts, hgrd, ⟨h, m, kids, hseq⟩, hpre⟩
    refine ⟨pre, post, halts, S.guardAll_paramBits hp.symm s.alt.guard ▸ hgrd,
      ⟨h, m, kids, (S.seqWith_paramBits hp.symm).mp hseq⟩, fun s' hs' hgrd' ⟨h', m', k', hseq'⟩ => ?_⟩
    exact hpre s' hs' (S.guardAll_paramBits hp s'.alt.guard ▸ hgrd')
      ⟨h', m', k', (S.seqWith_paramBits hp).mp hseq'⟩

theorem commitAllow_paramBits {c : Bool} {ps1 ps2 : List Param} (hp : paramBits ps1 = paramBits ps2)
    {n : NT} {i : Nat} {s : Src} :
    S.CommitAllow c n ps1 i s ↔ S.CommitAllow c n ps2 i s := by
  unfold CommitAllow
  split
  · exact S.isFirstAlt_paramBits hp
  · exact Iff.rfl

theorem commitAllow_key_eq (hok : parseTablesOk = true) (c : Bool) :
    S.CommitAllow (c && orderedBy A.cx A.g) = S.CommitAllow c := by
  funext n ps i s
  unfold CommitAllow
  rw [ordered_commit_eq hok A.cx A.g c n]

theorem modeDerives_key_eq (hok : parseTablesOk = true) (c : Bool) :
    S.ModeDerives (c && orderedBy A.cx A.g) = S.ModeDerives c := by
  unfold ModeDerives
  rw [S.commitAllow_key_eq hok c]

theorem modeDerives_exists_paramBits {c : Bool} {ps1 ps2 : List Param} (hp : paramBits ps1 = paramBits ps2)
    {n : NT} {i j : Nat} :
    (∃ t, S.ModeDerives c n ps1 i j t) ↔ (∃ t, S.ModeDerives c n ps2 i j t) := by
  constructor
  · rintro ⟨_, h⟩
    cases h with
    | node s hs hal hgrd hpid hseq =>
      exact ⟨_, .node s hs ((S.commitAllow_paramBits hp).mp hal)
        (S.guardAll_paramBits hp s.alt.guard ▸ hgrd) hpid ((S.seqWith_paramBits hp).mp hseq)⟩
  · rintro ⟨_, h⟩
    cases h with
    | node s hs hal hgrd hpid hseq =>
      exact ⟨_, .node s hs ((S.commitAllow_paramBits hp.symm).mp hal)
        (S.guardAll_paramBits hp.symm s.alt.guard ▸ hgrd) hpid ((S.seqWith_paramBits hp.symm).mp hseq)⟩

theorem modeDerives_key_congr (hok : parseTablesOk = true)
    {c1 c2 : Bool} {n1 n2 : NT} {ps1 ps2 : List Param} {i1 i2 : Nat}
    (hk : key A c1 n1 ps1 i1 = key A c2 n2 ps2 i2) (j : Nat) :
    (∃ t, S.ModeDerives c1 n1 ps1 i1 j t) ↔ (∃ t, S.ModeDerives c2 n2 ps2 i2 j t) := by
  obtain ⟨rfl, hp, rfl, hc⟩ := key_inj hk
  rw [← S.modeDerives_key_eq hok c1, ← S.modeDerives_key_eq hok c2, hc]
  exact S.modeDerives_exists_paramBits hp

/-! ## Pure item/sequence stepping (`ItemMatch`, `ItemStep`, `SeqRel`) & `SpecHit` -/

def SpanOfAllow (allow : NT → List Param → Nat → Src → Prop) (n : NT) (ps : List Param) (i j : Nat) : Prop :=
  ∃ t, S.DerivesWith allow n ps i j t

def OfKey (_ : AlphaSpec B A size) (c : Bool) (M : Key → Nat → Prop) (n : NT) (ps : List Param) (i j : Nat) : Prop :=
  M (key A c n ps i) j

theorem ofKey_eq_false_of_ordered_false (hord : orderedBy A.cx A.g = false)
    (c : Bool) (M : Key → Nat → Prop) :
    S.OfKey c M = S.OfKey false M := by
  funext n ps i j
  simp [OfKey, key_eq_false_of_ordered_false hord]

def CondOpt (next : Option Item) (h j : Nat) : Prop :=
  match next with
  | some (.onlyIf c) => S.Cond c h j
  | _ => True

theorem condOpt_head (is : List Item) (h j : Nat) :
    S.CondOpt is.head? h j ↔ S.CondHolds is h j := by
  cases is with
  | nil => simp [CondOpt, CondHolds, condAfter]
  | cons hd _ => cases hd <;> simp [CondOpt, CondHolds, condAfter]

def ItemMatch (R : NT → List Param → Nat → Nat → Prop) (s : Src) (k : Nat) (ps : List Param)
    (it : Item) (next : Option Item) (h j : Nat) : Prop :=
  match it with
  | .sym (.t x) _ => S.Term s k x h j
  | .sym (.nt n args) _ =>
    A.keep s.rule.lhs n j = true ∧ S.CondOpt next h j ∧
      if !(altsOf A.cx A.g n).isEmpty then R n (applyArgs ps args) h j else S.Leaf n h j
  | .butNot (.t x) ex => S.Term s k x h j ∧ ¬ S.ExclHolds s k ps h j ex
  | .butNot (.nt n args) ex =>
    A.keep s.rule.lhs n j = true ∧ ¬ S.ExclHolds s k ps h j ex ∧
      if !(altsOf A.cx A.g n).isEmpty then R n (applyArgs ps args) h j else S.Leaf n h j
  | .phrase p => S.Phrase p h j
  | _ => False

def ItemStep (R : NT → List Param → Nat → Nat → Prop) (s : Src) (k : Nat) (ps : List Param)
    (it : Item) (next : Option Item) (h j : Nat) : Prop :=
  match it with
  | .sym x o => (o = true ∧ j = h) ∨ S.ItemMatch R s k ps (.sym x o) next h j
  | .butNot base ex => S.ItemMatch R s k ps (.butNot base ex) next h j
  | .phrase p => S.ItemMatch R s k ps (.phrase p) next h j
  | .lookahead l => j = h ∧ S.LookHolds l h
  | .noLT => j = h ∧ S.NoLT h
  | .empty | .onlyIf _ => j = h

inductive SeqRel (R : NT → List Param → Nat → Nat → Prop) (s : Src) (ps : List Param) :
    Nat → List Item → Nat → Nat → Prop where
  | nil {k i} : SeqRel R s ps k [] i i
  | cons {k it rest i h j} :
      S.ItemStep R s k ps it rest.head? i h →
      SeqRel R s ps (k + 1) rest h j →
      SeqRel R s ps k (it :: rest) i j

inductive PrefixRel (R : NT → List Param → Nat → Nat → Prop) (s : Src) (ps : List Param) :
    Nat → List Item → Nat → Nat → List Item → Nat → Prop where
  | refl {k is i} : PrefixRel R s ps k is i k is i
  | step {k0 it rest i0 i1 k is h} :
      S.ItemStep R s k0 ps it rest.head? i0 i1 →
      PrefixRel R s ps (k0 + 1) rest i1 k is h →
      PrefixRel R s ps k0 (it :: rest) i0 k is h

theorem itemMatch_mono {R1 R2 : NT → List Param → Nat → Nat → Prop}
    (hm : ∀ n ps i j, R1 n ps i j → R2 n ps i j)
    {s k ps it next h j} (h1 : S.ItemMatch R1 s k ps it next h j) :
    S.ItemMatch R2 s k ps it next h j := by
  cases it with
  | sym x o =>
    cases x with
    | t _ => exact h1
    | nt n args =>
      obtain ⟨hk, hc, hr⟩ := h1
      refine ⟨hk, hc, ?_⟩
      cases hem : (altsOf A.cx A.g n).isEmpty <;>
        simp only [hem, Bool.not_false, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hr ⊢
      · exact hm _ _ _ _ hr
      · exact hr
  | butNot base ex =>
    cases base with
    | t _ => exact h1
    | nt n args =>
      obtain ⟨hk, hex, hr⟩ := h1
      refine ⟨hk, hex, ?_⟩
      cases hem : (altsOf A.cx A.g n).isEmpty <;>
        simp only [hem, Bool.not_false, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hr ⊢
      · exact hm _ _ _ _ hr
      · exact hr
  | phrase _ => exact h1
  | _ => cases h1

theorem itemStep_mono {R1 R2 : NT → List Param → Nat → Nat → Prop}
    (hm : ∀ n ps i j, R1 n ps i j → R2 n ps i j)
    {s k ps it next h j} (h1 : S.ItemStep R1 s k ps it next h j) :
    S.ItemStep R2 s k ps it next h j := by
  cases it with
  | sym x o =>
    rcases h1 with ha | hm1
    · exact Or.inl ha
    · exact Or.inr (S.itemMatch_mono hm hm1)
  | butNot _ _ | phrase _ =>
    dsimp only [ItemStep] at h1 ⊢
    exact S.itemMatch_mono hm h1
  | _ => exact h1

theorem seqRel_mono {R1 R2 : NT → List Param → Nat → Nat → Prop}
    (hm : ∀ n ps i j, R1 n ps i j → R2 n ps i j)
    {s ps k is i j} (h : S.SeqRel R1 s ps k is i j) :
    S.SeqRel R2 s ps k is i j := by
  induction h with
  | nil => exact .nil
  | cons hs _ ih => exact .cons (S.itemStep_mono hm hs) ih

theorem prefixRel_mono {R1 R2 : NT → List Param → Nat → Nat → Prop}
    (hm : ∀ n ps i j, R1 n ps i j → R2 n ps i j)
    {s ps k0 is0 i0 k is h} (hp : S.PrefixRel R1 s ps k0 is0 i0 k is h) :
    S.PrefixRel R2 s ps k0 is0 i0 k is h := by
  induction hp with
  | refl => exact .refl
  | step hs _ ih => exact .step (S.itemStep_mono hm hs) ih

theorem itemMatch_ofKey_paramBits {c : Bool} {M : Key → Nat → Prop} {ps1 ps2 : List Param}
    (hp : paramBits ps1 = paramBits ps2)
    {s k it next h j} (hm : S.ItemMatch (S.OfKey c M) s k ps1 it next h j) :
    S.ItemMatch (S.OfKey c M) s k ps2 it next h j := by
  have hc := contains_eq_of_paramBits hp
  cases it with
  | sym x o =>
    cases x with
    | t _ => exact hm
    | nt m args => simp only [ItemMatch, applyArgs_eq_of_contains hc] at hm ⊢; exact hm
  | butNot base ex =>
    cases base with
    | t _ => exact ⟨hm.1, fun hx => hm.2 ((S.exclHolds_paramBits hp).mpr hx)⟩
    | nt m args =>
      obtain ⟨hk0, hex0, hr0⟩ := hm
      refine ⟨hk0, fun hx => hex0 ((S.exclHolds_paramBits hp).mpr hx), ?_⟩
      simp only [applyArgs_eq_of_contains hc] at hr0 ⊢; exact hr0
  | _ => exact hm

theorem itemStep_ofKey_paramBits {c : Bool} {M : Key → Nat → Prop} {ps1 ps2 : List Param}
    (hp : paramBits ps1 = paramBits ps2)
    {s k it next h j} (hs : S.ItemStep (S.OfKey c M) s k ps1 it next h j) :
    S.ItemStep (S.OfKey c M) s k ps2 it next h j := by
  cases it with
  | sym x o =>
    rcases hs with ha | hm
    · exact Or.inl ha
    · exact Or.inr (S.itemMatch_ofKey_paramBits hp hm)
  | butNot _ _ | phrase _ =>
    dsimp only [ItemStep] at hs ⊢
    exact S.itemMatch_ofKey_paramBits hp hs
  | _ => exact hs

theorem seqRel_ofKey_paramBits {c : Bool} {M : Key → Nat → Prop} {ps1 ps2 : List Param}
    (hp : paramBits ps1 = paramBits ps2)
    {s k is i j} (hsr : S.SeqRel (S.OfKey c M) s ps1 k is i j) :
    S.SeqRel (S.OfKey c M) s ps2 k is i j := by
  induction hsr with
  | nil => exact .nil
  | cons hs _ ih => exact .cons (S.itemStep_ofKey_paramBits hp hs) ih

theorem prefixRel_ofKey_paramBits {c : Bool} {M : Key → Nat → Prop} {ps1 ps2 : List Param}
    (hp : paramBits ps1 = paramBits ps2)
    {s k0 is0 i0 k is h} (hpr : S.PrefixRel (S.OfKey c M) s ps1 k0 is0 i0 k is h) :
    S.PrefixRel (S.OfKey c M) s ps2 k0 is0 i0 k is h := by
  induction hpr with
  | refl => exact .refl
  | step hs _ ih => exact .step (S.itemStep_ofKey_paramBits hp hs) ih

private theorem prefixRel_snoc_aux (S : AlphaSpec B A size) {R : NT → List Param → Nat → Nat → Prop}
    {s : Src} {ps : List Param} {k0 : Nat} {is0 : List Item} {i0 k : Nat} {is1 : List Item} {h : Nat}
    (hp : S.PrefixRel R s ps k0 is0 i0 k is1 h) :
    ∀ {it rest h'}, is1 = it :: rest → S.ItemStep R s k ps it rest.head? h h' →
      S.PrefixRel R s ps k0 is0 i0 (k + 1) rest h' := by
  induction hp with
  | refl => intro it rest h' his hs; subst his; exact .step hs .refl
  | step hs0 _ ih => intro it rest h' his hs; exact .step hs0 (ih his hs)

theorem prefixRel_snoc (S : AlphaSpec B A size) {R : NT → List Param → Nat → Nat → Prop}
    {s : Src} {ps : List Param} {k0 : Nat} {is0 : List Item} {i0 k : Nat}
    {it : Item} {rest : List Item} {h h' : Nat}
    (hp : S.PrefixRel R s ps k0 is0 i0 k (it :: rest) h)
    (hs : S.ItemStep R s k ps it rest.head? h h') :
    S.PrefixRel R s ps k0 is0 i0 (k + 1) rest h' :=
  prefixRel_snoc_aux S hp rfl hs

theorem seqRel_iff_seqWith (S : AlphaSpec B A size) {allow : NT → List Param → Nat → Src → Prop}
    {s : Src} {ps : List Param} :
    ∀ {k : Nat} {is : List Item} {i j : Nat},
      S.SeqRel (S.SpanOfAllow allow) s ps k is i j ↔
      ∃ m ts, S.SeqWith allow s ps k is i j m ts
  | k, [], i, j => by
    constructor
    · intro h; cases h; exact ⟨[], [], .nil⟩
    · rintro ⟨_, _, h⟩; cases h; exact .nil
  | k, it :: rest, i, j => by
    constructor
    · intro h
      cases h with
      | cons hs hrest =>
        obtain ⟨mr, tsr, hsr⟩ := (seqRel_iff_seqWith S).mp hrest
        cases it with
        | sym x o =>
          rcases hs with ⟨rfl, rfl⟩ | hm
          · exact ⟨false :: mr, tsr, .absent hsr⟩
          · cases x with
            | t tm => exact ⟨_, _, .term hm hsr⟩
            | nt n args =>
              obtain ⟨hk, hc, hr⟩ := hm
              have hch := (S.condOpt_head rest i _).mp hc
              cases hem : (altsOf A.cx A.g n).isEmpty
              · simp only [hem, Bool.not_false, ↓reduceIte] at hr
                obtain ⟨t, hder⟩ := hr
                exact ⟨_, _, .nt hem hder hk hch hsr⟩
              · simp only [hem, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hr
                exact ⟨_, _, .leaf hem hr hk hch hsr⟩
        | butNot base ex =>
          cases base with
          | t tm => exact ⟨_, _, .butNotT hs.1 hs.2 hsr⟩
          | nt n args =>
            obtain ⟨hk, hex, hr⟩ := hs
            cases hem : (altsOf A.cx A.g n).isEmpty
            · simp only [hem, Bool.not_false, ↓reduceIte] at hr
              obtain ⟨t, hder⟩ := hr
              exact ⟨_, _, .butNotN hem hder hk hex hsr⟩
            · simp only [hem, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hr
              exact ⟨_, _, .butNotLeaf hem hr hk hex hsr⟩
        | phrase p => exact ⟨_, _, .phrase hs hsr⟩
        | lookahead l => obtain ⟨rfl, hl⟩ := hs; exact ⟨_, _, .look hl hsr⟩
        | noLT => obtain ⟨rfl, hnl⟩ := hs; exact ⟨_, _, .noLT hnl hsr⟩
        | empty => subst hs; exact ⟨_, _, .empty hsr⟩
        | onlyIf c => subst hs; exact ⟨_, _, .onlyIf hsr⟩
    · rintro ⟨m, ts, hseq⟩
      cases hseq with
      | absent hsr => exact .cons (Or.inl ⟨rfl, rfl⟩) ((seqRel_iff_seqWith S).mpr ⟨_, _, hsr⟩)
      | term ht hsr => exact .cons (Or.inr ht) ((seqRel_iff_seqWith S).mpr ⟨_, _, hsr⟩)
      | nt hne hd hk hch hsr =>
        refine .cons (Or.inr ⟨hk, (S.condOpt_head rest i _).mpr hch, ?_⟩) ((seqRel_iff_seqWith S).mpr ⟨_, _, hsr⟩)
        simp only [hne, Bool.not_false, ↓reduceIte]; exact ⟨_, hd⟩
      | leaf he hl hk hch hsr =>
        refine .cons (Or.inr ⟨hk, (S.condOpt_head rest i _).mpr hch, ?_⟩) ((seqRel_iff_seqWith S).mpr ⟨_, _, hsr⟩)
        simp [he, hl]
      | butNotT ht hex hsr => exact .cons ⟨ht, hex⟩ ((seqRel_iff_seqWith S).mpr ⟨_, _, hsr⟩)
      | butNotN hne hd hk hex hsr =>
        refine .cons ⟨hk, hex, ?_⟩ ((seqRel_iff_seqWith S).mpr ⟨_, _, hsr⟩)
        simp only [hne, Bool.not_false, ↓reduceIte]; exact ⟨_, hd⟩
      | butNotLeaf he hl hk hex hsr =>
        refine .cons ⟨hk, hex, ?_⟩ ((seqRel_iff_seqWith S).mpr ⟨_, _, hsr⟩)
        simp [he, hl]
      | phrase hph hsr => exact .cons hph ((seqRel_iff_seqWith S).mpr ⟨_, _, hsr⟩)
      | look hlk hsr => exact .cons ⟨rfl, hlk⟩ ((seqRel_iff_seqWith S).mpr ⟨_, _, hsr⟩)
      | noLT hnl hsr => exact .cons ⟨rfl, hnl⟩ ((seqRel_iff_seqWith S).mpr ⟨_, _, hsr⟩)
      | empty hsr => exact .cons rfl ((seqRel_iff_seqWith S).mpr ⟨_, _, hsr⟩)
      | onlyIf hsr => exact .cons rfl ((seqRel_iff_seqWith S).mpr ⟨_, _, hsr⟩)

theorem derivesWith_of_seqRel (hok : parseTablesOk = true)
    {allow : NT → List Param → Nat → Src → Prop}
    {n : NT} {ps : List Param} {i j : Nat} {s : Src}
    (hs : s ∈ altsOf A.cx A.g n)
    (hal : allow n ps i s)
    (hgrd : s.alt.guard.all (Guard.holds ps) = true)
    (hseq : S.SeqRel (S.SpanOfAllow allow) s ps 0 s.alt.rhs i j) :
    ∃ t, S.DerivesWith allow n ps i j t := by
  obtain ⟨m, ts, hsw⟩ := S.seqRel_iff_seqWith.mp hseq
  have hs' : s ∈ Ecma.Spec.gl.alts A.cx A.g n := by rw [← altsOf_eq hok]; exact hs
  have hopts := (alt_lhs_and_opts hok hs').2
  have hm : m ∈ masks s.alt.opts := hopts ▸ S.seqWith_masks hsw
  obtain ⟨hpeq, id, _, hid, _⟩ := prodIdOf_spec hok hs' hm
  exact ⟨.node n id s ps i j m ts, .node s hs hal hgrd (hpeq.trans hid) hsw⟩

/-! ## `SpecOpen`, `SpecPrefix`, `SpecHit` (furthest-match specification for `st.far`) -/

mutual
inductive SpecOpen (goal : NT) (goalPs : List Param) : NT → List Param → Nat → Prop where
  | root : SpecOpen goal goalPs goal goalPs 0
  | nt {s ps k n args o is i} :
      SpecPrefix goal goalPs s ps k (.sym (.nt n args) o :: is) i →
      (altsOf A.cx A.g n).isEmpty = false →
      SpecOpen goal goalPs n (applyArgs ps args) i
  | butNotN {s ps k n args ex is i} :
      SpecPrefix goal goalPs s ps k (.butNot (.nt n args) ex :: is) i →
      (altsOf A.cx A.g n).isEmpty = false →
      SpecOpen goal goalPs n (applyArgs ps args) i

inductive SpecPrefix (goal : NT) (goalPs : List Param) :
    Src → List Param → Nat → List Item → Nat → Prop where
  | enter {n ps i} (s : Src) :
      SpecOpen goal goalPs n ps i →
      s ∈ altsOf A.cx A.g n →
      s.alt.guard.all (Guard.holds ps) = true →
      SpecPrefix goal goalPs s ps 0 s.alt.rhs i
  | step {s ps k it rest i h} :
      SpecPrefix goal goalPs s ps k (it :: rest) i →
      S.ItemStep (S.SpanOfAllow (fun _ _ _ _ => True)) s k ps it rest.head? i h →
      SpecPrefix goal goalPs s ps (k + 1) rest h
end

inductive SpecHit (goal : NT) (goalPs : List Param) : Nat → Prop where
  | zero : SpecHit goal goalPs 0
  | matchAt {s ps k it rest i j} :
      S.SpecPrefix goal goalPs s ps k (it :: rest) i →
      S.ItemMatch (S.SpanOfAllow (fun _ _ _ _ => True)) s k ps it rest.head? i j →
      SpecHit goal goalPs j

private theorem step_hit_of_prefix_hit {goal : NT} {goalPs : List Param}
    {s : Src} {ps : List Param} {k : Nat} {it : Item} {rest : List Item} {i h : Nat}
    (hp : S.SpecPrefix goal goalPs s ps k (it :: rest) i)
    (ih : S.SpecHit goal goalPs i)
    (hs : S.ItemStep (S.SpanOfAllow (fun _ _ _ _ => True)) s k ps it rest.head? i h) :
    S.SpecHit goal goalPs h := by
  cases it with
  | sym x o =>
    rcases hs with ⟨_, rfl⟩ | hm
    · exact ih
    · exact .matchAt hp hm
  | butNot _ _ | phrase _ => exact .matchAt hp hs
  | lookahead _ | noLT => obtain ⟨rfl, _⟩ := hs; exact ih
  | empty | onlyIf _ => subst hs; exact ih

mutual
theorem specOpen_hit (S : AlphaSpec B A size) {goal : NT} {goalPs : List Param}
    {n : NT} {ps : List Param} {i : Nat} (ho : S.SpecOpen goal goalPs n ps i) :
    S.SpecHit goal goalPs i :=
  match ho with
  | .root => .zero
  | .nt hp _ => specPrefix_hit S hp
  | .butNotN hp _ => specPrefix_hit S hp

theorem specPrefix_hit (S : AlphaSpec B A size) {goal : NT} {goalPs : List Param}
    {s : Src} {ps : List Param} {k : Nat} {is : List Item} {h : Nat}
    (hpr : S.SpecPrefix goal goalPs s ps k is h) :
    S.SpecHit goal goalPs h :=
  match hpr with
  | .enter _ ho _ _ => specOpen_hit S ho
  | .step hp hs => S.step_hit_of_prefix_hit hp (specPrefix_hit S hp) hs
end

inductive OpenFromKey (R : NT → List Param → Nat → Nat → Prop) (k0 : Key) : Key → Prop where
  | root : OpenFromKey R k0 k0
  | child {k1 n ps i s k it rest h m args} :
      OpenFromKey R k0 k1 →
      key A false n ps i = k1 →
      s ∈ altsUnder A n ps →
      S.PrefixRel R s ps 0 s.alt.rhs i k (it :: rest) h →
      (altsOf A.cx A.g m).isEmpty = false →
      ((∃ o, it = .sym (.nt m args) o) ∨ (∃ ex, it = .butNot (.nt m args) ex)) →
      OpenFromKey R k0 (key A false m (applyArgs ps args) h)

def HitFromKey (R : NT → List Param → Nat → Nat → Prop) (k0 : Key) (j : Nat) : Prop :=
  ∃ k1 n ps i s k it rest h,
    S.OpenFromKey R k0 k1 ∧
    key A false n ps i = k1 ∧
    s ∈ altsUnder A n ps ∧
    S.PrefixRel R s ps 0 s.alt.rhs i k (it :: rest) h ∧
    S.ItemMatch R s k ps it rest.head? h j

theorem openFromKey_trans {R : NT → List Param → Nat → Nat → Prop} {k0 k1 k2 : Key}
    (h01 : S.OpenFromKey R k0 k1) (h12 : S.OpenFromKey R k1 k2) :
    S.OpenFromKey R k0 k2 := by
  induction h12 with
  | root => exact h01
  | child _ hk hs hp hne hkind ih => exact .child ih hk hs hp hne hkind

theorem hitFromKey_of_open {R : NT → List Param → Nat → Nat → Prop} {k0 k1 : Key} {j : Nat}
    (h01 : S.OpenFromKey R k0 k1) (hh : S.HitFromKey R k1 j) :
    S.HitFromKey R k0 j := by
  obtain ⟨k2, n, ps, i, s, k, it, rest, h, h12, hk, hs, hp, hm⟩ := hh
  exact ⟨k2, n, ps, i, s, k, it, rest, h, S.openFromKey_trans h01 h12, hk, hs, hp, hm⟩

mutual
theorem specOpen_to_openFromKey (S : AlphaSpec B A size) {goal : NT} {goalPs : List Param}
    {n : NT} {ps : List Param} {i : Nat} (ho : S.SpecOpen goal goalPs n ps i) :
    S.OpenFromKey (S.SpanOfAllow (fun _ _ _ _ => True)) (key A false goal goalPs 0) (key A false n ps i) :=
  match ho with
  | .root => .root
  | .nt hp hne => by
    obtain ⟨n0, ps0, i0, ho0, rfl, hs0, hpref0⟩ := specPrefix_to_prefixRel S hp
    exact .child ho0 rfl hs0 hpref0 hne (Or.inl ⟨_, rfl⟩)
  | .butNotN hp hne => by
    obtain ⟨n0, ps0, i0, ho0, rfl, hs0, hpref0⟩ := specPrefix_to_prefixRel S hp
    exact .child ho0 rfl hs0 hpref0 hne (Or.inr ⟨_, rfl⟩)

theorem specPrefix_to_prefixRel (S : AlphaSpec B A size) {goal : NT} {goalPs : List Param}
    {s : Src} {ps : List Param} {k : Nat} {is : List Item} {h : Nat}
    (hpr : S.SpecPrefix goal goalPs s ps k is h) :
    ∃ n0 ps0 i0,
      S.OpenFromKey (S.SpanOfAllow (fun _ _ _ _ => True)) (key A false goal goalPs 0) (key A false n0 ps0 i0) ∧
      ps0 = ps ∧
      s ∈ altsUnder A n0 ps0 ∧
      S.PrefixRel (S.SpanOfAllow (fun _ _ _ _ => True)) s ps0 0 s.alt.rhs i0 k is h :=
  match hpr with
  | .enter s ho hs hgrd =>
    ⟨_, _, _, specOpen_to_openFromKey S ho, rfl, (mem_altsUnder_iff A _ _ s).mpr ⟨hs, hgrd⟩, .refl⟩
  | .step hp hs => by
    obtain ⟨n0, ps0, i0, ho0, rfl, hs0, hpref0⟩ := specPrefix_to_prefixRel S hp
    exact ⟨n0, ps0, i0, ho0, rfl, hs0, S.prefixRel_snoc hpref0 hs⟩
end

theorem specHit_to_hitFromKey {goal : NT} {goalPs : List Param} {j : Nat}
    (hh : S.SpecHit goal goalPs j) :
    j = 0 ∨ S.HitFromKey (S.SpanOfAllow (fun _ _ _ _ => True)) (key A false goal goalPs 0) j := by
  cases hh with
  | zero => exact Or.inl rfl
  | matchAt hp hm =>
    obtain ⟨n0, ps0, i0, ho0, rfl, hs0, hpref0⟩ := S.specPrefix_to_prefixRel hp
    exact Or.inr ⟨_, n0, ps0, i0, _, _, _, _, _, ho0, rfl, hs0, hpref0, hm⟩

/-! ## `MemoInv` and Tarski `PostFix` invariants -/

structure MemoInv (farTrack : Option (NT × List Param)) (st : St T) : Prop where
  inv : S.Inv st
  memo_sound : ∀ (k : Key) (e : Entry), st.memo[k]? = some e →
    ∀ c n ps i, key A c n ps i = k → ∀ j, e.ends.mem j = true → ∃ t, S.ModeDerives c n ps i j t
  memo_complete : ∀ (k : Key) (e : Entry), st.memo[k]? = some e → e.final = true →
    ∀ c n ps i, key A c n ps i = k → ∀ j t, S.ModeDerives c n ps i j t → e.ends.mem j = true
  active_in_memo : ∀ (k : Key), st.active.contains k = true → (st.memo[k]?).isSome = true
  active_provisional : ∀ (k : Key) (e : Entry), st.active.contains k = true → st.memo[k]? = some e → e.final = false
  first_spec : ∀ (k : Key) optS, st.first[k]? = some optS →
    ∀ n ps i, key A false n ps i = k →
      match optS with
      | some s => S.IsFirstAlt n ps i s
      | none => ∀ s' ∈ altsUnder A n ps, ¬ ∃ h m kids, S.SeqWith (fun _ _ _ _ => True) s' ps 0 s'.alt.rhs i h m kids
  far_sound : ∀ goal goalPs, farTrack = some (goal, goalPs) →
    S.SpecHit goal goalPs st.far ∧ ∀ (k : Key) (e : Entry), st.memo[k]? = some e → S.SpecHit goal goalPs e.far
  far_complete : orderedBy A.cx A.g = false →
    ∀ (k : Key) (e : Entry), st.memo[k]? = some e → e.final = true →
      ∀ j, S.HitFromKey (S.SpanOfAllow (fun _ _ _ _ => True)) k j → j ≤ e.far

theorem MemoInv.drop_far {S : AlphaSpec B A size} {ft : Option (NT × List Param)} {st : St T} (h : S.MemoInv ft st) :
    S.MemoInv none st :=
  { inv := h.inv
    memo_sound := h.memo_sound
    memo_complete := h.memo_complete
    active_in_memo := h.active_in_memo
    active_provisional := h.active_provisional
    first_spec := h.first_spec
    far_sound := fun _ _ hnone => nomatch hnone
    far_complete := h.far_complete }

theorem MemoInv.fresh (S : AlphaSpec B A size) {st : St T} (hinv : S.Inv st)
    (hm : st.memo = {}) (ha : st.active = {}) (hf : st.first = {}) (hfar : st.far = 0)
    (ft : Option (NT × List Param)) :
    S.MemoInv ft st :=
  { inv := hinv
    memo_sound := fun k _ hk => by rw [hm, hm_empty] at hk; cases hk
    memo_complete := fun k _ hk => by rw [hm, hm_empty] at hk; cases hk
    active_in_memo := fun k hk => by rw [ha, hs_empty] at hk; cases hk
    active_provisional := fun k _ hk => by rw [ha, hs_empty] at hk; cases hk
    first_spec := fun k _ hk => by rw [hf, hm_empty] at hk; cases hk
    far_sound := fun _ _ _ => ⟨hfar ▸ .zero, fun k _ hk => by rw [hm, hm_empty] at hk; cases hk⟩
    far_complete := fun _ k _ hk => by rw [hm, hm_empty] at hk; cases hk }

theorem MemoInv.of_alpha_eq {S : AlphaSpec B A size} {ft : Option (NT × List Param)} {st st' : St T}
    (h : S.MemoInv ft st) (hi' : S.Inv st')
    (hm : st'.memo = st.memo) (ha : st'.active = st.active)
    (hfi : st'.first = st.first) (hfar : st'.far = st.far) :
    S.MemoInv ft st' :=
  { inv := hi'
    memo_sound := hm ▸ h.memo_sound
    memo_complete := hm ▸ h.memo_complete
    active_in_memo := hm ▸ ha ▸ h.active_in_memo
    active_provisional := hm ▸ ha ▸ h.active_provisional
    first_spec := hfi ▸ h.first_spec
    far_sound := hm ▸ hfar ▸ h.far_sound
    far_complete := hm ▸ h.far_complete }

theorem MemoInv.of_hit {S : AlphaSpec B A size} {ft : Option (NT × List Param)} {j : Nat} {st st' : St T}
    (h : S.MemoInv ft st) (hi' : S.Inv st')
    (hm : st'.memo = st.memo) (ha : st'.active = st.active)
    (hfi : st'.first = st.first) (hfar : st'.far = max st.far j)
    (hj : ∀ g gp, ft = some (g, gp) → S.SpecHit g gp j) :
    S.MemoInv ft st' :=
  { inv := hi'
    memo_sound := hm ▸ h.memo_sound
    memo_complete := hm ▸ h.memo_complete
    active_in_memo := hm ▸ ha ▸ h.active_in_memo
    active_provisional := hm ▸ ha ▸ h.active_provisional
    first_spec := hfi ▸ h.first_spec
    far_sound := fun g gp hft => by
      obtain ⟨hsf, hmf⟩ := h.far_sound g gp hft
      refine ⟨?_, hm ▸ hmf⟩
      rw [hfar]
      by_cases hle : st.far ≤ j
      · rw [Nat.max_eq_right hle]; exact hj g gp hft
      · rw [Nat.max_eq_left (by omega)]; exact hsf
    far_complete := hm ▸ h.far_complete }

theorem MemoInv.of_tick {S : AlphaSpec B A size} {ft : Option (NT × List Param)} {st st' : St T}
    (h : S.MemoInv ft st) {u : Unit} (hrun : tick.run st = .ok (u, st')) :
    S.MemoInv ft st' ∧ st'.memo = st.memo ∧ st'.active = st.active ∧ st'.reads = st.reads ∧
    st'.fwd = st.fwd ∧ st'.first = st.first ∧ st'.far = st.far := by
  unfold tick at hrun
  obtain ⟨s0, st0, hg, hr1⟩ := sm_bind_ok hrun
  obtain ⟨hs0, hst0⟩ := sm_pure_ok hg
  subst s0 st0
  cases hz : st.steps == 0 with
  | true =>
    rw [hz] at hr1; simp only [↓reduceIte] at hr1
    obtain ⟨_, _, ht, _⟩ := sm_bind_ok hr1; cases ht
  | false =>
    rw [hz] at hr1; simp only [Bool.false_eq_true, ↓reduceIte, sm_run_set] at hr1
    cases hr1
    exact ⟨MemoInv.of_alpha_eq h (S.inv_tick st _ h.inv) rfl rfl rfl rfl,
      rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem MemoInv.insert_provisional {S : AlphaSpec B A size} {ft : Option (NT × List Param)} {st : St T}
    (h : S.MemoInv ft st) (hok : parseTablesOk = true)
    {c : Bool} {n : NT} {ps : List Param} {i : Nat} {cur : Ends} {farVal : Nat}
    (_ : ∀ e0, st.memo[key A c n ps i]? = some e0 → e0.final = false)
    (hsound : ∀ j, cur.mem j = true → ∃ t, S.ModeDerives c n ps i j t)
    (hfarVal : ∀ g gp, ft = some (g, gp) → S.SpecHit g gp farVal) :
    S.MemoInv ft { st with memo := st.memo.insert (key A c n ps i) ⟨cur, false, farVal⟩ } :=
  let k := key A c n ps i
  { inv := S.inv_mono_memo st _ _ _ _ _ _ h.inv
    memo_sound := fun k' e' hk' c' n' ps' i' heq j hj => by
      by_cases hkk : k = k'
      · subst hkk; rw [hm_insert_eq] at hk'; cases hk'
        exact (S.modeDerives_key_congr hok heq.symm j).mp (hsound j hj)
      · rw [hm_insert_ne _ _ hkk] at hk'
        exact h.memo_sound k' e' hk' c' n' ps' i' heq j hj
    memo_complete := fun k' e' hk' hfin => by
      by_cases hkk : k = k'
      · subst hkk; rw [hm_insert_eq] at hk'; cases hk'; cases hfin
      · rw [hm_insert_ne _ _ hkk] at hk'; exact h.memo_complete k' e' hk' hfin
    active_in_memo := fun k' ha => by
      by_cases hkk : k = k'
      · subst hkk; rw [hm_insert_eq]; rfl
      · rw [hm_insert_ne _ _ hkk]; exact h.active_in_memo k' ha
    active_provisional := fun k' e' ha hk' => by
      by_cases hkk : k = k'
      · subst hkk; rw [hm_insert_eq] at hk'; cases hk'; rfl
      · rw [hm_insert_ne _ _ hkk] at hk'; exact h.active_provisional k' e' ha hk'
    first_spec := h.first_spec
    far_sound := fun g gp hft => by
      obtain ⟨hsf, hmf⟩ := h.far_sound g gp hft
      refine ⟨hsf, fun k' e' hk' => ?_⟩
      by_cases hkk : k = k'
      · subst hkk; rw [hm_insert_eq] at hk'; cases hk'; exact hfarVal g gp hft
      · rw [hm_insert_ne _ _ hkk] at hk'; exact hmf k' e' hk'
    far_complete := fun hord k' e' hk' hfin => by
      by_cases hkk : k = k'
      · subst hkk; rw [hm_insert_eq] at hk'; cases hk'; cases hfin
      · rw [hm_insert_ne _ _ hkk] at hk'; exact h.far_complete hord k' e' hk' hfin }

def OneStepClosed (c : Bool) (M : Key → Nat → Prop) (k1 : Key) : Prop :=
  ∀ n ps i, key A c n ps i = k1 →
    ∀ s ∈ altsOf A.cx A.g n, S.CommitAllow c n ps i s → s.alt.guard.all (Guard.holds ps) = true →
      ∀ j, S.SeqRel (S.OfKey c M) s ps 0 s.alt.rhs i j → M k1 j

mutual
theorem global_postFix_complete (S : AlphaSpec B A size) {c : Bool} {M : Key → Nat → Prop}
    (hcl : ∀ k1, S.OneStepClosed c M k1)
    {n : NT} {ps : List Param} {i j : Nat} {t : DTree}
    (hd : S.DerivesWith (S.CommitAllow c) n ps i j t) :
    M (key A c n ps i) j :=
  match hd with
  | .node s hs hal hgrd _ hseq =>
    hcl (key A c n ps i) n ps i rfl s hs hal hgrd j (global_postFix_complete_seq S hcl hseq)

theorem global_postFix_complete_seq (S : AlphaSpec B A size) {c : Bool} {M : Key → Nat → Prop}
    (hcl : ∀ k1, S.OneStepClosed c M k1)
    {s : Src} {ps : List Param} {k : Nat} {is : List Item} {i j : Nat} {m : List Bool} {ts : List DTree}
    (hs : S.SeqWith (S.CommitAllow c) s ps k is i j m ts) :
    S.SeqRel (S.OfKey c M) s ps k is i j :=
  match hs with
  | .nil => .nil
  | .absent hr => .cons (Or.inl ⟨rfl, rfl⟩) (global_postFix_complete_seq S hcl hr)
  | .term ht hr => .cons (Or.inr ht) (global_postFix_complete_seq S hcl hr)
  | .nt hne hd hk hch hr =>
    .cons (Or.inr ⟨hk, (S.condOpt_head _ _ _).mpr hch, by simp [hne, OfKey, global_postFix_complete S hcl hd]⟩)
      (global_postFix_complete_seq S hcl hr)
  | .leaf he hl hk hch hr =>
    .cons (Or.inr ⟨hk, (S.condOpt_head _ _ _).mpr hch, by simp [he, hl]⟩)
      (global_postFix_complete_seq S hcl hr)
  | .butNotT ht hex hr => .cons ⟨ht, hex⟩ (global_postFix_complete_seq S hcl hr)
  | .butNotN hne hd hk hex hr =>
    .cons ⟨hk, hex, by simp [hne, OfKey, global_postFix_complete S hcl hd]⟩
      (global_postFix_complete_seq S hcl hr)
  | .butNotLeaf he hl hk hex hr =>
    .cons ⟨hk, hex, by simp [he, hl]⟩ (global_postFix_complete_seq S hcl hr)
  | .phrase hph hr => .cons hph (global_postFix_complete_seq S hcl hr)
  | .look hlk hr => .cons ⟨rfl, hlk⟩ (global_postFix_complete_seq S hcl hr)
  | .noLT hnl hr => .cons ⟨rfl, hnl⟩ (global_postFix_complete_seq S hcl hr)
  | .empty hr => .cons rfl (global_postFix_complete_seq S hcl hr)
  | .onlyIf hr => .cons rfl (global_postFix_complete_seq S hcl hr)
end

structure PostFix (c : Bool) (rs : Key → Bool) (st : St T)
    (V : Key → Prop) (M : Key → Nat → Prop) : Prop where
  rs_mode : ∀ k1, rs k1 = true → k1.2.2.2.2 = (c && orderedBy A.cx A.g)
  rs_sub_active : ∀ k1, rs k1 = true → st.active.contains k1 = true
  rs_upper : ∀ k1, rs k1 = true → ∃ e1, st.memo[k1]? = some e1 ∧ ∀ j, M k1 j → e1.ends.mem j = true
  active_lower : ∀ k1 e1, st.active.contains k1 = true → st.memo[k1]? = some e1 →
    ∀ j, e1.ends.mem j = true → M k1 j
  closed_outside : ∀ k1, rs k1 = false → S.OneStepClosed c M k1
  far_visited : orderedBy A.cx A.g = false → ∀ k1, V k1 → rs k1 = false →
    (∀ n ps i s k it rest h,
      key A false n ps i = k1 → s ∈ altsUnder A n ps →
      S.PrefixRel (S.OfKey false M) s ps 0 s.alt.rhs i k (it :: rest) h →
      (∀ j, S.ItemMatch (S.OfKey false M) s k ps it rest.head? h j → j ≤ st.far) ∧
      (∀ m args, (altsOf A.cx A.g m).isEmpty = false →
        ((∃ o, it = .sym (.nt m args) o) ∨ (∃ ex, it = .butNot (.nt m args) ex)) →
        V (key A false m (applyArgs ps args) h) ∨ rs (key A false m (applyArgs ps args) h) = true))

theorem postFix_top (S : AlphaSpec B A size) (c : Bool) (st : St T) :
    S.PostFix c (fun _ => false) st (fun _ => False) (fun _ _ => True) :=
  { rs_mode := fun _ h => nomatch h
    rs_sub_active := fun _ h => nomatch h
    rs_upper := fun _ h => nomatch h
    active_lower := fun _ _ _ _ _ _ => trivial
    closed_outside := fun _ _ _ _ _ _ _ _ _ _ _ _ => trivial
    far_visited := fun _ _ hv => nomatch hv }

theorem PostFix.mono_state {S : AlphaSpec B A size} {c : Bool} {rs : Key → Bool} {st st' : St T} {V : Key → Prop} {M : Key → Nat → Prop}
    (hp : S.PostFix c rs st V M)
    (hact : ∀ x, st'.active.contains x = st.active.contains x)
    (hmemo : ∀ x, st.active.contains x = true → st'.memo[x]? = st.memo[x]?)
    (hfar : st.far ≤ st'.far) :
    S.PostFix c rs st' V M :=
  { rs_mode := hp.rs_mode
    rs_sub_active := fun k1 hr => by rw [hact]; exact hp.rs_sub_active k1 hr
    rs_upper := fun k1 hr => by
      rw [hmemo k1 (hp.rs_sub_active k1 hr)]
      exact hp.rs_upper k1 hr
    active_lower := fun k1 e1 ha hm => by
      rw [hact] at ha; rw [hmemo k1 ha] at hm
      exact hp.active_lower k1 e1 ha hm
    closed_outside := hp.closed_outside
    far_visited := fun hord k1 hv hnr n ps i s k it rest h hk hs hpr => by
      obtain ⟨hjb, hch⟩ := hp.far_visited hord k1 hv hnr n ps i s k it rest h hk hs hpr
      exact ⟨fun j hj => Nat.le_trans (hjb j hj) hfar, hch⟩ }

theorem PostFix.inter {S : AlphaSpec B A size} {c : Bool} {rs1 rs2 : Key → Bool} {st : St T}
    {V1 V2 : Key → Prop} {M1 M2 : Key → Nat → Prop}
    (h1 : S.PostFix c rs1 st V1 M1) (h2 : S.PostFix c rs2 st V2 M2) :
    S.PostFix c (fun k => rs1 k || rs2 k) st (fun k => V1 k ∨ V2 k) (fun k j => M1 k j ∧ M2 k j) :=
  { rs_mode := fun k1 hr => by
      rcases (Bool.or_eq_true _ _).mp hr with hr1 | hr2
      · exact h1.rs_mode k1 hr1
      · exact h2.rs_mode k1 hr2
    rs_sub_active := fun k1 hr => by
      rcases (Bool.or_eq_true _ _).mp hr with hr1 | hr2
      · exact h1.rs_sub_active k1 hr1
      · exact h2.rs_sub_active k1 hr2
    rs_upper := fun k1 hr => by
      rcases (Bool.or_eq_true _ _).mp hr with hr1 | hr2
      · obtain ⟨e1, hm, hu⟩ := h1.rs_upper k1 hr1
        exact ⟨e1, hm, fun j hj => hu j hj.1⟩
      · obtain ⟨e2, hm, hu⟩ := h2.rs_upper k1 hr2
        exact ⟨e2, hm, fun j hj => hu j hj.2⟩
    active_lower := fun k1 e1 ha hm j hj =>
      ⟨h1.active_lower k1 e1 ha hm j hj, h2.active_lower k1 e1 ha hm j hj⟩
    closed_outside := fun k1 hnr n ps i hk s hs hal hgrd j hseq => by
      simp only [Bool.or_eq_false_iff] at hnr
      exact ⟨h1.closed_outside k1 hnr.1 n ps i hk s hs hal hgrd j
               (S.seqRel_mono (fun _ _ _ _ h => h.1) hseq),
             h2.closed_outside k1 hnr.2 n ps i hk s hs hal hgrd j
               (S.seqRel_mono (fun _ _ _ _ h => h.2) hseq)⟩
    far_visited := fun hord k1 hv hnr n ps i s k it rest h hk hs hpr => by
      simp only [Bool.or_eq_false_iff] at hnr
      rcases hv with hv1 | hv2
      · obtain ⟨hjb, hch⟩ := h1.far_visited hord k1 hv1 hnr.1 n ps i s k it rest h hk hs
          (S.prefixRel_mono (fun _ _ _ _ hm => hm.1) hpr)
        refine ⟨fun j hj => hjb j (S.itemMatch_mono (fun _ _ _ _ hm => hm.1) hj), fun m args hne hkind => ?_⟩
        rcases hch m args hne hkind with hv' | hr'
        · exact Or.inl (Or.inl hv')
        · exact Or.inr ((Bool.or_eq_true _ _).mpr (Or.inl hr'))
      · obtain ⟨hjb, hch⟩ := h2.far_visited hord k1 hv2 hnr.2 n ps i s k it rest h hk hs
          (S.prefixRel_mono (fun _ _ _ _ hm => hm.2) hpr)
        refine ⟨fun j hj => hjb j (S.itemMatch_mono (fun _ _ _ _ hm => hm.2) hj), fun m args hne hkind => ?_⟩
        rcases hch m args hne hkind with hv' | hr'
        · exact Or.inl (Or.inr hv')
        · exact Or.inr ((Bool.or_eq_true _ _).mpr (Or.inr hr')) }

/-! ## Specifications of `collectM`, `foldUnionM`, `admit`, `stepItem`, `forwardGo`, `ruleEnds` -/

theorem collectM_rel_spec {α β : Type} {Rel : α → β → Prop} {f : α → SM T (Option β)}
    {ft : Option (NT × List Param)}
    (hf : ∀ x st0, S.MemoInv ft st0 → ∀ r st1, (f x).run st0 = .ok (r, st1) →
      S.MemoInv ft st1 ∧ st1.memo = st0.memo ∧ st1.active = st0.active ∧ st1.reads = st0.reads ∧
      st1.fwd = st0.fwd ∧ st1.first = st0.first ∧ st1.far = st0.far ∧
      ((∃ y, r = some y ∧ Rel x y) ∨ (r = none ∧ ∀ y, ¬ Rel x y)))
    (hdet : ∀ x y1 y2, Rel x y1 → Rel x y2 → y1 = y2) :
    ∀ (xs : List α) (st : St T) (ys : List β) (st' : St T),
      S.MemoInv ft st →
      (collectM f xs).run st = .ok (ys, st') →
      S.MemoInv ft st' ∧ st'.memo = st.memo ∧ st'.active = st.active ∧ st'.reads = st.reads ∧
      st'.fwd = st.fwd ∧ st'.first = st.first ∧ st'.far = st.far ∧
      ∀ y, y ∈ ys ↔ ∃ x ∈ xs, Rel x y
  | [], st, ys, st', hinv, hrun => by
    unfold collectM at hrun
    obtain ⟨rfl, rfl⟩ := sm_pure_ok hrun
    exact ⟨hinv, rfl, rfl, rfl, rfl, rfl, rfl, fun y => by simp⟩
  | x :: rest, st, ys, st', hinv, hrun => by
    unfold collectM at hrun
    obtain ⟨r, st1, hx, hr1⟩ := sm_bind_ok hrun
    obtain ⟨rys, st2, hrest, hr2⟩ := sm_bind_ok hr1
    have ⟨hi1, hm1, ha1, hrd1, hfw1, hfi1, hfar1, hrel⟩ := hf x st hinv r st1 hx
    have ⟨hi2, hm2, ha2, hrd2, hfw2, hfi2, hfar2, hmem⟩ :=
      collectM_rel_spec hf hdet rest st1 rys st2 hi1 hrest
    obtain ⟨hys, hst2⟩ := sm_pure_ok hr2
    subst hys st2
    refine ⟨hi2, hm2.trans hm1, ha2.trans ha1, hrd2.trans hrd1, hfw2.trans hfw1,
      hfi2.trans hfi1, hfar2.trans hfar1, fun y => ?_⟩
    rcases hrel with ⟨y0, rfl, hry0⟩ | ⟨rfl, hno⟩
    · rw [List.mem_cons, hmem]
      constructor
      · rintro (rfl | ⟨x', hx', hr'⟩)
        · exact ⟨x, List.mem_cons_self, hry0⟩
        · exact ⟨x', List.mem_cons_of_mem _ hx', hr'⟩
      · rintro ⟨x', hx', hr'⟩
        rcases List.mem_cons.mp hx' with rfl | hx'
        · exact Or.inl (hdet x' y y0 hr' hry0)
        · exact Or.inr ⟨x', hx', hr'⟩
    · rw [hmem]
      constructor
      · rintro ⟨x', hx', hr'⟩; exact ⟨x', List.mem_cons_of_mem _ hx', hr'⟩
      · rintro ⟨x', hx', hr'⟩
        rcases List.mem_cons.mp hx' with rfl | hx'
        · exact absurd hr' (hno y)
        · exact ⟨x', hx', hr'⟩

structure RecSpec (c : Bool) (ft : Option (NT × List Param))
    (rec : NT → List Param → Nat → SM T Ends) : Prop where
  run_spec : ∀ n ps h st es st',
    S.MemoInv ft st →
    (c = true → ∀ k_a, st.active.contains k_a = true → k_a.2.2.2.2 = (true && orderedBy A.cx A.g)) →
    (∀ g gp, ft = some (g, gp) → S.SpecOpen g gp n ps h) →
    (rec n ps h).run st = .ok (es, st') →
    S.MemoInv ft st' ∧
    (∀ x, st'.active.contains x = st.active.contains x) ∧
    (∀ x, st.active.contains x = true → st'.memo[x]? = st.memo[x]?) ∧
    (∀ (x : Key) (e : Entry), st.memo[x]? = some e → e.final = true → st'.memo[x]? = some e) ∧
    st'.fwd = st.fwd ∧
    st.far ≤ st'.far ∧
    (∀ j, es.mem j = true → S.SpanOfAllow (S.CommitAllow c) n ps h j) ∧
    ∃ rs V M,
      (∀ x, st'.reads.contains x = (st.reads.contains x || rs x)) ∧
      S.PostFix c rs st' V M ∧
      (∀ j, M (key A c n ps h) j → es.mem j = true) ∧
      (orderedBy A.cx A.g = false → V (key A false n ps h) ∨ rs (key A false n ps h) = true)

theorem admit_spec {ft : Option (NT × List Param)}
    (lhs n : NT) (next : Option Item) (h : Nat) (js : Ends)
    (st : St T) (out : Ends) (st' : St T)
    (hinv : S.MemoInv ft st)
    (hrun : (admit A lhs n next h js).run st = .ok (out, st')) :
    S.MemoInv ft st' ∧ st'.memo = st.memo ∧ st'.active = st.active ∧ st'.reads = st.reads ∧
    st'.fwd = st.fwd ∧ st'.first = st.first ∧ st'.far = st.far ∧
    ∀ j, out.mem j = true ↔ (js.mem j = true ∧ A.keep lhs n j = true ∧ S.CondOpt next h j) := by
  have hkeepOnly : ∀ j, (if A.keepAll lhs n then js else js.filter (A.keep lhs n)).mem j = true ↔
      (js.mem j = true ∧ A.keep lhs n j = true) := by
    intro j
    cases hka : A.keepAll lhs n
    · simp [Ends.mem_filter, Bool.and_eq_true]
    · simp [S.keepAll_sound lhs n j hka]
  cases next with
  | none =>
    unfold admit at hrun
    obtain ⟨hout, rfl⟩ := sm_pure_ok hrun; subst hout
    refine ⟨hinv, rfl, rfl, rfl, rfl, rfl, rfl, fun j => ?_⟩
    simp [CondOpt, hkeepOnly j]
  | some nx =>
    cases nx with
    | onlyIf cd =>
      unfold admit at hrun
      have hp : ∀ j st0, S.MemoInv ft st0 → ∀ b st1,
          (do let r ← A.cond cd h j; pure (A.keep lhs n j && r)).run st0 = .ok (b, st1) →
          S.MemoInv ft st1 ∧ st1.memo = st0.memo ∧ st1.active = st0.active ∧ st1.reads = st0.reads ∧
          st1.fwd = st0.fwd ∧ st1.first = st0.first ∧ st1.far = st0.far ∧
          (b = true ↔ (A.keep lhs n j = true ∧ S.Cond cd h j)) := by
        intro j st0 hi0 b st1 hcrun
        obtain ⟨r, stM, hcd, hpure⟩ := sm_bind_ok hcrun
        have ⟨hiM, hmM, haM, hrdM, hfwM, hfiM, hfarM, hrc⟩ := S.cond_spec cd h j st0 hi0.inv r stM hcd
        obtain ⟨hb, rfl⟩ := sm_pure_ok hpure; subst hb
        exact ⟨MemoInv.of_alpha_eq hi0 hiM hmM haM hfiM hfarM, hmM, haM, hrdM, hfwM, hfiM, hfarM,
          by simp [Bool.and_eq_true, hrc]⟩
      have ⟨hi', hm', ha', hrd', hfw', hfi', hfar', hout⟩ :=
        Ends.filterM_sm_spec hp js st out st' hinv hrun
      exact ⟨hi', hm', ha', hrd', hfw', hfi', hfar', fun j => by simp [CondOpt, hout j]⟩
    | sym _ _ | lookahead _ | noLT | empty | butNot _ _ | phrase _ =>
      unfold admit at hrun
      obtain ⟨hout, rfl⟩ := sm_pure_ok hrun; subst hout
      refine ⟨hinv, rfl, rfl, rfl, rfl, rfl, rfl, fun j => ?_⟩
      simp [CondOpt, hkeepOnly j]

theorem foldUnionM_spec {α : Type} {c : Bool} {ft : Option (NT × List Param)}
    {f : α → SM T Ends}
    {xs : List α} {st : St T} {out : Ends} {st' : St T}
    {U : α → Nat → Prop} {L : (Key → Nat → Prop) → α → Nat → Prop}
    (L_mono : ∀ {M1 M2 : Key → Nat → Prop}, (∀ k j, M1 k j → M2 k j) → ∀ x j, L M1 x j → L M2 x j)
    {Vis : (Key → Prop) → (Key → Bool) → Nat → α → Prop}
    (Vis_mono : ∀ {V1 V2 : Key → Prop} {r1 r2 : Key → Bool} {f1 f2 : Nat},
      (∀ k, V1 k → V2 k) → (∀ k, r1 k = true → r2 k = true) → f1 ≤ f2 →
      ∀ x, Vis V1 r1 f1 x → Vis V2 r2 f2 x)
    (hinv : S.MemoInv ft st)
    (hactM : c = true → ∀ k_a, st.active.contains k_a = true → k_a.2.2.2.2 = (true && orderedBy A.cx A.g))
    (hf : ∀ x ∈ xs, ∀ st0 es st1, S.MemoInv ft st0 →
      (c = true → ∀ k_a, st0.active.contains k_a = true → k_a.2.2.2.2 = (true && orderedBy A.cx A.g)) →
      (f x).run st0 = .ok (es, st1) →
      S.MemoInv ft st1 ∧
      (∀ k, st1.active.contains k = st0.active.contains k) ∧
      (∀ k, st0.active.contains k = true → st1.memo[k]? = st0.memo[k]?) ∧
      (∀ (k : Key) (e : Entry), st0.memo[k]? = some e → e.final = true → st1.memo[k]? = some e) ∧
      st1.fwd = st0.fwd ∧
      st0.far ≤ st1.far ∧
      (∀ j, es.mem j = true → U x j) ∧
      ∃ rs V M,
        (∀ k, st1.reads.contains k = (st0.reads.contains k || rs k)) ∧
        S.PostFix c rs st1 V M ∧
        (∀ j, L M x j → es.mem j = true) ∧
        (orderedBy A.cx A.g = false → Vis V rs st1.far x))
    (hrun : (foldUnionM f xs).run st = .ok (out, st')) :
    S.MemoInv ft st' ∧
    (∀ k, st'.active.contains k = st.active.contains k) ∧
    (∀ k, st.active.contains k = true → st'.memo[k]? = st.memo[k]?) ∧
    (∀ (k : Key) (e : Entry), st.memo[k]? = some e → e.final = true → st'.memo[k]? = some e) ∧
    st'.fwd = st.fwd ∧
    st.far ≤ st'.far ∧
    (∀ j, out.mem j = true → ∃ x ∈ xs, U x j) ∧
    ∃ rs V M,
      (∀ k, st'.reads.contains k = (st.reads.contains k || rs k)) ∧
      S.PostFix c rs st' V M ∧
      (∀ x ∈ xs, ∀ j, L M x j → out.mem j = true) ∧
      (orderedBy A.cx A.g = false → ∀ x ∈ xs, Vis V rs st'.far x) := by
  induction xs generalizing st out with
  | nil =>
    unfold foldUnionM at hrun
    obtain ⟨hout, rfl⟩ := sm_pure_ok hrun; subst hout
    exact ⟨hinv, fun _ => rfl, fun _ _ => rfl, fun _ _ hm _ => hm, rfl, Nat.le_refl _,
      (fun j hj => nomatch hj),
      fun _ => false, fun _ => False, fun _ _ => True,
      fun k => by simp, S.postFix_top c _,
      (fun _ hx => nomatch hx), (fun _ _ hx => nomatch hx)⟩
  | cons x rest ih =>
    unfold foldUnionM at hrun
    obtain ⟨e1, st1, hx, hr1⟩ := sm_bind_ok hrun
    obtain ⟨er, st2, hrest, hr2⟩ := sm_bind_ok hr1
    obtain ⟨hout, rfl⟩ := sm_pure_ok hr2; subst hout
    have ⟨hi1, ha1, hm1, hf1, hfw1, hfar1, hu1, rs1, V1, M1, hrd1, hpf1, hl1, hv1⟩ :=
      hf x (List.mem_cons_self ..) st e1 st1 hinv hactM hx
    have hactM1 : c = true → ∀ k_a, st1.active.contains k_a = true → k_a.2.2.2.2 = (true && orderedBy A.cx A.g) :=
      fun hc k_a hk => hactM hc k_a ((ha1 k_a) ▸ hk)
    have ⟨hi2, ha2, hm2, hf2, hfw2, hfar2, hu2, rs2, V2, M2, hrd2, hpf2, hl2, hv2⟩ :=
      ih hi1 hactM1 (fun x' hx' => hf x' (List.mem_cons_of_mem _ hx')) hrest
    have hpf := (hpf1.mono_state ha2 hm2 hfar2).inter hpf2
    refine ⟨hi2,
      fun k => (ha2 k).trans (ha1 k),
      fun k hak => (hm2 k ((ha1 k).symm ▸ hak)).trans (hm1 k hak),
      fun k e hm he => hf2 k e (hf1 k e hm he) he,
      hfw2.trans hfw1,
      Nat.le_trans hfar1 hfar2,
      fun j hj => ?_,
      fun k => rs1 k || rs2 k, fun k => V1 k ∨ V2 k, fun k j => M1 k j ∧ M2 k j,
      fun k => by rw [hrd2 k, hrd1 k, Bool.or_assoc],
      hpf, ?_, ?_⟩
    · rw [Ends.mem_union, Bool.or_eq_true] at hj
      rcases hj with hj1 | hj2
      · exact ⟨x, List.mem_cons_self .., hu1 j hj1⟩
      · obtain ⟨x', hx', hux⟩ := hu2 j hj2
        exact ⟨x', List.mem_cons_of_mem _ hx', hux⟩
    · intro x' hx' j hlj
      rw [Ends.mem_union, Bool.or_eq_true]
      rcases List.mem_cons.mp hx' with rfl | hx'
      · exact Or.inl (hl1 j (L_mono (fun _ _ h => h.1) x' j hlj))
      · exact Or.inr (hl2 x' hx' j (L_mono (fun _ _ h => h.2) x' j hlj))
    · intro hord x' hx'
      rcases List.mem_cons.mp hx' with rfl | hx'
      · exact Vis_mono (fun _ => Or.inl) (fun k h => (Bool.or_eq_true _ _).mpr (Or.inl h)) hfar2 x' (hv1 hord)
      · exact Vis_mono (fun _ => Or.inr) (fun k h => (Bool.or_eq_true _ _).mpr (Or.inr h)) (Nat.le_refl _) x' (hv2 hord x' hx')

theorem ntEnds_spec {c : Bool} {ft : Option (NT × List Param)}
    {rec : NT → List Param → Nat → SM T Ends} (hrec : S.RecSpec c ft rec)
    (n : NT) (ps : List Param) (h : Nat) (st : St T) (es : Ends) (st' : St T)
    (hinv : S.MemoInv ft st)
    (hactM : c = true → ∀ k_a, st.active.contains k_a = true → k_a.2.2.2.2 = (true && orderedBy A.cx A.g))
    (hopen : (altsOf A.cx A.g n).isEmpty = false → ∀ g gp, ft = some (g, gp) → S.SpecOpen g gp n ps h)
    (hrun : (ntEnds A rec n ps h).run st = .ok (es, st')) :
    S.MemoInv ft st' ∧
    (∀ x, st'.active.contains x = st.active.contains x) ∧
    (∀ x, st.active.contains x = true → st'.memo[x]? = st.memo[x]?) ∧
    (∀ (x : Key) (e : Entry), st.memo[x]? = some e → e.final = true → st'.memo[x]? = some e) ∧
    st'.fwd = st.fwd ∧
    st.far ≤ st'.far ∧
    (∀ j, es.mem j = true →
      if !(altsOf A.cx A.g n).isEmpty then S.SpanOfAllow (S.CommitAllow c) n ps h j else S.Leaf n h j) ∧
    ∃ rs V M,
      (∀ x, st'.reads.contains x = (st.reads.contains x || rs x)) ∧
      S.PostFix c rs st' V M ∧
      (∀ j, (if !(altsOf A.cx A.g n).isEmpty then S.OfKey c M n ps h j else S.Leaf n h j) → es.mem j = true) ∧
      (orderedBy A.cx A.g = false → (altsOf A.cx A.g n).isEmpty = false →
        V (key A false n ps h) ∨ rs (key A false n ps h) = true) := by
  unfold ntEnds at hrun
  cases hem : (altsOf A.cx A.g n).isEmpty with
  | false =>
    simp only [hem, Bool.not_false, ↓reduceIte] at hrun ⊢
    have ⟨hi', ha', hm', hf', hfw', hfar', hu, rs, V, M, hrd, hpf, hl, hv⟩ :=
      hrec.run_spec n ps h st es st' hinv hactM (hopen hem) hrun
    exact ⟨hi', ha', hm', hf', hfw', hfar', hu, rs, V, M, hrd, hpf, hl, fun hord _ => hv hord⟩
  | true =>
    simp only [hem, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hrun ⊢
    obtain ⟨o, st1, hlf, hr1⟩ := sm_bind_ok hrun
    have ⟨hi1, hm1, ha1, hrd1, hfw1, hfi1, hfar1, hlo⟩ := S.leaf_spec n h st hinv.inv o st1 hlf
    obtain ⟨hes, rfl⟩ := sm_pure_ok hr1; subst hes
    refine ⟨MemoInv.of_alpha_eq hinv hi1 hm1 ha1 hfi1 hfar1,
      fun x => by rw [ha1],
      fun x _ => by rw [hm1],
      fun x e hx _ => hm1 ▸ hx,
      hfw1, by rw [hfar1]; exact Nat.le_refl _,
      fun j hj => ?_,
      fun _ => false, fun _ => False, fun _ _ => True,
      fun x => by rw [hrd1]; simp,
      S.postFix_top c _,
      fun j hlj => ?_,
      fun _ hne => nomatch hne⟩
    · rw [Ends.mem_ofList, List.contains_iff_mem] at hj
      rcases hlo with ⟨j0, rfl, hlj0⟩ | ⟨rfl, _⟩
      · simp only [Option.toList_some, List.mem_singleton] at hj; subst hj; exact hlj0
      · cases hj
    · rw [Ends.mem_ofList, List.contains_iff_mem]
      rcases hlo with ⟨j0, rfl, hlj0⟩ | ⟨rfl, hno⟩
      · simp [S.leaf_det n h j j0 hlj hlj0]
      · exact absurd hlj (hno j)

theorem stepItem_spec {c : Bool} {ft : Option (NT × List Param)}
    {rec : NT → List Param → Nat → SM T Ends} (hrec : S.RecSpec c ft rec)
    (s : Src) (k : Nat) (ps : List Param) (it : Item) (rest : List Item) (P : Ends)
    (st : St T) (out : Ends) (st' : St T)
    (hinv : S.MemoInv ft st)
    (hactM : c = true → ∀ k_a, st.active.contains k_a = true → k_a.2.2.2.2 = (true && orderedBy A.cx A.g))
    (hwf : ItemWF A it)
    (hpref : ∀ g gp, ft = some (g, gp) → ∀ h, P.mem h = true → S.SpecPrefix g gp s ps k (it :: rest) h)
    (hrun : (stepItem A rec s k ps it rest.head? P).run st = .ok (out, st')) :
    S.MemoInv ft st' ∧
    (∀ x, st'.active.contains x = st.active.contains x) ∧
    (∀ x, st.active.contains x = true → st'.memo[x]? = st.memo[x]?) ∧
    (∀ (x : Key) (e : Entry), st.memo[x]? = some e → e.final = true → st'.memo[x]? = some e) ∧
    st'.fwd = st.fwd ∧
    st.far ≤ st'.far ∧
    (∀ j, out.mem j = true → ∃ h, P.mem h = true ∧ S.ItemStep (S.SpanOfAllow (S.CommitAllow c)) s k ps it rest.head? h j) ∧
    ∃ rs V M,
      (∀ x, st'.reads.contains x = (st.reads.contains x || rs x)) ∧
      S.PostFix c rs st' V M ∧
      (∀ h j, P.mem h = true → S.ItemStep (S.OfKey c M) s k ps it rest.head? h j → out.mem j = true) ∧
      (orderedBy A.cx A.g = false → ∀ h, P.mem h = true →
        (∀ j, S.ItemMatch (S.OfKey false M) s k ps it rest.head? h j → j ≤ st'.far) ∧
        (∀ m args, (altsOf A.cx A.g m).isEmpty = false →
          ((∃ o, it = .sym (.nt m args) o) ∨ (∃ ex, it = .butNot (.nt m args) ex)) →
          V (key A false m (applyArgs ps args) h) ∨ rs (key A false m (applyArgs ps args) h) = true)) := by
  have htoPlain : ∀ n' ps' a' b', S.SpanOfAllow (S.CommitAllow c) n' ps' a' b' →
      S.SpanOfAllow (fun _ _ _ _ => True) n' ps' a' b' :=
    fun _ _ _ _ ⟨t, hd⟩ => ⟨t, S.derivesWith_mono_allow (fun _ _ _ _ _ => trivial) hd⟩
  have hhitTail : ∀ (out0 : Ends) (st1 : St T) (hi1 : S.MemoInv ft st1)
      (houtHit : ∀ g gp, ft = some (g, gp) → ∀ j, out0.mem j = true → S.SpecHit g gp j)
      (htail : (if let some j := out0.max? then do A.hit j; pure out0 else pure out0).run st1 = .ok (out, st')),
      out = out0 ∧ S.MemoInv ft st' ∧ st'.memo = st1.memo ∧ st'.active = st1.active ∧
      st'.reads = st1.reads ∧ st'.fwd = st1.fwd ∧ st'.first = st1.first ∧ st1.far ≤ st'.far ∧
      (∀ j, out0.mem j = true → j ≤ st'.far) := by
    intro out0 st1 hi1 houtHit htail
    cases hm : out0.max? with
    | none =>
      simp only [hm] at htail
      obtain ⟨heq, rfl⟩ := sm_pure_ok htail
      exact ⟨heq.symm, hi1, rfl, rfl, rfl, rfl, rfl, Nat.le_refl _,
        fun j hj => by rw [Ends.max?_none hm j] at hj; cases hj⟩
    | some m =>
      simp only [hm] at htail
      obtain ⟨_, st2, hh1, hp2⟩ := sm_bind_ok htail
      obtain ⟨hjm, hjub⟩ := Ends.max?_some hm
      have ⟨hi2, hm2, ha2, hrd2, hfw2, hfi2, hfar2⟩ := S.hit_spec m st1 hi1.inv _ st2 hh1
      obtain ⟨heq, rfl⟩ := sm_pure_ok hp2
      exact ⟨heq.symm, MemoInv.of_hit hi1 hi2 hm2 ha2 hfi2 hfar2 (fun g gp hft => houtHit g gp hft m hjm),
        hm2, ha2, hrd2, hfw2, hfi2, by rw [hfar2]; exact Nat.le_max_left _ _,
        fun j hj => by rw [hfar2]; exact Nat.le_trans (hjub j hj) (Nat.le_max_right _ _)⟩
  cases it with
  | sym x o =>
    cases x with
    | t tm =>
      unfold stepItem at hrun; dsimp only at hrun
      obtain ⟨P', st1, hc, hr1⟩ := sm_bind_ok hrun
      obtain ⟨out0, st1', hpure, htail⟩ := sm_bind_ok hr1
      obtain ⟨hout0, hst1'⟩ := sm_pure_ok hpure; subst st1'
      have htf : ∀ h st0, S.MemoInv ft st0 → ∀ r st1', (A.term s k tm h).run st0 = .ok (r, st1') →
          S.MemoInv ft st1' ∧ st1'.memo = st0.memo ∧ st1'.active = st0.active ∧ st1'.reads = st0.reads ∧
          st1'.fwd = st0.fwd ∧ st1'.first = st0.first ∧ st1'.far = st0.far ∧
          ((∃ j, r = some j ∧ S.Term s k tm h j) ∨ (r = none ∧ ∀ j, ¬ S.Term s k tm h j)) := by
        intro h st0 hi0 r st1' hr
        have ⟨hi', hm', ha', hrd', hfw', hfi', hfar', ho'⟩ := S.term_spec s k tm h st0 hi0.inv r st1' hr
        exact ⟨MemoInv.of_alpha_eq hi0 hi' hm' ha' hfi' hfar', hm', ha', hrd', hfw', hfi', hfar', ho'⟩
      have ⟨hi1, hm1, ha1, hrd1, hfw1, hfi1, hfar1, hP'⟩ :=
        S.collectM_rel_spec htf (S.term_det s k tm) P.toList st P' st1 hinv hc
      have hu0 : ∀ j, out0.mem j = true → ∃ h, P.mem h = true ∧ S.ItemStep (S.SpanOfAllow (S.CommitAllow c)) s k ps (.sym (.t tm) o) rest.head? h j := by
        intro j hj; rw [← hout0] at hj
        cases o with
        | false =>
          simp only [Bool.false_eq_true, ↓reduceIte, Ends.mem_ofList, List.contains_iff_mem, hP', Ends.mem_toList] at hj
          obtain ⟨h, hh, htm⟩ := hj; exact ⟨h, hh, Or.inr htm⟩
        | true =>
          simp only [↓reduceIte, Ends.mem_union, Bool.or_eq_true, Ends.mem_ofList, List.contains_iff_mem, hP', Ends.mem_toList] at hj
          rcases hj with ⟨h, hh, htm⟩ | hjP
          · exact ⟨h, hh, Or.inr htm⟩
          · exact ⟨j, hjP, Or.inl ⟨rfl, rfl⟩⟩
      have houtHit : ∀ g gp, ft = some (g, gp) → ∀ j, out0.mem j = true → S.SpecHit g gp j := by
        intro g gp hft j hj
        obtain ⟨h, hh, hs⟩ := hu0 j hj
        rcases hs with ⟨_, rfl⟩ | htm
        · exact S.specPrefix_hit (hpref g gp hft j hh)
        · exact .matchAt (hpref g gp hft h hh) htm
      obtain ⟨rfl, hi2, hm2, ha2, hrd2, hfw2, hfi2, hfar2, hjb⟩ := hhitTail out0 st1 hi1 houtHit htail
      refine ⟨hi2,
        fun q => by rw [ha2, ha1],
        fun q _ => by rw [hm2, hm1],
        fun q e hq _ => (hm2.trans hm1) ▸ hq,
        hfw2.trans hfw1,
        by rw [← hfar1]; exact hfar2,
        hu0,
        fun _ => false, fun _ => False, fun _ _ => True,
        fun q => by rw [hrd2, hrd1]; simp,
        S.postFix_top c st',
        fun h j hh hs => ?_,
        fun _ h hh => ⟨fun j hjm => hjb j ?_,
          fun _ _ _ hk => by rcases hk with ⟨_, h1⟩ | ⟨_, h1⟩ <;> cases h1⟩⟩
      · rw [← hout0]
        cases o with
        | false =>
          rcases hs with ⟨ho, _⟩ | htm; · cases ho
          simp only [Bool.false_eq_true, ↓reduceIte, Ends.mem_ofList, List.contains_iff_mem, hP', Ends.mem_toList]
          exact ⟨h, hh, htm⟩
        | true =>
          simp only [↓reduceIte, Ends.mem_union, Bool.or_eq_true, Ends.mem_ofList, List.contains_iff_mem, hP', Ends.mem_toList]
          rcases hs with ⟨_, rfl⟩ | htm
          · exact Or.inr hh
          · exact Or.inl ⟨h, hh, htm⟩
      · rw [← hout0]
        cases o <;> simp only [↓reduceIte, Bool.false_eq_true, Ends.mem_union, Bool.or_eq_true,
          Ends.mem_ofList, List.contains_iff_mem, hP', Ends.mem_toList]
        · exact ⟨h, hh, hjm⟩
        · exact Or.inl ⟨h, hh, hjm⟩
    | nt n args =>
      unfold stepItem at hrun; dsimp only at hrun
      obtain ⟨acc, st1, hfU, hr1⟩ := sm_bind_ok hrun
      obtain ⟨out0, st1', hpure, htail⟩ := sm_bind_ok hr1
      obtain ⟨hout0, hst1'⟩ := sm_pure_ok hpure; subst st1'
      have hstep1 : ∀ h ∈ P.toList, ∀ st0 es st1', S.MemoInv ft st0 →
          (c = true → ∀ k_a, st0.active.contains k_a = true → k_a.2.2.2.2 = (true && orderedBy A.cx A.g)) →
          (do let ne ← ntEnds A rec n (applyArgs ps args) h; admit A s.rule.lhs n rest.head? h ne).run st0 = .ok (es, st1') →
          S.MemoInv ft st1' ∧
          (∀ q, st1'.active.contains q = st0.active.contains q) ∧
          (∀ q, st0.active.contains q = true → st1'.memo[q]? = st0.memo[q]?) ∧
          (∀ (q : Key) (e : Entry), st0.memo[q]? = some e → e.final = true → st1'.memo[q]? = some e) ∧
          st1'.fwd = st0.fwd ∧
          st0.far ≤ st1'.far ∧
          (∀ j, es.mem j = true → S.ItemMatch (S.SpanOfAllow (S.CommitAllow c)) s k ps (.sym (.nt n args) o) rest.head? h j) ∧
          ∃ rs V M,
            (∀ q, st1'.reads.contains q = (st0.reads.contains q || rs q)) ∧
            S.PostFix c rs st1' V M ∧
            (∀ j, S.ItemMatch (S.OfKey c M) s k ps (.sym (.nt n args) o) rest.head? h j → es.mem j = true) ∧
            (orderedBy A.cx A.g = false →
              ((altsOf A.cx A.g n).isEmpty = false → V (key A false n (applyArgs ps args) h) ∨ rs (key A false n (applyArgs ps args) h) = true)) := by
        intro h hhL st0 es st1' hi0 hact0 hfr
        have hhP : P.mem h = true := (Ends.mem_toList P h).mp hhL
        obtain ⟨ne, stN, hneRun, hadmRun⟩ := sm_bind_ok hfr
        have hopenN : (altsOf A.cx A.g n).isEmpty = false → ∀ g gp, ft = some (g, gp) → S.SpecOpen g gp n (applyArgs ps args) h :=
          fun hne g gp hft => .nt (hpref g gp hft h hhP) hne
        have ⟨hiN, haN, hmN, hfN, hfwN, hfarN, huN, rs, V, M, hrdN, hpfN, hlN, hvN⟩ :=
          S.ntEnds_spec hrec n (applyArgs ps args) h st0 ne stN hi0 hact0 hopenN hneRun
        have ⟨hiA, hmA, haA, hrdA, hfwA, hfiA, hfarA, hadm⟩ :=
          S.admit_spec s.rule.lhs n rest.head? h ne stN es st1' hiN hadmRun
        have hpfA := hpfN.mono_state (fun q => by rw [haA]) (fun q _ => by rw [hmA]) (by rw [hfarA]; exact Nat.le_refl _)
        refine ⟨hiA,
          fun q => by rw [haA, haN],
          fun q hq => by rw [hmA, hmN q hq],
          fun q e hq he => hmA ▸ hfN q e hq he,
          hfwA.trans hfwN,
          by rw [hfarA]; exact hfarN,
          fun j hj => ?_,
          rs, V, M,
          fun q => by rw [hrdA, hrdN],
          hpfA,
          fun j hj => ?_,
          hvN⟩
        · obtain ⟨hnej, hkj, hcj⟩ := (hadm j).mp hj
          exact ⟨hkj, hcj, huN j hnej⟩
        · obtain ⟨hkj, hcj, hrj⟩ := hj
          exact (hadm j).mpr ⟨hlN j hrj, hkj, hcj⟩
      have ⟨hi1, ha1, hm1, hf1, hfw1, hfar1, hu1, rs, V, M, hrd1, hpf1, hl1, hv1⟩ :=
        S.foldUnionM_spec
          (U := fun h j => S.ItemMatch (S.SpanOfAllow (S.CommitAllow c)) s k ps (.sym (.nt n args) o) rest.head? h j)
          (L := fun M h j => S.ItemMatch (S.OfKey c M) s k ps (.sym (.nt n args) o) rest.head? h j)
          (fun hmM _ _ hj => S.itemMatch_mono (fun _ _ _ _ h => hmM _ _ h) hj)
          (Vis := fun V rs _ h => (altsOf A.cx A.g n).isEmpty = false → V (key A false n (applyArgs ps args) h) ∨ rs (key A false n (applyArgs ps args) h) = true)
          (fun hmV hmR _ _ hv hne => (hv hne).elim (Or.inl ∘ hmV _) (Or.inr ∘ hmR _))
          hinv hactM hstep1 hfU
      have hu0 : ∀ j, out0.mem j = true → ∃ h, P.mem h = true ∧ S.ItemStep (S.SpanOfAllow (S.CommitAllow c)) s k ps (.sym (.nt n args) o) rest.head? h j := by
        intro j hj; rw [← hout0] at hj
        cases o with
        | false =>
          simp only [Bool.false_eq_true, ↓reduceIte] at hj
          obtain ⟨h, hhL, hm⟩ := hu1 j hj
          exact ⟨h, (Ends.mem_toList P h).mp hhL, Or.inr hm⟩
        | true =>
          simp only [↓reduceIte, Ends.mem_union, Bool.or_eq_true] at hj
          rcases hj with hjA | hjP
          · obtain ⟨h, hhL, hm⟩ := hu1 j hjA
            exact ⟨h, (Ends.mem_toList P h).mp hhL, Or.inr hm⟩
          · exact ⟨j, hjP, Or.inl ⟨rfl, rfl⟩⟩
      have houtHit : ∀ g gp, ft = some (g, gp) → ∀ j, out0.mem j = true → S.SpecHit g gp j := by
        intro g gp hft j hj
        obtain ⟨h, hh, hs⟩ := hu0 j hj
        rcases hs with ⟨_, rfl⟩ | hm
        · exact S.specPrefix_hit (hpref g gp hft j hh)
        · exact .matchAt (hpref g gp hft h hh) (S.itemMatch_mono htoPlain hm)
      obtain ⟨rfl, hi2, hm2, ha2, hrd2, hfw2, hfi2, hfar2, hjb⟩ := hhitTail out0 st1 hi1 houtHit htail
      have hpf2 := hpf1.mono_state (fun q => by rw [ha2]) (fun q _ => by rw [hm2]) hfar2
      refine ⟨hi2,
        fun q => by rw [ha2, ha1],
        fun q hq => by rw [hm2, hm1 q hq],
        fun q e hq he => hm2 ▸ hf1 q e hq he,
        hfw2.trans hfw1,
        Nat.le_trans hfar1 hfar2,
        hu0,
        rs, V, M,
        fun q => by rw [hrd2, hrd1],
        hpf2,
        fun h j hh hs => ?_,
        fun hord h hh => ⟨fun j hjm => hjb j ?_, fun m' args' hne' hk' => ?_⟩⟩
      · rw [← hout0]
        have hhL := (Ends.mem_toList P h).mpr hh
        cases o with
        | false =>
          rcases hs with ⟨ho, _⟩ | hm; · cases ho
          simp [hl1 h hhL j hm]
        | true =>
          simp only [↓reduceIte, Ends.mem_union, Bool.or_eq_true]
          rcases hs with ⟨_, rfl⟩ | hm
          · exact Or.inr hh
          · exact Or.inl (hl1 h hhL j hm)
      · rw [← hout0]
        rw [← S.ofKey_eq_false_of_ordered_false hord c M] at hjm
        have hhL := (Ends.mem_toList P h).mpr hh
        cases o <;> simp only [↓reduceIte, Bool.false_eq_true, Ends.mem_union, Bool.or_eq_true]
        · exact hl1 h hhL j hjm
        · exact Or.inl (hl1 h hhL j hjm)
      · rcases hk' with ⟨o', h1⟩ | ⟨_, h1⟩
        · cases h1
          exact hv1 hord h ((Ends.mem_toList P h).mpr hh) hne'
        · cases h1
  | butNot base ex =>
    unfold stepItem at hrun; dsimp only at hrun
    obtain ⟨out0, st1, hbody, htail⟩ := sm_bind_ok hrun
    have hstepBN : ∀ h ∈ P.toList, ∀ st0 es st1', S.MemoInv ft st0 →
        (c = true → ∀ k_a, st0.active.contains k_a = true → k_a.2.2.2.2 = (true && orderedBy A.cx A.g)) →
        (do
          let js ← match base with
            | .t x => pure (Ends.ofList (← A.term s k x h).toList)
            | .nt n args => admit A s.rule.lhs n none h (← ntEnds A rec n (applyArgs ps args) h)
          js.filterM fun j => return !(← excluded A s k ps h j ex)).run st0 = .ok (es, st1') →
        S.MemoInv ft st1' ∧
        (∀ q, st1'.active.contains q = st0.active.contains q) ∧
        (∀ q, st0.active.contains q = true → st1'.memo[q]? = st0.memo[q]?) ∧
        (∀ (q : Key) (e : Entry), st0.memo[q]? = some e → e.final = true → st1'.memo[q]? = some e) ∧
        st1'.fwd = st0.fwd ∧
        st0.far ≤ st1'.far ∧
        (∀ j, es.mem j = true → S.ItemMatch (S.SpanOfAllow (S.CommitAllow c)) s k ps (.butNot base ex) rest.head? h j) ∧
        ∃ rs V M,
          (∀ q, st1'.reads.contains q = (st0.reads.contains q || rs q)) ∧
          S.PostFix c rs st1' V M ∧
          (∀ j, S.ItemMatch (S.OfKey c M) s k ps (.butNot base ex) rest.head? h j → es.mem j = true) ∧
          (orderedBy A.cx A.g = false →
            ∀ m' args', (altsOf A.cx A.g m').isEmpty = false → base = .nt m' args' →
              V (key A false m' (applyArgs ps args') h) ∨ rs (key A false m' (applyArgs ps args') h) = true) := by
      intro h hhL st0 es st1' hi0 hact0 hfr
      have hhP : P.mem h = true := (Ends.mem_toList P h).mp hhL
      have hexPred : ∀ j stA, S.MemoInv ft stA → ∀ b stB,
          (do let r ← excluded A s k ps h j ex; pure (!r)).run stA = .ok (b, stB) →
          S.MemoInv ft stB ∧ stB.memo = stA.memo ∧ stB.active = stA.active ∧ stB.reads = stA.reads ∧
          stB.fwd = stA.fwd ∧ stB.first = stA.first ∧ stB.far = stA.far ∧
          (b = true ↔ ¬ S.ExclHolds s k ps h j ex) := by
        intro j stA hiA b stB hexr
        obtain ⟨r, stE, hex1, hpure⟩ := sm_bind_ok hexr
        have ⟨hiE, hmE, haE, hrdE, hfwE, hfiE, hfarE, hre⟩ :=
          excluded_spec S s k ps h j ex stA hiA.inv hwf r stE hex1
        obtain ⟨hb, rfl⟩ := sm_pure_ok hpure; subst hb
        exact ⟨MemoInv.of_alpha_eq hiA hiE hmE haE hfiE hfarE, hmE, haE, hrdE, hfwE, hfiE, hfarE,
          by simp [← hre]⟩
      cases base with
      | t x =>
        dsimp only at hfr
        obtain ⟨o, stT, htmRun, hrA⟩ := sm_bind_ok hfr
        obtain ⟨js, stJ, hpure, hfltRun⟩ := sm_bind_ok hrA
        obtain ⟨hjs, hstJ⟩ := sm_pure_ok hpure; subst stJ hjs
        have ⟨hiT, hmT, haT, hrdT, hfwT, hfiT, hfarT, hto⟩ := S.term_spec s k x h st0 hi0.inv o stT htmRun
        have hiJ := MemoInv.of_alpha_eq hi0 hiT hmT haT hfiT hfarT
        have ⟨hiF, hmF, haF, hrdF, hfwF, hfiF, hfarF, hflt⟩ :=
          Ends.filterM_sm_spec hexPred _ stT es st1' hiJ hfltRun
        refine ⟨hiF,
          fun q => by rw [haF, haT],
          fun q _ => by rw [hmF, hmT],
          fun q e hq _ => (hmF.trans hmT) ▸ hq,
          hfwF.trans hfwT,
          by rw [hfarF, hfarT]; exact Nat.le_refl _,
          fun j hj => ?_,
          fun _ => false, fun _ => False, fun _ _ => True,
          fun q => by rw [hrdF, hrdT]; simp,
          S.postFix_top c st1',
          fun j hj => ?_,
          fun _ _ _ _ hb => nomatch hb⟩
        · obtain ⟨hjsm, hnex⟩ := (hflt j).mp hj
          rw [Ends.mem_ofList, List.contains_iff_mem] at hjsm
          rcases hto with ⟨j0, rfl, htj0⟩ | ⟨rfl, _⟩
          · simp only [Option.toList_some, List.mem_singleton] at hjsm; subst hjsm; exact ⟨htj0, hnex⟩
          · cases hjsm
        · obtain ⟨htj, hnex⟩ := hj
          refine (hflt j).mpr ⟨?_, hnex⟩
          rw [Ends.mem_ofList, List.contains_iff_mem]
          rcases hto with ⟨j0, rfl, htj0⟩ | ⟨rfl, hno⟩
          · simp [S.term_det s k x h j j0 htj htj0]
          · exact absurd htj (hno j)
      | nt n args =>
        dsimp only at hfr
        obtain ⟨ne, stN, hneRun, hrA⟩ := sm_bind_ok hfr
        obtain ⟨js, stJ, hadmRun, hfltRun⟩ := sm_bind_ok hrA
        have hopenN : (altsOf A.cx A.g n).isEmpty = false → ∀ g gp, ft = some (g, gp) → S.SpecOpen g gp n (applyArgs ps args) h :=
          fun hne g gp hft => .butNotN (hpref g gp hft h hhP) hne
        have ⟨hiN, haN, hmN, hfN, hfwN, hfarN, huN, rs, V, M, hrdN, hpfN, hlN, hvN⟩ :=
          S.ntEnds_spec hrec n (applyArgs ps args) h st0 ne stN hi0 hact0 hopenN hneRun
        have ⟨hiA, hmA, haA, hrdA, hfwA, hfiA, hfarA, hadm⟩ :=
          S.admit_spec s.rule.lhs n none h ne stN js stJ hiN hadmRun
        have ⟨hiF, hmF, haF, hrdF, hfwF, hfiF, hfarF, hflt⟩ :=
          Ends.filterM_sm_spec hexPred js stJ es st1' hiA hfltRun
        have hpfF := hpfN.mono_state (fun q => by rw [haF, haA]) (fun q _ => by rw [hmF, hmA])
          (by rw [hfarF, hfarA]; exact Nat.le_refl _)
        refine ⟨hiF,
          fun q => by rw [haF, haA, haN],
          fun q hq => by rw [hmF, hmA, hmN q hq],
          fun q e hq he => (hmF.trans hmA) ▸ hfN q e hq he,
          hfwF.trans (hfwA.trans hfwN),
          by rw [hfarF, hfarA]; exact hfarN,
          fun j hj => ?_,
          rs, V, M,
          fun q => by rw [hrdF, hrdA, hrdN],
          hpfF,
          fun j hj => ?_,
          fun hord m' args' hne' hb => by cases hb; exact hvN hord hne'⟩
        · obtain ⟨hjsm, hnex⟩ := (hflt j).mp hj
          obtain ⟨hnej, hkj, _⟩ := (hadm j).mp hjsm
          exact ⟨hkj, hnex, huN j hnej⟩
        · obtain ⟨hkj, hnex, hrj⟩ := hj
          exact (hflt j).mpr ⟨(hadm j).mpr ⟨hlN j hrj, hkj, trivial⟩, hnex⟩
    have ⟨hi1, ha1, hm1, hf1, hfw1, hfar1, hu1, rs, V, M, hrd1, hpf1, hl1, hv1⟩ :=
      S.foldUnionM_spec
        (U := fun h j => S.ItemMatch (S.SpanOfAllow (S.CommitAllow c)) s k ps (.butNot base ex) rest.head? h j)
        (L := fun M h j => S.ItemMatch (S.OfKey c M) s k ps (.butNot base ex) rest.head? h j)
        (fun hmM _ _ hj => S.itemMatch_mono (fun _ _ _ _ h => hmM _ _ h) hj)
        (Vis := fun V rs _ h => ∀ m' args', (altsOf A.cx A.g m').isEmpty = false → base = .nt m' args' →
          V (key A false m' (applyArgs ps args') h) ∨ rs (key A false m' (applyArgs ps args') h) = true)
        (fun hmV hmR _ _ hv m' args' hne' hb => (hv m' args' hne' hb).elim (Or.inl ∘ hmV _) (Or.inr ∘ hmR _))
        hinv hactM hstepBN hbody
    have hu0 : ∀ j, out0.mem j = true → ∃ h, P.mem h = true ∧ S.ItemStep (S.SpanOfAllow (S.CommitAllow c)) s k ps (.butNot base ex) rest.head? h j := by
      intro j hj; obtain ⟨h, hhL, hm⟩ := hu1 j hj; exact ⟨h, (Ends.mem_toList P h).mp hhL, hm⟩
    have houtHit : ∀ g gp, ft = some (g, gp) → ∀ j, out0.mem j = true → S.SpecHit g gp j := by
      intro g gp hft j hj
      obtain ⟨h, hh, hm⟩ := hu0 j hj
      exact .matchAt (hpref g gp hft h hh) (S.itemMatch_mono htoPlain hm)
    obtain ⟨rfl, hi2, hm2, ha2, hrd2, hfw2, hfi2, hfar2, hjb⟩ := hhitTail out0 st1 hi1 houtHit htail
    have hpf2 := hpf1.mono_state (fun q => by rw [ha2]) (fun q _ => by rw [hm2]) hfar2
    refine ⟨hi2,
      fun q => by rw [ha2, ha1],
      fun q hq => by rw [hm2, hm1 q hq],
      fun q e hq he => hm2 ▸ hf1 q e hq he,
      hfw2.trans hfw1,
      Nat.le_trans hfar1 hfar2,
      hu0,
      rs, V, M,
      fun q => by rw [hrd2, hrd1],
      hpf2,
      fun h j hh hs => hl1 h ((Ends.mem_toList P h).mpr hh) j hs,
      fun hord h hh => ⟨fun j hjm => hjb j ?_, fun m' args' hne' hk' => ?_⟩⟩
    · rw [← S.ofKey_eq_false_of_ordered_false hord c M] at hjm
      exact hl1 h ((Ends.mem_toList P h).mpr hh) j hjm
    · rcases hk' with ⟨_, h1⟩ | ⟨ex', h1⟩
      · cases h1
      · injection h1 with hb _; exact hv1 hord h ((Ends.mem_toList P h).mpr hh) m' args' hne' hb
  | phrase p =>
    unfold stepItem at hrun; dsimp only at hrun
    obtain ⟨P', st1, hc, hr1⟩ := sm_bind_ok hrun
    obtain ⟨out0, st1', hpure, htail⟩ := sm_bind_ok hr1
    obtain ⟨hout0, hst1'⟩ := sm_pure_ok hpure; subst st1'
    have hpf : ∀ h st0, S.MemoInv ft st0 → ∀ r st1', (A.phrase p h).run st0 = .ok (r, st1') →
        S.MemoInv ft st1' ∧ st1'.memo = st0.memo ∧ st1'.active = st0.active ∧ st1'.reads = st0.reads ∧
        st1'.fwd = st0.fwd ∧ st1'.first = st0.first ∧ st1'.far = st0.far ∧
        ((∃ j, r = some j ∧ S.Phrase p h j) ∨ (r = none ∧ ∀ j, ¬ S.Phrase p h j)) := by
      intro h st0 hi0 r st1' hr
      have ⟨hi', hm', ha', hrd', hfw', hfi', hfar', ho'⟩ := S.phrase_spec p h st0 hi0.inv r st1' hr
      exact ⟨MemoInv.of_alpha_eq hi0 hi' hm' ha' hfi' hfar', hm', ha', hrd', hfw', hfi', hfar', ho'⟩
    have ⟨hi1, hm1, ha1, hrd1, hfw1, hfi1, hfar1, hP'⟩ :=
      S.collectM_rel_spec hpf (S.phrase_det p) P.toList st P' st1 hinv hc
    have hu0 : ∀ j, out0.mem j = true → ∃ h, P.mem h = true ∧ S.ItemStep (S.SpanOfAllow (S.CommitAllow c)) s k ps (.phrase p) rest.head? h j := by
      intro j hj; rw [← hout0, Ends.mem_ofList, List.contains_iff_mem, hP'] at hj
      obtain ⟨h, hhL, hph⟩ := hj; exact ⟨h, (Ends.mem_toList P h).mp hhL, hph⟩
    have houtHit : ∀ g gp, ft = some (g, gp) → ∀ j, out0.mem j = true → S.SpecHit g gp j := by
      intro g gp hft j hj
      obtain ⟨h, hh, hph⟩ := hu0 j hj
      exact .matchAt (hpref g gp hft h hh) hph
    obtain ⟨rfl, hi2, hm2, ha2, hrd2, hfw2, hfi2, hfar2, hjb⟩ := hhitTail out0 st1 hi1 houtHit htail
    refine ⟨hi2,
      fun q => by rw [ha2, ha1],
      fun q _ => by rw [hm2, hm1],
      fun q e hq _ => (hm2.trans hm1) ▸ hq,
      hfw2.trans hfw1,
      by rw [← hfar1]; exact hfar2,
      hu0,
      fun _ => false, fun _ => False, fun _ _ => True,
      fun q => by rw [hrd2, hrd1]; simp,
      S.postFix_top c st',
      fun h j hh hs => ?_,
      fun _ h hh => ⟨fun j hjm => hjb j ?_,
        fun _ _ _ hk => by rcases hk with ⟨_, h1⟩ | ⟨_, h1⟩ <;> cases h1⟩⟩
    · rw [← hout0, Ends.mem_ofList, List.contains_iff_mem, hP']
      exact ⟨h, (Ends.mem_toList P h).mpr hh, hs⟩
    · rw [← hout0, Ends.mem_ofList, List.contains_iff_mem, hP']
      exact ⟨h, (Ends.mem_toList P h).mpr hh, hjm⟩
  | lookahead l =>
    unfold stepItem at hrun; dsimp only at hrun
    obtain ⟨out0, st1, hbody, hpure⟩ := sm_bind_ok hrun
    obtain ⟨hout0, hst1⟩ := sm_pure_ok hpure; subst st1 hout0
    have hp : ∀ h st0, S.MemoInv ft st0 → ∀ b st1', (lookOk A l h).run st0 = .ok (b, st1') →
        S.MemoInv ft st1' ∧ st1'.memo = st0.memo ∧ st1'.active = st0.active ∧ st1'.reads = st0.reads ∧
        st1'.fwd = st0.fwd ∧ st1'.first = st0.first ∧ st1'.far = st0.far ∧
        (b = true ↔ S.LookHolds l h) := by
      intro h st0 hi0 b st1' hr
      have ⟨hi', hm', ha', hrd', hfw', hfi', hfar', hb⟩ := lookOk_spec S l h st0 hi0.inv hwf b st1' hr
      exact ⟨MemoInv.of_alpha_eq hi0 hi' hm' ha' hfi' hfar', hm', ha', hrd', hfw', hfi', hfar', hb⟩
    have ⟨hi1, hm1, ha1, hrd1, hfw1, hfi1, hfar1, hflt⟩ :=
      Ends.filterM_sm_spec hp P st out0 st' hinv hbody
    exact ⟨hi1,
      fun q => by rw [ha1],
      fun q _ => by rw [hm1],
      fun q e hq _ => hm1 ▸ hq,
      hfw1,
      by rw [hfar1]; exact Nat.le_refl _,
      fun j hj => ⟨j, ((hflt j).mp hj).1, rfl, ((hflt j).mp hj).2⟩,
      fun _ => false, fun _ => False, fun _ _ => True,
      fun q => by rw [hrd1]; simp,
      S.postFix_top c _,
      fun h j hh ⟨rfl, hl⟩ => (hflt j).mpr ⟨hh, hl⟩,
      fun _ _ _ => ⟨(fun _ hm => nomatch hm), fun _ _ _ hk => by rcases hk with ⟨_, h1⟩ | ⟨_, h1⟩ <;> cases h1⟩⟩
  | noLT =>
    unfold stepItem at hrun; dsimp only at hrun
    obtain ⟨out0, st1, hbody, hpure⟩ := sm_bind_ok hrun
    obtain ⟨hout0, hst1⟩ := sm_pure_ok hpure; subst st1 hout0
    have hp : ∀ h st0, S.MemoInv ft st0 → ∀ b st1', (A.noLT h).run st0 = .ok (b, st1') →
        S.MemoInv ft st1' ∧ st1'.memo = st0.memo ∧ st1'.active = st0.active ∧ st1'.reads = st0.reads ∧
        st1'.fwd = st0.fwd ∧ st1'.first = st0.first ∧ st1'.far = st0.far ∧
        (b = true ↔ S.NoLT h) := by
      intro h st0 hi0 b st1' hr
      have ⟨hi', hm', ha', hrd', hfw', hfi', hfar', hb⟩ := S.noLT_spec h st0 hi0.inv b st1' hr
      exact ⟨MemoInv.of_alpha_eq hi0 hi' hm' ha' hfi' hfar', hm', ha', hrd', hfw', hfi', hfar', hb⟩
    have ⟨hi1, hm1, ha1, hrd1, hfw1, hfi1, hfar1, hflt⟩ :=
      Ends.filterM_sm_spec hp P st out0 st' hinv hbody
    exact ⟨hi1,
      fun q => by rw [ha1],
      fun q _ => by rw [hm1],
      fun q e hq _ => hm1 ▸ hq,
      hfw1,
      by rw [hfar1]; exact Nat.le_refl _,
      fun j hj => ⟨j, ((hflt j).mp hj).1, rfl, ((hflt j).mp hj).2⟩,
      fun _ => false, fun _ => False, fun _ _ => True,
      fun q => by rw [hrd1]; simp,
      S.postFix_top c _,
      fun h j hh ⟨rfl, hnl⟩ => (hflt j).mpr ⟨hh, hnl⟩,
      fun _ _ _ => ⟨(fun _ hm => nomatch hm), fun _ _ _ hk => by rcases hk with ⟨_, h1⟩ | ⟨_, h1⟩ <;> cases h1⟩⟩
  | empty | onlyIf _ =>
    unfold stepItem at hrun; dsimp only at hrun
    obtain ⟨out0, st1, hbody, hpure⟩ := sm_bind_ok hrun
    obtain ⟨hout0, hst1⟩ := sm_pure_ok hbody; subst out0 st1
    obtain ⟨hout, hst'⟩ := sm_pure_ok hpure; subst out st'
    exact ⟨hinv,
      fun _ => rfl,
      fun _ _ => rfl,
      fun _ _ hq _ => hq,
      rfl, Nat.le_refl _,
      fun j hj => ⟨j, hj, rfl⟩,
      fun _ => false, fun _ => False, fun _ _ => True,
      fun _ => by simp,
      S.postFix_top c _,
      fun h j hh hjeq => hjeq.symm ▸ hh,
      fun _ _ _ => ⟨(fun _ hm => nomatch hm), fun _ _ _ hk => by rcases hk with ⟨_, h1⟩ | ⟨_, h1⟩ <;> cases h1⟩⟩

inductive FwdSetsValid (R : NT → List Param → Nat → Nat → Prop) (s : Src) (ps : List Param) :
    Nat → List Item → Ends → List Ends → Ends → Prop where
  | nil {k P last} :
      (∀ x, last.mem x = P.mem x) →
      FwdSetsValid R s ps k [] P [] last
  | cons {k it rest P before restSets last} (P' : Ends) :
      (∀ x, before.mem x = P.mem x) →
      (∀ j, P'.mem j = true ↔ ∃ h, P.mem h = true ∧ S.ItemStep R s k ps it rest.head? h j) →
      FwdSetsValid R s ps (k + 1) rest P' restSets last →
      FwdSetsValid R s ps k (it :: rest) P (before :: restSets) last

theorem forwardGo_spec {c : Bool} {ft : Option (NT × List Param)}
    {rec : NT → List Param → Nat → SM T Ends} (hrec : S.RecSpec c ft rec)
    (s : Src) (ps : List Param) :
    ∀ (k : Nat) (P : Ends) (is : List Item) (st : St T) (sets : List Ends) (last : Ends) (st' : St T),
      S.MemoInv ft st →
      (c = true → ∀ k_a, st.active.contains k_a = true → k_a.2.2.2.2 = (true && orderedBy A.cx A.g)) →
      (∀ it ∈ is, ItemWF A it) →
      (∀ g gp, ft = some (g, gp) → ∀ h, P.mem h = true → S.SpecPrefix g gp s ps k is h) →
      (forwardGo A rec s ps k P is).run st = .ok ((sets, last), st') →
      S.MemoInv ft st' ∧
      (∀ x, st'.active.contains x = st.active.contains x) ∧
      (∀ x, st.active.contains x = true → st'.memo[x]? = st.memo[x]?) ∧
      (∀ (x : Key) (e : Entry), st.memo[x]? = some e → e.final = true → st'.memo[x]? = some e) ∧
      st'.fwd = st.fwd ∧
      st.far ≤ st'.far ∧
      sets.length = is.length ∧
      (∀ j, last.mem j = true → ∃ h, P.mem h = true ∧ S.SeqRel (S.SpanOfAllow (S.CommitAllow c)) s ps k is h j) ∧
      ∃ rs V M,
        (∀ x, st'.reads.contains x = (st.reads.contains x || rs x)) ∧
        S.PostFix c rs st' V M ∧
        (∀ h j, P.mem h = true → S.SeqRel (S.OfKey c M) s ps k is h j → last.mem j = true) ∧
        (orderedBy A.cx A.g = false →
          ∀ h0 k1 it1 rest1 h1, P.mem h0 = true →
            S.PrefixRel (S.OfKey false M) s ps k is h0 k1 (it1 :: rest1) h1 →
            (∀ j, S.ItemMatch (S.OfKey false M) s k1 ps it1 rest1.head? h1 j → j ≤ st'.far) ∧
            (∀ m args, (altsOf A.cx A.g m).isEmpty = false →
              ((∃ o, it1 = .sym (.nt m args) o) ∨ (∃ ex, it1 = .butNot (.nt m args) ex)) →
              V (key A false m (applyArgs ps args) h1) ∨ rs (key A false m (applyArgs ps args) h1) = true)) := by
  intro k P is
  induction is generalizing k P with
  | nil =>
    intro st sets last st' hinv _ _ _ hrun
    unfold forwardGo at hrun
    obtain ⟨hpEq, rfl⟩ := sm_pure_ok hrun
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj hpEq.symm
    exact ⟨hinv, fun _ => rfl, fun _ _ => rfl, fun _ _ hm _ => hm, rfl, Nat.le_refl _, rfl,
      fun j hj => ⟨j, hj, .nil⟩,
      fun _ => false, fun _ => False, fun _ _ => True,
      fun x => by simp, S.postFix_top c _,
      fun h j hh hsr => by cases hsr; exact hh,
      fun _ _ _ _ _ _ _ hpr => by cases hpr⟩
  | cons it rest ih =>
    intro st sets last st' hinv hactM hwf hpref hrun
    unfold forwardGo at hrun
    obtain ⟨P', st1, hstep, hr1⟩ := sm_bind_ok hrun
    obtain ⟨⟨restSets, last'⟩, st2, hrestRun, hr2⟩ := sm_bind_ok hr1
    have htoPlain : ∀ n' ps' a' b', S.SpanOfAllow (S.CommitAllow c) n' ps' a' b' →
        S.SpanOfAllow (fun _ _ _ _ => True) n' ps' a' b' :=
      fun _ _ _ _ ⟨t, hd⟩ => ⟨t, S.derivesWith_mono_allow (fun _ _ _ _ _ => trivial) hd⟩
    have ⟨hi1, ha1, hm1, hf1, hfw1, hfar1, hu1, rs1, V1, M1, hrd1, hpf1, hl1, hv1⟩ :=
      S.stepItem_spec hrec s k ps it rest P st P' st1 hinv hactM
        (hwf it (List.mem_cons_self ..)) hpref hstep
    have hpref' : ∀ g gp, ft = some (g, gp) → ∀ h1, P'.mem h1 = true → S.SpecPrefix g gp s ps (k + 1) rest h1 := by
      intro g gp hft h1 hh1
      obtain ⟨h0, hh0, hs0⟩ := hu1 h1 hh1
      exact .step (hpref g gp hft h0 hh0) (S.itemStep_mono htoPlain hs0)
    have hactM1 : c = true → ∀ k_a, st1.active.contains k_a = true → k_a.2.2.2.2 = (true && orderedBy A.cx A.g) :=
      fun hc k_a hk => hactM hc k_a ((ha1 k_a) ▸ hk)
    have ⟨hi2, ha2, hm2, hf2, hfw2, hfar2, hlen, hu2, rs2, V2, M2, hrd2, hpf2, hl2, hv2⟩ :=
      ih (k + 1) P' st1 restSets last' st2 hi1 hactM1
        (fun it' hit' => hwf it' (List.mem_cons_of_mem _ hit')) hpref' hrestRun
    obtain ⟨hpEq, hst2⟩ := sm_pure_ok hr2; subst st2
    obtain ⟨hsetsEq, hlastEq⟩ := Prod.mk.inj hpEq.symm; subst hsetsEq last'
    have hpf := (hpf1.mono_state ha2 hm2 hfar2).inter hpf2
    refine ⟨hi2,
      fun x => (ha2 x).trans (ha1 x),
      fun x hx => (hm2 x ((ha1 x).symm ▸ hx)).trans (hm1 x hx),
      fun x e hx he => hf2 x e (hf1 x e hx he) he,
      hfw2.trans hfw1,
      Nat.le_trans hfar1 hfar2,
      by simp [hlen],
      fun j hj => ?_,
      fun x => rs1 x || rs2 x, fun x => V1 x ∨ V2 x, fun x j => M1 x j ∧ M2 x j,
      fun x => by rw [hrd2 x, hrd1 x, Bool.or_assoc],
      hpf, ?_, ?_⟩
    · obtain ⟨h1, hh1, hsr1⟩ := hu2 j hj
      obtain ⟨h0, hh0, hs0⟩ := hu1 h1 hh1
      exact ⟨h0, hh0, .cons hs0 hsr1⟩
    · intro h0 j hh0 hsr
      cases hsr with
      | cons hs0 hsr1 =>
        have hh1 : P'.mem _ = true := hl1 h0 _ hh0 (S.itemStep_mono (fun _ _ _ _ h => h.1) hs0)
        exact hl2 _ j hh1 (S.seqRel_mono (fun _ _ _ _ h => h.2) hsr1)
    · intro hord h0 k1 it1 rest1 h1 hh0 hpr
      cases hpr with
      | refl =>
        obtain ⟨hjb, hch⟩ := hv1 hord h0 hh0
        refine ⟨fun j hj => Nat.le_trans (hjb j (S.itemMatch_mono (fun _ _ _ _ h => h.1) hj)) hfar2,
          fun m args hne hk => ?_⟩
        rcases hch m args hne hk with hv' | hr'
        · exact Or.inl (Or.inl hv')
        · exact Or.inr ((Bool.or_eq_true _ _).mpr (Or.inl hr'))
      | step hs0 hpr1 =>
        have hs0' := S.itemStep_mono (R2 := S.OfKey false M1) (fun _ _ _ _ h => h.1) hs0
        rw [← S.ofKey_eq_false_of_ordered_false hord c M1] at hs0'
        have hhM := hl1 h0 _ hh0 hs0'
        obtain ⟨hjb, hch⟩ := hv2 hord _ k1 it1 rest1 h1 hhM
          (S.prefixRel_mono (fun _ _ _ _ h => h.2) hpr1)
        refine ⟨fun j hj => hjb j (S.itemMatch_mono (fun _ _ _ _ h => h.2) hj),
          fun m args hne hk => ?_⟩
        rcases hch m args hne hk with hv' | hr'
        · exact Or.inl (Or.inr hv')
        · exact Or.inr ((Bool.or_eq_true _ _).mpr (Or.inr hr'))

theorem stepItem_exact_spec
    {allow : NT → List Param → Nat → Src → Prop}
    {rec : NT → List Param → Nat → SM T Ends}
    (hrec : ∀ n ps h st es st', S.MemoInv none st → (rec n ps h).run st = .ok (es, st') →
      S.MemoInv none st' ∧ st'.fwd = st.fwd ∧ ∀ j, es.mem j = true ↔ S.SpanOfAllow allow n ps h j)
    (s : Src) (k0 : Nat) (ps : List Param) (P0 : Ends) (it : Item) (next : Option Item)
    (st0 : St T) (out : Ends) (st1 : St T)
    (hi0 : S.MemoInv none st0) (hwf0 : ItemWF A it)
    (hsr : (stepItem A rec s k0 ps it next P0).run st0 = .ok (out, st1)) :
    S.MemoInv none st1 ∧ st1.fwd = st0.fwd ∧
    (∀ j, out.mem j = true ↔ ∃ h, P0.mem h = true ∧ S.ItemStep (S.SpanOfAllow allow) s k0 ps it next h j) := by
  have hntExact : ∀ n' ps' h' stA esA stB, S.MemoInv none stA →
      (ntEnds A rec n' ps' h').run stA = .ok (esA, stB) →
      S.MemoInv none stB ∧ stB.fwd = stA.fwd ∧
      (∀ j, esA.mem j = true ↔ if !(altsOf A.cx A.g n').isEmpty then S.SpanOfAllow allow n' ps' h' j else S.Leaf n' h' j) := by
    intro n' ps' h' stA esA stB hiA hnr
    unfold ntEnds at hnr
    cases hem : (altsOf A.cx A.g n').isEmpty with
    | false =>
      simp only [hem, Bool.not_false, ↓reduceIte] at hnr ⊢
      exact hrec n' ps' h' stA esA stB hiA hnr
    | true =>
      simp only [hem, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hnr ⊢
      obtain ⟨o, stL, hlf, hp⟩ := sm_bind_ok hnr
      have ⟨hiL, hmL, haL, _, hfwL, hfiL, hfarL, hlo⟩ := S.leaf_spec n' h' stA hiA.inv o stL hlf
      obtain ⟨hes, rfl⟩ := sm_pure_ok hp; subst hes
      refine ⟨MemoInv.of_alpha_eq hiA hiL hmL haL hfiL hfarL, hfwL, fun j => ?_⟩
      rw [Ends.mem_ofList, List.contains_iff_mem]
      rcases hlo with ⟨j0, rfl, hlj0⟩ | ⟨rfl, hno⟩
      · simp only [Option.toList_some, List.mem_singleton]
        exact ⟨fun heq => heq ▸ hlj0, fun hlj => S.leaf_det n' h' j j0 hlj hlj0⟩
      · simp only [Option.toList_none, List.not_mem_nil, false_iff]; exact hno j
  have hfoldExact : ∀ {R : Nat → Nat → Prop} (f : Nat → SM T Ends),
      (∀ h' ∈ P0.toList, ∀ stA esA stB, S.MemoInv none stA → (f h').run stA = .ok (esA, stB) →
        S.MemoInv none stB ∧ stB.fwd = stA.fwd ∧ (∀ j, esA.mem j = true ↔ R h' j)) →
      ∀ (xs : List Nat) (_ : ∀ x ∈ xs, x ∈ P0.toList) stA esA stB, S.MemoInv none stA →
        (foldUnionM f xs).run stA = .ok (esA, stB) →
        S.MemoInv none stB ∧ stB.fwd = stA.fwd ∧ (∀ j, esA.mem j = true ↔ ∃ h' ∈ xs, R h' j) := by
    intro R f hf xs
    induction xs with
    | nil =>
      intro _ stA esA stB hiA hfu; unfold foldUnionM at hfu
      obtain ⟨rfl, rfl⟩ := sm_pure_ok hfu
      exact ⟨hiA, rfl, fun j => by simp [Ends.mem_empty]⟩
    | cons x rxs ihx =>
      intro hsub stA esA stB hiA hfu; unfold foldUnionM at hfu
      obtain ⟨e1, stM, hx, hr1⟩ := sm_bind_ok hfu
      obtain ⟨er, stE, hrr, hr2⟩ := sm_bind_ok hr1
      have ⟨hiM, hfwM, he1⟩ := hf x (hsub x (List.mem_cons_self ..)) stA e1 stM hiA hx
      have ⟨hiE, hfwE, her⟩ := ihx (fun y hy => hsub y (List.mem_cons_of_mem _ hy)) stM er stE hiM hrr
      obtain ⟨heq, hstE⟩ := sm_pure_ok hr2; subst heq stE
      refine ⟨hiE, hfwE.trans hfwM, fun j => ?_⟩
      rw [Ends.mem_union, Bool.or_eq_true, he1 j, her j]
      simp [List.mem_cons, or_and_right, exists_or]
  have hhitNone : ∀ (out0 : Ends) (stM : St T) (_ : S.MemoInv none stM)
      (htail : (if let some j := out0.max? then do A.hit j; pure out0 else pure out0).run stM = .ok (out, st1)),
      S.MemoInv none st1 ∧ st1.fwd = stM.fwd ∧ out = out0 := by
    intro out0 stM hiM htail
    cases hm : out0.max? with
    | none =>
      simp only [hm] at htail
      obtain ⟨heq, rfl⟩ := sm_pure_ok htail
      exact ⟨hiM, rfl, heq.symm⟩
    | some m =>
      simp only [hm] at htail
      obtain ⟨_, stH, hh1, hp2⟩ := sm_bind_ok htail
      have ⟨hiH, hmH, haH, _, hfwH, hfiH, hfarH⟩ := S.hit_spec m stM hiM.inv _ stH hh1
      obtain ⟨heq, rfl⟩ := sm_pure_ok hp2
      exact ⟨MemoInv.of_hit hiM hiH hmH haH hfiH hfarH (fun _ _ h => nomatch h), hfwH, heq.symm⟩
  cases it with
  | sym x o =>
    cases x with
    | t tm =>
      unfold stepItem at hsr; dsimp only at hsr
      obtain ⟨P', stM, hc, hr1⟩ := sm_bind_ok hsr
      obtain ⟨out0, stM', hp, htail⟩ := sm_bind_ok hr1
      obtain ⟨hout0, hstM'⟩ := sm_pure_ok hp; subst stM'
      have htf : ∀ h stA, S.MemoInv none stA → ∀ r stB, (A.term s k0 tm h).run stA = .ok (r, stB) →
          S.MemoInv none stB ∧ stB.memo = stA.memo ∧ stB.active = stA.active ∧ stB.reads = stA.reads ∧
          stB.fwd = stA.fwd ∧ stB.first = stA.first ∧ stB.far = stA.far ∧
          ((∃ j, r = some j ∧ S.Term s k0 tm h j) ∨ (r = none ∧ ∀ j, ¬ S.Term s k0 tm h j)) := by
        intro h stA hiA r stB hr
        have ⟨hi', hm', ha', hrd', hfw', hfi', hfar', ho'⟩ := S.term_spec s k0 tm h stA hiA.inv r stB hr
        exact ⟨MemoInv.of_alpha_eq hiA hi' hm' ha' hfi' hfar', hm', ha', hrd', hfw', hfi', hfar', ho'⟩
      have ⟨hiM, _, _, _, hfwM, _, _, hP'⟩ := S.collectM_rel_spec htf (S.term_det s k0 tm) P0.toList st0 P' stM hi0 hc
      obtain ⟨hi1, hfw1, rfl⟩ := hhitNone out0 stM hiM htail
      refine ⟨hi1, hfw1.trans hfwM, fun j => ?_⟩
      rw [← hout0]
      cases o with
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte, Ends.mem_ofList, List.contains_iff_mem, hP', Ends.mem_toList, ItemStep, ItemMatch, false_and, false_or]
      | true =>
        simp only [↓reduceIte, Ends.mem_union, Bool.or_eq_true, Ends.mem_ofList, List.contains_iff_mem, hP', Ends.mem_toList, ItemStep, ItemMatch, true_and]
        constructor
        · rintro (⟨h, hh, htm⟩ | hjP)
          · exact ⟨h, hh, Or.inr htm⟩
          · exact ⟨j, hjP, Or.inl rfl⟩
        · rintro ⟨h, hh, rfl | htm⟩
          · exact Or.inr hh
          · exact Or.inl ⟨h, hh, htm⟩
    | nt n args =>
      unfold stepItem at hsr; dsimp only at hsr
      obtain ⟨acc, stM, hfU, hr1⟩ := sm_bind_ok hsr
      obtain ⟨out0, stM', hp, htail⟩ := sm_bind_ok hr1
      obtain ⟨hout0, hstM'⟩ := sm_pure_ok hp; subst stM'
      have ⟨hiM, hfwM, hacc⟩ := hfoldExact
        (R := fun h j => S.ItemMatch (S.SpanOfAllow allow) s k0 ps (.sym (.nt n args) o) next h j)
        _ (fun h _ stA esA stB hiA hfr => by
          obtain ⟨ne, stN, hnr, har⟩ := sm_bind_ok hfr
          have ⟨hiN, hfwN, hne⟩ := hntExact n (applyArgs ps args) h stA ne stN hiA hnr
          have ⟨hiA', _, _, _, hfwA, _, _, hadm⟩ := S.admit_spec s.rule.lhs n next h ne stN esA stB hiN har
          refine ⟨hiA', hfwA.trans hfwN, fun j => ?_⟩
          rw [hadm j, hne j]; simp [ItemMatch, and_assoc, and_left_comm, and_comm])
        P0.toList (fun _ h => h) st0 acc stM hi0 hfU
      obtain ⟨hi1, hfw1, rfl⟩ := hhitNone out0 stM hiM htail
      refine ⟨hi1, hfw1.trans hfwM, fun j => ?_⟩
      rw [← hout0]
      cases o with
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte, hacc j, Ends.mem_toList, ItemStep, false_and, false_or]
      | true =>
        simp only [↓reduceIte, Ends.mem_union, Bool.or_eq_true, hacc j, Ends.mem_toList, ItemStep, true_and]
        constructor
        · rintro (⟨h, hh, hm⟩ | hjP)
          · exact ⟨h, hh, Or.inr hm⟩
          · exact ⟨j, hjP, Or.inl rfl⟩
        · rintro ⟨h, hh, rfl | hm⟩
          · exact Or.inr hh
          · exact Or.inl ⟨h, hh, hm⟩
  | butNot base ex =>
    unfold stepItem at hsr; dsimp only at hsr
    obtain ⟨out0, stM, hbody, htail⟩ := sm_bind_ok hsr
    have hexPred : ∀ h j stA, S.MemoInv none stA → ∀ b stB,
        (do let r ← excluded A s k0 ps h j ex; pure (!r)).run stA = .ok (b, stB) →
        S.MemoInv none stB ∧ stB.memo = stA.memo ∧ stB.active = stA.active ∧ stB.reads = stA.reads ∧
        stB.fwd = stA.fwd ∧ stB.first = stA.first ∧ stB.far = stA.far ∧
        (b = true ↔ ¬ S.ExclHolds s k0 ps h j ex) := by
      intro h j stA hiA b stB hexr
      obtain ⟨r, stE, hex1, hpure⟩ := sm_bind_ok hexr
      have ⟨hiE, hmE, haE, hrdE, hfwE, hfiE, hfarE, hre⟩ := excluded_spec S s k0 ps h j ex stA hiA.inv hwf0 r stE hex1
      obtain ⟨hb, rfl⟩ := sm_pure_ok hpure; subst hb
      exact ⟨MemoInv.of_alpha_eq hiA hiE hmE haE hfiE hfarE, hmE, haE, hrdE, hfwE, hfiE, hfarE, by simp [← hre]⟩
    have ⟨hiM, hfwM, hacc⟩ := hfoldExact
      (R := fun h j => S.ItemMatch (S.SpanOfAllow allow) s k0 ps (.butNot base ex) next h j)
      _ (fun h _ stA esA stB hiA hfr => by
        cases base with
        | t x =>
          dsimp only at hfr
          obtain ⟨o, stT, htr, hrA⟩ := sm_bind_ok hfr
          obtain ⟨js, stJ, hp, hflr⟩ := sm_bind_ok hrA
          obtain ⟨hjs, hstJ⟩ := sm_pure_ok hp; subst stJ hjs
          have ⟨hiT, hmT, haT, _, hfwT, hfiT, hfarT, hto⟩ := S.term_spec s k0 x h stA hiA.inv o stT htr
          have ⟨hiF, _, _, _, hfwF, _, _, hflt⟩ :=
            Ends.filterM_sm_spec (hexPred h) _ stT esA stB (MemoInv.of_alpha_eq hiA hiT hmT haT hfiT hfarT) hflr
          refine ⟨hiF, hfwF.trans hfwT, fun j => ?_⟩
          rw [hflt j, Ends.mem_ofList, List.contains_iff_mem]
          rcases hto with ⟨j0, rfl, htj0⟩ | ⟨rfl, hno⟩
          · simp only [Option.toList_some, List.mem_singleton, ItemMatch]
            exact ⟨fun ⟨heq, hnx⟩ => ⟨heq ▸ htj0, hnx⟩, fun ⟨htj, hnx⟩ => ⟨S.term_det s k0 x h j j0 htj htj0, hnx⟩⟩
          · simp only [Option.toList_none, List.not_mem_nil, false_and, ItemMatch, false_iff, not_and]
            intro htj _; exact hno j htj
        | nt n args =>
          dsimp only at hfr
          obtain ⟨ne, stN, hnr, hrA⟩ := sm_bind_ok hfr
          obtain ⟨js, stJ, har, hflr⟩ := sm_bind_ok hrA
          have ⟨hiN, hfwN, hne⟩ := hntExact n (applyArgs ps args) h stA ne stN hiA hnr
          have ⟨hiJ, _, _, _, hfwJ, _, _, hadm⟩ := S.admit_spec s.rule.lhs n none h ne stN js stJ hiN har
          have ⟨hiF, _, _, _, hfwF, _, _, hflt⟩ := Ends.filterM_sm_spec (hexPred h) js stJ esA stB hiJ hflr
          refine ⟨hiF, hfwF.trans (hfwJ.trans hfwN), fun j => ?_⟩
          rw [hflt j, hadm j, hne j]; simp [CondOpt, ItemMatch, and_assoc, and_comm])
      P0.toList (fun _ h => h) st0 out0 stM hi0 hbody
    obtain ⟨hi1, hfw1, rfl⟩ := hhitNone out0 stM hiM htail
    exact ⟨hi1, hfw1.trans hfwM, fun j => by simp [hacc j, Ends.mem_toList, ItemStep]⟩
  | phrase p =>
    unfold stepItem at hsr; dsimp only at hsr
    obtain ⟨P', stM, hc, hr1⟩ := sm_bind_ok hsr
    obtain ⟨out0, stM', hp, htail⟩ := sm_bind_ok hr1
    obtain ⟨hout0, hstM'⟩ := sm_pure_ok hp; subst stM'
    have hpf : ∀ h stA, S.MemoInv none stA → ∀ r stB, (A.phrase p h).run stA = .ok (r, stB) →
        S.MemoInv none stB ∧ stB.memo = stA.memo ∧ stB.active = stA.active ∧ stB.reads = stA.reads ∧
        stB.fwd = stA.fwd ∧ stB.first = stA.first ∧ stB.far = stA.far ∧
        ((∃ j, r = some j ∧ S.Phrase p h j) ∨ (r = none ∧ ∀ j, ¬ S.Phrase p h j)) := by
      intro h stA hiA r stB hr
      have ⟨hi', hm', ha', hrd', hfw', hfi', hfar', ho'⟩ := S.phrase_spec p h stA hiA.inv r stB hr
      exact ⟨MemoInv.of_alpha_eq hiA hi' hm' ha' hfi' hfar', hm', ha', hrd', hfw', hfi', hfar', ho'⟩
    have ⟨hiM, _, _, _, hfwM, _, _, hP'⟩ := S.collectM_rel_spec hpf (S.phrase_det p) P0.toList st0 P' stM hi0 hc
    obtain ⟨hi1, hfw1, rfl⟩ := hhitNone out0 stM hiM htail
    refine ⟨hi1, hfw1.trans hfwM, fun j => ?_⟩
    rw [← hout0]; simp [Ends.mem_ofList, hP', Ends.mem_toList, ItemStep, ItemMatch]
  | lookahead l =>
    unfold stepItem at hsr; dsimp only at hsr
    obtain ⟨out0, stM, hbody, hpure⟩ := sm_bind_ok hsr
    obtain ⟨hout0, hstM⟩ := sm_pure_ok hpure; subst stM hout0
    have hp : ∀ h stA, S.MemoInv none stA → ∀ b stB, (lookOk A l h).run stA = .ok (b, stB) →
        S.MemoInv none stB ∧ stB.memo = stA.memo ∧ stB.active = stA.active ∧ stB.reads = stA.reads ∧
        stB.fwd = stA.fwd ∧ stB.first = stA.first ∧ stB.far = stA.far ∧ (b = true ↔ S.LookHolds l h) := by
      intro h stA hiA b stB hr
      have ⟨hi', hm', ha', hrd', hfw', hfi', hfar', hb⟩ := lookOk_spec S l h stA hiA.inv hwf0 b stB hr
      exact ⟨MemoInv.of_alpha_eq hiA hi' hm' ha' hfi' hfar', hm', ha', hrd', hfw', hfi', hfar', hb⟩
    have ⟨hiM, _, _, _, hfwM, _, _, hflt⟩ := Ends.filterM_sm_spec hp P0 st0 out0 st1 hi0 hbody
    exact ⟨hiM, hfwM, fun j => by
      rw [hflt j]
      exact ⟨fun ⟨hj, hl⟩ => ⟨j, hj, rfl, hl⟩, fun ⟨_, hj, rfl, hl⟩ => ⟨hj, hl⟩⟩⟩
  | noLT =>
    unfold stepItem at hsr; dsimp only at hsr
    obtain ⟨out0, stM, hbody, hpure⟩ := sm_bind_ok hsr
    obtain ⟨hout0, hstM⟩ := sm_pure_ok hpure; subst stM hout0
    have hp : ∀ h stA, S.MemoInv none stA → ∀ b stB, (A.noLT h).run stA = .ok (b, stB) →
        S.MemoInv none stB ∧ stB.memo = stA.memo ∧ stB.active = stA.active ∧ stB.reads = stA.reads ∧
        stB.fwd = stA.fwd ∧ stB.first = stA.first ∧ stB.far = stA.far ∧ (b = true ↔ S.NoLT h) := by
      intro h stA hiA b stB hr
      have ⟨hi', hm', ha', hrd', hfw', hfi', hfar', hb⟩ := S.noLT_spec h stA hiA.inv b stB hr
      exact ⟨MemoInv.of_alpha_eq hiA hi' hm' ha' hfi' hfar', hm', ha', hrd', hfw', hfi', hfar', hb⟩
    have ⟨hiM, _, _, _, hfwM, _, _, hflt⟩ := Ends.filterM_sm_spec hp P0 st0 out0 st1 hi0 hbody
    exact ⟨hiM, hfwM, fun j => by
      rw [hflt j]
      exact ⟨fun ⟨hj, hnl⟩ => ⟨j, hj, rfl, hnl⟩, fun ⟨_, hj, rfl, hnl⟩ => ⟨hj, hnl⟩⟩⟩
  | empty | onlyIf _ =>
    unfold stepItem at hsr; dsimp only at hsr
    obtain ⟨out0, stM, hbody, hpure⟩ := sm_bind_ok hsr
    obtain ⟨hout0, hstM⟩ := sm_pure_ok hbody; subst out0 stM
    obtain ⟨hout, hst1⟩ := sm_pure_ok hpure; subst out st1
    exact ⟨hi0, rfl, fun j => ⟨fun hj => ⟨j, hj, rfl⟩, fun ⟨_, hj, hjeq⟩ => hjeq.symm ▸ hj⟩⟩

theorem forwardGo_exact_spec
    {allow : NT → List Param → Nat → Src → Prop}
    {rec : NT → List Param → Nat → SM T Ends}
    (hrec : ∀ n ps h st es st', S.MemoInv none st → (rec n ps h).run st = .ok (es, st') →
      S.MemoInv none st' ∧ st'.fwd = st.fwd ∧ ∀ j, es.mem j = true ↔ S.SpanOfAllow allow n ps h j)
    (s : Src) (ps : List Param) :
    ∀ (k : Nat) (P : Ends) (is : List Item) (st : St T) (sets : List Ends) (last : Ends) (st' : St T),
      S.MemoInv none st →
      (∀ it ∈ is, ItemWF A it) →
      (forwardGo A rec s ps k P is).run st = .ok ((sets, last), st') →
      S.MemoInv none st' ∧ st'.fwd = st.fwd ∧
      S.FwdSetsValid (S.SpanOfAllow allow) s ps k is P sets last ∧
      (∀ j, last.mem j = true ↔ ∃ h, P.mem h = true ∧ S.SeqRel (S.SpanOfAllow allow) s ps k is h j) := by
  intro k P is
  induction is generalizing k P with
  | nil =>
    intro st sets last st' hi _ hrun
    unfold forwardGo at hrun
    obtain ⟨hpEq, rfl⟩ := sm_pure_ok hrun
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj hpEq.symm
    refine ⟨hi, rfl, .nil (fun _ => rfl), fun j => ?_⟩
    exact ⟨fun hj => ⟨j, hj, .nil⟩, fun ⟨h, hh, hsr⟩ => by cases hsr; exact hh⟩
  | cons it rest ih =>
    intro st sets last st' hi hwf hrun
    unfold forwardGo at hrun
    obtain ⟨P', st1, hs, hr1⟩ := sm_bind_ok hrun
    obtain ⟨⟨restSets, last'⟩, st2, hrr, hr2⟩ := sm_bind_ok hr1
    have ⟨hi1, hfw1, hP'⟩ := S.stepItem_exact_spec hrec s k ps P it rest.head? st P' st1 hi
      (hwf it (List.mem_cons_self ..)) hs
    have ⟨hi2, hfw2, hfsv, hlast⟩ :=
      ih (k + 1) P' st1 restSets last' st2 hi1 (fun it' h => hwf it' (List.mem_cons_of_mem _ h)) hrr
    obtain ⟨hpEq, hst2⟩ := sm_pure_ok hr2; subst st2
    obtain ⟨hsetsEq, hlastEq⟩ := Prod.mk.inj hpEq.symm; subst hsetsEq last'
    refine ⟨hi2, hfw2.trans hfw1, .cons P' (fun _ => rfl) hP' hfsv, fun j => ?_⟩
    rw [hlast j]
    constructor
    · rintro ⟨h1, hh1, hsr1⟩
      obtain ⟨h0, hh0, hs0⟩ := (hP' h1).mp hh1
      exact ⟨h0, hh0, .cons hs0 hsr1⟩
    · rintro ⟨h0, hh0, hsr⟩
      cases hsr with
      | cons hs0 hsr1 => exact ⟨_, (hP' _).mpr ⟨h0, hh0, hs0⟩, hsr1⟩

theorem ruleEnds_spec (hok : parseTablesOk = true) (hg : A.g = .syntactic ∨ A.g ∈ codeGrammars)
    {c : Bool} {ft : Option (NT × List Param)}
    {rec : NT → List Param → Nat → SM T Ends} (hrec : S.RecSpec c ft rec)
    (n : NT) (es : List Src) (ps : List Param) (i : Nat)
    (st : St T) (out : Ends) (st' : St T)
    (hinv : S.MemoInv ft st)
    (hactM : c = true → ∀ k_a, st.active.contains k_a = true → k_a.2.2.2.2 = (true && orderedBy A.cx A.g))
    (hes : ∀ e ∈ es, e ∈ altsOf A.cx A.g n ∧ S.CommitAllow c n ps i e ∧ e.alt.guard.all (Guard.holds ps) = true)
    (hopen : ∀ g gp, ft = some (g, gp) → S.SpecOpen g gp n ps i)
    (hrun : (ruleEnds A rec es ps i).run st = .ok (out, st')) :
    S.MemoInv ft st' ∧
    (∀ x, st'.active.contains x = st.active.contains x) ∧
    (∀ x, st.active.contains x = true → st'.memo[x]? = st.memo[x]?) ∧
    (∀ (x : Key) (e : Entry), st.memo[x]? = some e → e.final = true → st'.memo[x]? = some e) ∧
    st'.fwd = st.fwd ∧
    st.far ≤ st'.far ∧
    (∀ j, out.mem j = true → ∃ t, S.ModeDerives c n ps i j t) ∧
    ∃ rs V M,
      (∀ x, st'.reads.contains x = (st.reads.contains x || rs x)) ∧
      S.PostFix c rs st' V M ∧
      (∀ e ∈ es, ∀ j, S.SeqRel (S.OfKey c M) e ps 0 e.alt.rhs i j → out.mem j = true) ∧
      (orderedBy A.cx A.g = false → ∀ e ∈ es,
        ∀ k1 it1 rest1 h1,
          S.PrefixRel (S.OfKey false M) e ps 0 e.alt.rhs i k1 (it1 :: rest1) h1 →
          (∀ j, S.ItemMatch (S.OfKey false M) e k1 ps it1 rest1.head? h1 j → j ≤ st'.far) ∧
          (∀ m args, (altsOf A.cx A.g m).isEmpty = false →
            ((∃ o, it1 = .sym (.nt m args) o) ∨ (∃ ex, it1 = .butNot (.nt m args) ex)) →
            V (key A false m (applyArgs ps args) h1) ∨ rs (key A false m (applyArgs ps args) h1) = true)) := by
  unfold ruleEnds at hrun
  have hone : ∀ e ∈ es, ∀ st0 es0 st1, S.MemoInv ft st0 →
      (c = true → ∀ k_a, st0.active.contains k_a = true → k_a.2.2.2.2 = (true && orderedBy A.cx A.g)) →
      (Prod.snd <$> forward A rec e ps i e.alt.rhs).run st0 = .ok (es0, st1) →
      S.MemoInv ft st1 ∧
      (∀ k, st1.active.contains k = st0.active.contains k) ∧
      (∀ k, st0.active.contains k = true → st1.memo[k]? = st0.memo[k]?) ∧
      (∀ (k : Key) (ef : Entry), st0.memo[k]? = some ef → ef.final = true → st1.memo[k]? = some ef) ∧
      st1.fwd = st0.fwd ∧
      st0.far ≤ st1.far ∧
      (∀ j, es0.mem j = true → ∃ t, S.ModeDerives c n ps i j t) ∧
      ∃ rs V M,
        (∀ k, st1.reads.contains k = (st0.reads.contains k || rs k)) ∧
        S.PostFix c rs st1 V M ∧
        (∀ j, S.SeqRel (S.OfKey c M) e ps 0 e.alt.rhs i j → es0.mem j = true) ∧
        (orderedBy A.cx A.g = false →
          ∀ k1 it1 rest1 h1,
            S.PrefixRel (S.OfKey false M) e ps 0 e.alt.rhs i k1 (it1 :: rest1) h1 →
            (∀ j, S.ItemMatch (S.OfKey false M) e k1 ps it1 rest1.head? h1 j → j ≤ st1.far) ∧
            (∀ m args, (altsOf A.cx A.g m).isEmpty = false →
              ((∃ o, it1 = .sym (.nt m args) o) ∨ (∃ ex, it1 = .butNot (.nt m args) ex)) →
              V (key A false m (applyArgs ps args) h1) ∨ rs (key A false m (applyArgs ps args) h1) = true)) := by
    intro e heMem st0 es0 st1 hi0 hact0 hfr
    obtain ⟨heAlts, heAllow, heGrd⟩ := hes e heMem
    change (do let p ← forward A rec e ps i e.alt.rhs; pure p.2).run st0 = .ok (es0, st1) at hfr
    obtain ⟨⟨sets, last⟩, stF, hfwRun, hpure⟩ := sm_bind_ok hfr
    obtain ⟨hes0, rfl⟩ := sm_pure_ok hpure; dsimp only at hes0; subst hes0
    have hpref0 : ∀ g gp, ft = some (g, gp) → ∀ h, (Ends.single i).mem h = true → S.SpecPrefix g gp e ps 0 e.alt.rhs h := by
      intro g gp hft h hh
      rw [Ends.mem_single, beq_iff_eq] at hh; subst hh
      exact .enter e (hopen g gp hft) heAlts heGrd
    have ⟨hi1, ha1, hm1, hf1, hfw1, hfar1, _, hu1, rs, V, M, hrd1, hpf1, hl1, hv1⟩ :=
      S.forwardGo_spec hrec e ps 0 (.single i) e.alt.rhs st0 sets last st1 hi0 hact0
        (fun it hit => itemWF_of_mem A hok hg heAlts hit) hpref0 hfwRun
    have hsi : (Ends.single i).mem i = true := by simp [Ends.mem_single]
    refine ⟨hi1, ha1, hm1, hf1, hfw1, hfar1, fun j hj => ?_, rs, V, M, hrd1, hpf1,
      fun j hsr => hl1 i j hsi hsr,
      fun hord k1 it1 rest1 h1 hpr => hv1 hord i k1 it1 rest1 h1 hsi hpr⟩
    obtain ⟨h0, hh0, hsr⟩ := hu1 j hj
    rw [Ends.mem_single, beq_iff_eq] at hh0; subst hh0
    exact S.derivesWith_of_seqRel hok heAlts heAllow heGrd hsr
  induction es generalizing st out with
  | nil =>
    unfold foldUnionM at hrun
    obtain ⟨hout, rfl⟩ := sm_pure_ok hrun; subst hout
    exact ⟨hinv, fun _ => rfl, fun _ _ => rfl, fun _ _ hm _ => hm, rfl, Nat.le_refl _,
      (fun j hj => nomatch hj),
      fun _ => false, fun _ => False, fun _ _ => True,
      fun x => by simp, S.postFix_top c _,
      (fun _ he => nomatch he), (fun _ _ he => nomatch he)⟩
  | cons e rest ih =>
    unfold foldUnionM at hrun
    obtain ⟨e1, st1, hx, hr1⟩ := sm_bind_ok hrun
    obtain ⟨er, st2, hrr, hr2⟩ := sm_bind_ok hr1
    obtain ⟨hout, rfl⟩ := sm_pure_ok hr2; subst hout
    have ⟨hi1, ha1, hm1, hf1, hfw1, hfar1, hu1, rs1, V1, M1, hrd1, hpf1, hl1, hv1⟩ :=
      hone e (List.mem_cons_self ..) st e1 st1 hinv hactM hx
    have hactM1 : c = true → ∀ k_a, st1.active.contains k_a = true → k_a.2.2.2.2 = (true && orderedBy A.cx A.g) :=
      fun hc k_a hk => hactM hc k_a ((ha1 k_a) ▸ hk)
    have ⟨hi2, ha2, hm2, hf2, hfw2, hfar2, hu2, rs2, V2, M2, hrd2, hpf2, hl2, hv2⟩ :=
      ih st1 er hi1 hactM1 (fun e' he' => hes e' (List.mem_cons_of_mem _ he')) hrr
        (fun e' he' => hone e' (List.mem_cons_of_mem _ he'))
    have hpf := (hpf1.mono_state ha2 hm2 hfar2).inter hpf2
    refine ⟨hi2,
      fun k => (ha2 k).trans (ha1 k),
      fun k hk => (hm2 k ((ha1 k).symm ▸ hk)).trans (hm1 k hk),
      fun k ef hk hef => hf2 k ef (hf1 k ef hk hef) hef,
      hfw2.trans hfw1,
      Nat.le_trans hfar1 hfar2,
      fun j hj => ?_,
      fun k => rs1 k || rs2 k, fun k => V1 k ∨ V2 k, fun k j => M1 k j ∧ M2 k j,
      fun k => by rw [hrd2 k, hrd1 k, Bool.or_assoc],
      hpf, ?_, ?_⟩
    · rw [Ends.mem_union, Bool.or_eq_true] at hj
      rcases hj with hj1 | hj2
      · exact hu1 j hj1
      · exact hu2 j hj2
    · intro e' he' j hsr
      rw [Ends.mem_union, Bool.or_eq_true]
      rcases List.mem_cons.mp he' with rfl | he'
      · exact Or.inl (hl1 j (S.seqRel_mono (fun _ _ _ _ h => h.1) hsr))
      · exact Or.inr (hl2 e' he' j (S.seqRel_mono (fun _ _ _ _ h => h.2) hsr))
    · intro hord e' he' k1 it1 rest1 h1 hpr
      rcases List.mem_cons.mp he' with rfl | he'
      · obtain ⟨hjb, hch⟩ := hv1 hord k1 it1 rest1 h1 (S.prefixRel_mono (fun _ _ _ _ h => h.1) hpr)
        refine ⟨fun j hj => Nat.le_trans (hjb j (S.itemMatch_mono (fun _ _ _ _ h => h.1) hj)) hfar2,
          fun m args hne hk => ?_⟩
        rcases hch m args hne hk with hv' | hr'
        · exact Or.inl (Or.inl hv')
        · exact Or.inr ((Bool.or_eq_true _ _).mpr (Or.inl hr'))
      · obtain ⟨hjb, hch⟩ := hv2 hord e' he' k1 it1 rest1 h1 (S.prefixRel_mono (fun _ _ _ _ h => h.2) hpr)
        refine ⟨fun j hj => hjb j (S.itemMatch_mono (fun _ _ _ _ h => h.2) hj),
          fun m args hne hk => ?_⟩
        rcases hch m args hne hk with hv' | hr'
        · exact Or.inl (Or.inr hv')
        · exact Or.inr ((Bool.or_eq_true _ _).mpr (Or.inr hr'))

/-! ## Soundness of `leftAll` / `growLeft` -/

theorem leftAll_sound (hok : parseTablesOk = true) (hg : A.g = .syntactic ∨ A.g ∈ codeGrammars)
    {c : Bool} {ft : Option (NT × List Param)}
    {rec : NT → List Param → Nat → SM T Ends} (hrec : S.RecSpec c ft rec)
    (n : NT) (ps : List Param) (i : Nat) (dir : List Src) (P : Ends)
    (st : St T) (out : Ends) (st' : St T)
    (hinv : S.MemoInv ft st)
    (hactM : c = true → ∀ k_a, st.active.contains k_a = true → k_a.2.2.2.2 = (true && orderedBy A.cx A.g))
    (hdir : ∀ e ∈ dir, e ∈ altsOf A.cx A.g n ∧ S.CommitAllow c n ps i e ∧
      e.alt.guard.all (Guard.holds ps) = true ∧ leftRec n ps e = true)
    (hPsound : ∀ h, P.mem h = true → ∃ t, S.ModeDerives c n ps i h t)
    (hopen : ∀ g gp, ft = some (g, gp) → S.SpecOpen g gp n ps i)
    (hrun : (leftAll A rec n ps i dir P).run st = .ok (out, st')) :
    S.MemoInv ft st' ∧
    (∀ x, st'.active.contains x = st.active.contains x) ∧
    (∀ x, st.active.contains x = true → st'.memo[x]? = st.memo[x]?) ∧
    (∀ (x : Key) (e : Entry), st.memo[x]? = some e → e.final = true → st'.memo[x]? = some e) ∧
    st'.fwd = st.fwd ∧
    st.far ≤ st'.far ∧
    (∀ j, out.mem j = true → ∃ t, S.ModeDerives c n ps i j t) := by
  have htoPlain : ∀ n' ps' a' b', S.SpanOfAllow (S.CommitAllow c) n' ps' a' b' →
      S.SpanOfAllow (fun _ _ _ _ => True) n' ps' a' b' :=
    fun _ _ _ _ ⟨t, hd⟩ => ⟨t, S.derivesWith_mono_allow (fun _ _ _ _ _ => trivial) hd⟩
  induction dir generalizing st out with
  | nil =>
    unfold leftAll foldUnionM at hrun
    obtain ⟨hout, rfl⟩ := sm_pure_ok hrun; subst hout
    exact ⟨hinv, fun _ => rfl, fun _ _ => rfl, fun _ _ hm _ => hm, rfl, Nat.le_refl _,
      fun j hj => nomatch hj⟩
  | cons e rest ih =>
    unfold leftAll foldUnionM at hrun
    obtain ⟨e1, st1, hx, hr1⟩ := sm_bind_ok hrun
    obtain ⟨er, st2, hrr, hr2⟩ := sm_bind_ok hr1
    obtain ⟨hout, rfl⟩ := sm_pure_ok hr2; subst hout
    obtain ⟨heAlts, heAllow, heGrd, heLR⟩ := hdir e (List.mem_cons_self ..)
    unfold leftRec at heLR
    cases hrhs : e.alt.rhs with
    | nil => rw [hrhs] at heLR; cases heLR
    | cons firstIt tail =>
      rw [hrhs] at heLR
      cases firstIt with
      | lookahead _ | noLT | empty | butNot _ _ | onlyIf _ | phrase _ => simp at heLR
      | sym sym0 opt0 =>
        cases opt0 with
        | true => simp at heLR
        | false =>
          cases sym0 with
          | t _ => simp at heLR
          | nt m args =>
            simp only [Bool.and_eq_true, beq_iff_eq] at heLR
            obtain ⟨rfl, hpbits⟩ := heLR
            have hne : (altsOf A.cx A.g m).isEmpty = false := by
              rw [List.isEmpty_eq_false_iff]; intro hnil; rw [hnil] at heAlts; cases heAlts
            unfold leftStep at hx
            rw [hrhs] at hx; dsimp only [List.drop] at hx
            obtain ⟨Padm, stA, hadmRun, hx1⟩ := sm_bind_ok hx
            have ⟨hiA, hmA, haA, hrdA, hfwA, hfiA, hfarA, hadm⟩ :=
              S.admit_spec e.rule.lhs m tail.head? i P st Padm stA hinv hadmRun
            have hPadmHit : ∀ g gp, ft = some (g, gp) → ∀ h, Padm.mem h = true →
                S.SpecHit g gp h ∧ S.SpecPrefix g gp e ps 1 tail h := by
              intro g gp hft h hh
              obtain ⟨hhP, hkeep, hco⟩ := (hadm h).mp hh
              have ⟨t0, hd0⟩ := (S.modeDerives_exists_paramBits hpbits.symm).mp (hPsound h hhP)
              have hsp0 : S.SpanOfAllow (fun _ _ _ _ => True) m (applyArgs ps args) i h :=
                htoPlain _ _ _ _ ⟨t0, hd0⟩
              have hp0 : S.SpecPrefix g gp e ps 0 (.sym (.nt m args) false :: tail) i :=
                hrhs ▸ .enter e (hopen g gp hft) heAlts heGrd
              have hm0 : S.ItemMatch (S.SpanOfAllow (fun _ _ _ _ => True)) e 0 ps (.sym (.nt m args) false) tail.head? i h := by
                simp [ItemMatch, hkeep, hco, hne, hsp0]
              exact ⟨.matchAt hp0 hm0, .step hp0 (Or.inr hm0)⟩
            have hhitMid : ∃ stH,
                S.MemoInv ft stH ∧ stH.memo = stA.memo ∧ stH.active = stA.active ∧
                stH.fwd = stA.fwd ∧ stA.far ≤ stH.far ∧
                (forwardGo A rec e ps 1 Padm tail >>= fun p => pure p.2).run stH = .ok (e1, st1) := by
              cases hmP : Padm.max? with
              | none =>
                simp only [hmP] at hx1
                exact ⟨stA, hiA, rfl, rfl, rfl, Nat.le_refl _, hx1⟩
              | some mj =>
                simp only [hmP] at hx1
                obtain ⟨_, stH, hhRun, hfgRun⟩ := sm_bind_ok hx1
                obtain ⟨hmjMem, _⟩ := Ends.max?_some hmP
                have ⟨hiH, hmH, haH, _, hfwH, hfiH, hfarH⟩ := S.hit_spec mj stA hiA.inv _ stH hhRun
                exact ⟨stH,
                  MemoInv.of_hit hiA hiH hmH haH hfiH hfarH (fun g gp hft => (hPadmHit g gp hft mj hmjMem).1),
                  hmH, haH, hfwH, by rw [hfarH]; exact Nat.le_max_left _ _, hfgRun⟩
            obtain ⟨stH, hiH, hmH, haH, hfwH, hfarH, hfgRun⟩ := hhitMid
            obtain ⟨⟨_, last1⟩, _, hfwg, hpureF⟩ := sm_bind_ok hfgRun
            obtain ⟨he1, rfl⟩ := sm_pure_ok hpureF; dsimp only at he1; subst he1
            have hactH : c = true → ∀ k_a, stH.active.contains k_a = true → k_a.2.2.2.2 = (true && orderedBy A.cx A.g) :=
              fun hc k_a hk => hactM hc k_a (by rw [← haA, ← haH]; exact hk)
            have ⟨hi1, ha1, hm1, hf1, hfw1, hfar1, _, hu1, _⟩ :=
              S.forwardGo_spec hrec e ps 1 Padm tail stH _ last1 st1 hiH hactH
                (fun it' hit' => itemWF_of_mem A hok hg heAlts (hrhs ▸ List.mem_cons_of_mem _ hit'))
                (fun g gp hft h hh => (hPadmHit g gp hft h hh).2) hfwg
            have hact1 : c = true → ∀ k_a, st1.active.contains k_a = true → k_a.2.2.2.2 = (true && orderedBy A.cx A.g) :=
              fun hc k_a hk => hactH hc k_a ((ha1 k_a) ▸ hk)
            have ⟨hi2, ha2, hm2, hf2, hfw2, hfar2, hu2⟩ :=
              ih st1 er hi1 hact1 (fun e' he' => hdir e' (List.mem_cons_of_mem _ he')) hrr
            refine ⟨hi2,
              fun x => (ha2 x).trans ((ha1 x).trans (by rw [haH, haA])),
              fun x hx => by rw [hm2 x (by rw [ha1 x, haH, haA]; exact hx), hm1 x (by rw [haH, haA]; exact hx), hmH, hmA],
              fun x ef hx hef => hf2 x ef (hf1 x ef ((hmH.trans hmA) ▸ hx) hef) hef,
              hfw2.trans (hfw1.trans (hfwH.trans hfwA)),
              Nat.le_trans (by rw [← hfarA]; exact hfarH) (Nat.le_trans hfar1 hfar2),
              fun j hj => ?_⟩
            rw [Ends.mem_union, Bool.or_eq_true] at hj
            rcases hj with hj1 | hj2
            · obtain ⟨h, hhPadm, hsrTail⟩ := hu1 j hj1
              obtain ⟨hhP, hkeep, hco⟩ := (hadm h).mp hhPadm
              have ⟨t0, hd0⟩ := (S.modeDerives_exists_paramBits hpbits.symm).mp (hPsound h hhP)
              have hs0 : S.ItemStep (S.SpanOfAllow (S.CommitAllow c)) e 0 ps (.sym (.nt m args) false) tail.head? i h :=
                Or.inr ⟨hkeep, hco, by simp only [hne, Bool.not_false, ↓reduceIte]; exact ⟨t0, hd0⟩⟩
              have hsrFull : S.SeqRel (S.SpanOfAllow (S.CommitAllow c)) e ps 0 e.alt.rhs i j :=
                hrhs ▸ .cons hs0 hsrTail
              exact S.derivesWith_of_seqRel hok heAlts heAllow heGrd hsrFull
            · exact hu2 j hj2

theorem growLeft_sound (hok : parseTablesOk = true) (hg : A.g = .syntactic ∨ A.g ∈ codeGrammars)
    {c : Bool} {ft : Option (NT × List Param)}
    {rec : NT → List Param → Nat → SM T Ends} (hrec : S.RecSpec c ft rec)
    (n : NT) (ps : List Param) (i : Nat) (dir : List Src)
    (hdir : ∀ e ∈ dir, e ∈ altsOf A.cx A.g n ∧ S.CommitAllow c n ps i e ∧
      e.alt.guard.all (Guard.holds ps) = true ∧ leftRec n ps e = true)
    (hopen : ∀ g gp, ft = some (g, gp) → S.SpecOpen g gp n ps i) :
    ∀ (f : Nat) (cur delta : Ends) (st : St T) (res : Ends) (gen : Bool) (st' : St T),
      S.MemoInv ft st →
      st.active.contains (key A c n ps i) = true →
      (c = true → ∀ k_a, st.active.contains k_a = true → k_a.2.2.2.2 = (true && orderedBy A.cx A.g)) →
      (∀ j, cur.mem j = true → ∃ t, S.ModeDerives c n ps i j t) →
      (∀ j, delta.mem j = true → ∃ t, S.ModeDerives c n ps i j t) →
      (growLeft A rec n ps i dir (key A c n ps i) f cur delta).run st = .ok ((res, gen), st') →
      S.MemoInv ft st' ∧
      st'.active.contains (key A c n ps i) = true ∧
      (∀ x, st'.active.contains x = st.active.contains x) ∧
      (∀ x, x ≠ key A c n ps i → st.active.contains x = true → st'.memo[x]? = st.memo[x]?) ∧
      (∀ (x : Key) (e : Entry), st.memo[x]? = some e → e.final = true → st'.memo[x]? = some e) ∧
      st'.fwd = st.fwd ∧
      st.far ≤ st'.far ∧
      (∀ j, res.mem j = true → ∃ t, S.ModeDerives c n ps i j t)
  | 0, _, _, st, _, _, _, _, _, _, _, _, hrun => by
    unfold growLeft at hrun; rw [sm_run_throw] at hrun; cases hrun
  | f + 1, cur, delta, st, res, gen, st', hinv, hactK, hactM, hcurS, hdelS, hrun => by
    let k := key A c n ps i
    unfold growLeft at hrun
    obtain ⟨_, stT, htk, hr1⟩ := sm_bind_ok hrun
    have ⟨hiT, hmT, haT, _, hfwT, hfiT, hfarT⟩ := hinv.of_tick htk
    obtain ⟨add, stA, hlRun, hr2⟩ := sm_bind_ok hr1
    have ⟨hiA, haA, hmA, hfA, hfwA, hfarA, haddS⟩ :=
      S.leftAll_sound hok hg hrec n ps i dir delta stT add stA hiT
        (haT ▸ hactM) hdir hdelS hopen hlRun
    have hr3 := sm_get_bind_ok hr2
    have haKA : stA.active.contains k = true := by rw [haA k, haT]; exact hactK
    cases hrds : stA.reads.isEmpty with
    | false =>
      simp only [hrds, Bool.false_eq_true, ↓reduceIte] at hr3
      obtain ⟨hpEq, rfl⟩ := sm_pure_ok hr3
      obtain ⟨_, _⟩ := Prod.mk.inj hpEq.symm; subst res gen
      exact ⟨hiA, haKA, fun x => by rw [haA x, haT],
        fun x _ hx => by rw [hmA x (haT ▸ hx), hmT],
        fun x e hx he => hfA x e (hmT ▸ hx) he,
        hfwA.trans hfwT, by rw [← hfarT]; exact hfarA, hcurS⟩
    | true =>
      simp only [hrds, ↓reduceIte] at hr3
      cases hde : (add.diff cur).isEmpty with
      | true =>
        simp only [hde, ↓reduceIte] at hr3
        obtain ⟨hpEq, rfl⟩ := sm_pure_ok hr3
        obtain ⟨_, _⟩ := Prod.mk.inj hpEq.symm; subst res gen
        exact ⟨hiA, haKA, fun x => by rw [haA x, haT],
          fun x _ hx => by rw [hmA x (haT ▸ hx), hmT],
          fun x e hx he => hfA x e (hmT ▸ hx) he,
          hfwA.trans hfwT, by rw [← hfarT]; exact hfarA, hcurS⟩
      | false =>
        simp only [hde, Bool.false_eq_true, ↓reduceIte] at hr3
        obtain ⟨_, stM, hmod, hr4⟩ := sm_bind_ok hr3
        obtain ⟨_, rfl⟩ := sm_pure_ok hmod
        have hdel'S : ∀ j, (add.diff cur).mem j = true → ∃ t, S.ModeDerives c n ps i j t := by
          intro j hj; rw [Ends.mem_diff, Bool.and_eq_true] at hj; exact haddS j hj.1
        have hcur'S : ∀ j, (cur.union (add.diff cur)).mem j = true → ∃ t, S.ModeDerives c n ps i j t := by
          intro j hj; rw [Ends.mem_union, Bool.or_eq_true] at hj
          exact hj.elim (hcurS j) (hdel'S j)
        have hiM : S.MemoInv ft { stA with memo := stA.memo.insert k ⟨cur.union (add.diff cur), false, stA.far⟩ } :=
          hiA.insert_provisional hok (fun e0 he0 => hiA.active_provisional k e0 haKA he0)
            hcur'S (fun g gp hft => (hiA.far_sound g gp hft).1)
        have ⟨hi2, haK2, ha2, hm2, hf2, hfw2, hfar2, hresS⟩ :=
          growLeft_sound hok hg hrec n ps i dir hdir hopen f (cur.union (add.diff cur)) (add.diff cur)
            _ res gen st' hiM haKA (fun hc k_a hk => (haT ▸ hactM) hc k_a ((haA k_a) ▸ hk))
            hcur'S hdel'S hr4
        refine ⟨hi2, haK2,
          fun x => (ha2 x).trans (by rw [haA x, haT]),
          fun x hne hx => ?_,
          fun x e hx he => ?_,
          hfw2.trans (hfwA.trans hfwT),
          Nat.le_trans (by rw [← hfarT]; exact hfarA) hfar2,
          hresS⟩
        · have hxA : stA.active.contains x = true := by rw [haA x, haT]; exact hx
          have h1 := hm2 x hne hxA
          dsimp only at h1
          rw [hm_insert_ne _ _ hne.symm] at h1
          rw [h1, hmA x (haT ▸ hx), hmT]
        · have hxA := hfA x e (hmT ▸ hx) he
          have hne : k ≠ x := by
            rintro rfl; rw [hiA.active_provisional k e haKA hxA] at he; cases he
          refine hf2 x e ?_ he
          dsimp only
          rw [hm_insert_ne _ _ hne]
          exact hxA

/-! ## Closing `k` from a `ruleEnds` pass & `growAll` / `viaLeft` -/

theorem close_key_postFix (hok : parseTablesOk = true)
    {c : Bool} {rs : Key → Bool} {st : St T} {V : Key → Prop} {M : Key → Nat → Prop}
    {n : NT} {ps : List Param} {i : Nat} {es : List Src} {chk cur : Ends}
    (hpf : S.PostFix c rs st V M)
    (hmk : (∀ k0, rs k0 = false) ∨ ∃ f0, st.memo[key A c n ps i]? = some ⟨cur, false, f0⟩)
    (hmemoSub : ∀ e0, st.memo[key A c n ps i]? = some e0 → ∀ j, e0.ends.mem j = true → cur.mem j = true)
    (hesAll : ∀ n' ps' i', key A c n' ps' i' = key A c n ps i →
      ∀ s ∈ altsOf A.cx A.g n', S.CommitAllow c n' ps' i' s → s.alt.guard.all (Guard.holds ps') = true → s ∈ es)
    (hchkComplete : ∀ e ∈ es, ∀ j, S.SeqRel (S.OfKey c M) e ps 0 e.alt.rhs i j → chk.mem j = true)
    (hchkSub : ∀ j, chk.mem j = true → cur.mem j = true)
    (hfarChk : orderedBy A.cx A.g = false → ∀ e ∈ es,
      ∀ k1 it1 rest1 h1,
        S.PrefixRel (S.OfKey false M) e ps 0 e.alt.rhs i k1 (it1 :: rest1) h1 →
        (∀ j, S.ItemMatch (S.OfKey false M) e k1 ps it1 rest1.head? h1 j → j ≤ st.far) ∧
        (∀ m args, (altsOf A.cx A.g m).isEmpty = false →
          ((∃ o, it1 = .sym (.nt m args) o) ∨ (∃ ex, it1 = .butNot (.nt m args) ex)) →
          V (key A false m (applyArgs ps args) h1) ∨ rs (key A false m (applyArgs ps args) h1) = true)) :
    let k := key A c n ps i
    let rs' := fun x => !(k == x) && rs x
    let V' := fun x => V x ∨ x = k
    let M' := fun x j => M x j ∧ (x = k → cur.mem j = true)
    S.PostFix c rs' st V' M' ∧
    (∀ j, M' k j → cur.mem j = true) ∧
    (orderedBy A.cx A.g = false → V' (key A false n ps i)) := by
  intro k rs' V' M'
  have hvisitK : ∀ hord : orderedBy A.cx A.g = false, ∀ n' ps' i' s k0 it0 rest0 h0,
      key A false n' ps' i' = k → s ∈ altsUnder A n' ps' →
      S.PrefixRel (S.OfKey false M') s ps' 0 s.alt.rhs i' k0 (it0 :: rest0) h0 →
      (∀ j, S.ItemMatch (S.OfKey false M') s k0 ps' it0 rest0.head? h0 j → j ≤ st.far) ∧
      (∀ m args, (altsOf A.cx A.g m).isEmpty = false →
        ((∃ o, it0 = .sym (.nt m args) o) ∨ (∃ ex, it0 = .butNot (.nt m args) ex)) →
        V' (key A false m (applyArgs ps' args) h0) ∨ rs' (key A false m (applyArgs ps' args) h0) = true) := by
    intro hord n' ps' i' s k0 it0 rest0 h0 hk1 hsU hpr
    have hkEq : k = key A false n ps i := key_eq_false_of_ordered_false hord c n ps i
    obtain ⟨rfl, hpbits, rfl, _⟩ := key_inj (hk1.trans hkEq)
    obtain ⟨hsAlts, hsGrd⟩ := (mem_altsUnder_iff A n' ps' s).mp hsU
    have hse : s ∈ es := by
      refine hesAll n' ps' i' (by rw [key_eq_false_of_ordered_false hord c]; exact hk1) s hsAlts ?_ hsGrd
      unfold CommitAllow; rw [orderedNts_nil_of_ordered_false hok hord]; simp
    have hprM : S.PrefixRel (S.OfKey false M) s ps 0 s.alt.rhs i' k0 (it0 :: rest0) h0 :=
      S.prefixRel_ofKey_paramBits hpbits (S.prefixRel_mono (fun _ _ _ _ h => h.1) hpr)
    obtain ⟨hjb, hch⟩ := hfarChk hord s hse k0 it0 rest0 h0 hprM
    refine ⟨fun j hj => hjb j (S.itemMatch_ofKey_paramBits hpbits (S.itemMatch_mono (fun _ _ _ _ h => h.1) hj)),
      fun m args hne hkind => ?_⟩
    rw [applyArgs_eq_of_contains (contains_eq_of_paramBits hpbits)]
    rcases hch m args hne hkind with hv' | hr'
    · exact Or.inl (Or.inl hv')
    · by_cases hck : k == key A false m (applyArgs ps args) h0
      · rw [beq_iff_eq] at hck; exact Or.inl (Or.inr hck.symm)
      · exact Or.inr (by simp [rs', hck, hr'])
  have hpf' : S.PostFix c rs' st V' M' :=
    { rs_mode := fun k1 hr => by simp only [rs', Bool.and_eq_true] at hr; exact hpf.rs_mode k1 hr.2
      rs_sub_active := fun k1 hr => by simp only [rs', Bool.and_eq_true] at hr; exact hpf.rs_sub_active k1 hr.2
      rs_upper := fun k1 hr => by
        simp only [rs', Bool.and_eq_true] at hr
        obtain ⟨e1, hm1, hu1⟩ := hpf.rs_upper k1 hr.2
        exact ⟨e1, hm1, fun j hj => hu1 j hj.1⟩
      active_lower := fun k1 e1 ha1 hm1 j hj =>
        ⟨hpf.active_lower k1 e1 ha1 hm1 j hj, fun heq => by subst heq; exact hmemoSub e1 hm1 j hj⟩
      closed_outside := fun k1 hnr n' ps' i' hk1 s hs hal hgrd j hseq => by
        have hseqM : S.SeqRel (S.OfKey c M) s ps' 0 s.alt.rhs i' j :=
          S.seqRel_mono (fun _ _ _ _ h => h.1) hseq
        by_cases hkk : k1 = k
        · subst hkk
          obtain ⟨rfl, hpbits, rfl, _⟩ := key_inj hk1
          have hse := hesAll n' ps' i' hk1 s hs hal hgrd
          have hcurJ : cur.mem j = true := hchkSub j (hchkComplete s hse j (S.seqRel_ofKey_paramBits hpbits hseqM))
          refine ⟨?_, fun _ => hcurJ⟩
          cases hrk : rs k with
          | false => exact hpf.closed_outside k hrk n' ps' i' hk1 s hs hal hgrd j hseqM
          | true =>
            rcases hmk with hrsF | ⟨f0, hmk0⟩
            · rw [hrsF k] at hrk; cases hrk
            · exact hpf.active_lower k _ (hpf.rs_sub_active k hrk) hmk0 j hcurJ
        · have hnr0 : rs k1 = false := by
            simp only [rs', Bool.and_eq_false_iff, Bool.not_eq_false', beq_iff_eq] at hnr
            rcases hnr with hkeq | hrf
            · exact absurd hkeq.symm hkk
            · exact hrf
          exact ⟨hpf.closed_outside k1 hnr0 n' ps' i' hk1 s hs hal hgrd j hseqM, fun heq => absurd heq hkk⟩
      far_visited := fun hord k1 hv1 hnr n' ps' i' s k0 it0 rest0 h0 hk1 hsU hpr => by
        by_cases hkk : k1 = k
        · subst hkk; exact hvisitK hord n' ps' i' s k0 it0 rest0 h0 hk1 hsU hpr
        · rcases hv1 with hv0 | hkeq
          · have hnr0 : rs k1 = false := by
              simp only [rs', Bool.and_eq_false_iff, Bool.not_eq_false', beq_iff_eq] at hnr
              rcases hnr with hkeq | hrf
              · exact absurd hkeq.symm hkk
              · exact hrf
            obtain ⟨hjb, hch⟩ := hpf.far_visited hord k1 hv0 hnr0 n' ps' i' s k0 it0 rest0 h0 hk1 hsU
              (S.prefixRel_mono (fun _ _ _ _ h => h.1) hpr)
            refine ⟨fun j hj => hjb j (S.itemMatch_mono (fun _ _ _ _ h => h.1) hj), fun m args hne hkind => ?_⟩
            rcases hch m args hne hkind with hv' | hr'
            · exact Or.inl (Or.inl hv')
            · by_cases hck : k == key A false m (applyArgs ps' args) h0
              · rw [beq_iff_eq] at hck; exact Or.inl (Or.inr hck.symm)
              · exact Or.inr (by simp [rs', hck, hr'])
          · exact absurd hkeq hkk }
  exact ⟨hpf', fun j hj => hj.2 rfl, fun hord => Or.inr (key_eq_false_of_ordered_false hord c n ps i).symm⟩

theorem growAll_spec (hok : parseTablesOk = true) (hg : A.g = .syntactic ∨ A.g ∈ codeGrammars)
    {c : Bool} {ft : Option (NT × List Param)}
    {rec : NT → List Param → Nat → SM T Ends} (hrec : S.RecSpec c ft rec)
    (n : NT) (es : List Src) (ps : List Param) (i : Nat) (outer : Std.HashSet Key)
    (hes : ∀ e ∈ es, e ∈ altsOf A.cx A.g n ∧ S.CommitAllow c n ps i e ∧ e.alt.guard.all (Guard.holds ps) = true)
    (hesAll : ∀ n' ps' i', key A c n' ps' i' = key A c n ps i →
      ∀ s ∈ altsOf A.cx A.g n', S.CommitAllow c n' ps' i' s → s.alt.guard.all (Guard.holds ps') = true → s ∈ es)
    (hopen : ∀ g gp, ft = some (g, gp) → S.SpecOpen g gp n ps i) :
    ∀ (f : Nat) (cur : Ends) (st : St T) (res : Ends) (others : Bool) (st' : St T),
      S.MemoInv ft st →
      st.active.contains (key A c n ps i) = true →
      (c = true → ∀ k_a, st.active.contains k_a = true → k_a.2.2.2.2 = (true && orderedBy A.cx A.g)) →
      (∀ j, cur.mem j = true → ∃ t, S.ModeDerives c n ps i j t) →
      (growAll A rec es ps i (key A c n ps i) outer f cur).run st = .ok ((res, others), st') →
      S.MemoInv ft st' ∧
      st'.active.contains (key A c n ps i) = true ∧
      (∀ x, st'.active.contains x = st.active.contains x) ∧
      (∀ x, x ≠ key A c n ps i → st.active.contains x = true → st'.memo[x]? = st.memo[x]?) ∧
      (∀ (x : Key) (e : Entry), st.memo[x]? = some e → e.final = true → st'.memo[x]? = some e) ∧
      st'.fwd = st.fwd ∧
      st.far ≤ st'.far ∧
      (∀ j, res.mem j = true → ∃ t, S.ModeDerives c n ps i j t) ∧
      ∃ rs V M,
        rs (key A c n ps i) = false ∧
        (∀ x, st'.reads.contains x = (outer.contains x || rs x)) ∧
        (others = false → ∀ x, rs x = false) ∧
        S.PostFix c rs st' V M ∧
        (∀ j, M (key A c n ps i) j → res.mem j = true) ∧
        (orderedBy A.cx A.g = false → V (key A false n ps i))
  | 0, _, st, _, _, _, _, _, _, _, hrun => by
    unfold growAll at hrun; rw [sm_run_throw] at hrun; cases hrun
  | f + 1, cur, st, res, others, st', hinv, hactK, hactM, hcurS, hrun => by
    let k := key A c n ps i
    unfold growAll at hrun
    obtain ⟨_, stT, htk, hr1⟩ := sm_bind_ok hrun
    have ⟨hiT, hmT, haT, _, hfwT, hfiT, hfarT⟩ := hinv.of_tick htk
    obtain ⟨_, st0, hmod0, hr2⟩ := sm_bind_ok hr1
    obtain ⟨_, rfl⟩ := sm_pure_ok hmod0
    have hi0 : S.MemoInv ft { stT with memo := stT.memo.insert k ⟨cur, false, stT.far⟩, reads := {} } := by
      have hiM := hiT.insert_provisional hok (fun e0 he0 => hiT.active_provisional k e0 (haT ▸ hactK) he0)
        hcurS (fun g gp hft => (hiT.far_sound g gp hft).1)
      exact MemoInv.of_alpha_eq hiM (S.inv_mono_memo stT _ _ _ _ _ _ hiT.inv) rfl rfl rfl rfl
    obtain ⟨es', st1, hreRun, hr3⟩ := sm_bind_ok hr2
    have ⟨hi1, ha1, hm1, hf1, hfw1, hfar1, hes'S, rs0, V0, M0, hrd1, hpf0, hl0, hv0⟩ :=
      S.ruleEnds_spec hok hg hrec n es ps i _ es' st1 hi0 (haT ▸ hactM) hes hopen hreRun
    have hr4 := sm_get_bind_ok hr3
    obtain ⟨_, st2, hmod2, hr5⟩ := sm_bind_ok hr4
    obtain ⟨_, rfl⟩ := sm_pure_ok hmod2
    have hm1K : st1.memo[k]? = some ⟨cur, false, stT.far⟩ := by
      have h := hm1 k (haT ▸ hactK)
      dsimp only at h
      rw [hm_insert_eq] at h
      exact h
    have hrsEq : ∀ x, st1.reads.contains x = rs0 x := by
      intro x; have h := hrd1 x; dsimp only at h; rw [hs_empty, Bool.false_or] at h; exact h
    have hrdEq : ∀ x, (st1.reads.erase k).contains x = (!(k == x) && rs0 x) := by
      intro x; rw [hs_erase, hrsEq]
    have hreadSet : ∀ x, (outer.insertMany (st1.reads.erase k).toList).contains x =
        (outer.contains x || (!(k == x) && rs0 x)) := by
      intro x; rw [hs_insertMany]
      congr 1; apply Bool.eq_iff_iff.mpr
      rw [List.contains_iff_mem, hs_mem_toList, hrdEq]
    have hi2 : S.MemoInv ft { st1 with reads := outer.insertMany (st1.reads.erase k).toList } :=
      MemoInv.of_alpha_eq hi1 (S.inv_mono_memo st1 _ _ _ _ _ _ hi1.inv) rfl rfl rfl rfl
    have hnextS : ∀ j, (cur.union es').mem j = true → ∃ t, S.ModeDerives c n ps i j t := by
      intro j hj; rw [Ends.mem_union, Bool.or_eq_true] at hj
      exact hj.elim (hcurS j) (hes'S j)
    have haK1 : st1.active.contains k = true := by rw [ha1 k]; exact haT ▸ hactK
    have hmToSt : ∀ x, x ≠ k → st.active.contains x = true → st1.memo[x]? = st.memo[x]? := by
      intro x hne hx
      have h := hm1 x (haT ▸ hx); dsimp only at h
      rw [hm_insert_ne _ _ hne.symm] at h
      rw [h, hmT]
    have hfToSt : ∀ (x : Key) (e : Entry), st.memo[x]? = some e → e.final = true → st1.memo[x]? = some e := by
      intro x e hx he
      have hne : k ≠ x := by
        rintro rfl; rw [hinv.active_provisional k e hactK hx] at he; cases he
      refine hf1 x e ?_ he
      dsimp only; rw [hm_insert_ne _ _ hne, hmT]; exact hx
    cases hrsEmpty : st1.reads.isEmpty with
    | true =>
      simp only [hrsEmpty, ↓reduceIte] at hr5
      obtain ⟨hpEq, rfl⟩ := sm_pure_ok hr5
      obtain ⟨_, _⟩ := Prod.mk.inj hpEq.symm; subst res others
      have hrs0F : ∀ x, rs0 x = false := fun x => by
        rw [← hrsEq x]; exact (hs_isEmpty_iff st1.reads).mp hrsEmpty x
      have hpf2 := hpf0.mono_state (fun _ => rfl) (fun _ _ => rfl) (Nat.le_refl _)
        (st' := { st1 with reads := outer.insertMany (st1.reads.erase k).toList })
      obtain ⟨hpfCl, hM'k, hV'k⟩ := S.close_key_postFix hok (cur := cur.union es') hpf2 (Or.inl hrs0F)
        (fun e0 he0 j hj => by
          dsimp only at he0; rw [hm1K] at he0; injection he0 with he0'
          rw [← he0'] at hj
          rw [Ends.mem_union, hj, Bool.true_or])
        hesAll hl0 (fun j hj => by rw [Ends.mem_union, hj, Bool.or_true]) hv0
      have hrs'Eq : (fun x => !(k == x) && rs0 x) = (fun _ => false) :=
        funext fun x => by rw [hrs0F x, Bool.and_false]
      rw [hrs'Eq] at hpfCl
      exact ⟨hi2, haK1, fun x => (ha1 x).trans (by rw [haT]),
        hmToSt, hfToSt, hfw1.trans hfwT, by rw [← hfarT]; exact hfar1, hnextS,
        fun _ => false, _, _, rfl,
        fun x => by dsimp only; rw [hreadSet x, hrs0F x, Bool.and_false, Bool.or_false],
        fun _ _ => rfl, hpfCl, hM'k, hV'k⟩
    | false =>
      simp only [hrsEmpty, Bool.false_eq_true, ↓reduceIte] at hr5
      cases hdiff : (es'.diff cur).isEmpty with
      | true =>
        simp only [hdiff, ↓reduceIte] at hr5
        obtain ⟨hpEq, rfl⟩ := sm_pure_ok hr5
        obtain ⟨_, _⟩ := Prod.mk.inj hpEq.symm; subst res others
        have hchkSub : ∀ j, es'.mem j = true → cur.mem j = true := by
          intro j hj
          have hd := (Ends.isEmpty_iff _).mp hdiff j
          rw [Ends.mem_diff] at hd
          cases hc : cur.mem j
          · simp [hj, hc] at hd
          · rfl
        have hpf2 := hpf0.mono_state (fun _ => rfl) (fun _ _ => rfl) (Nat.le_refl _)
          (st' := { st1 with reads := outer.insertMany (st1.reads.erase k).toList })
        obtain ⟨hpfCl, hM'k, hV'k⟩ := S.close_key_postFix hok (cur := cur) hpf2 (Or.inr ⟨stT.far, hm1K⟩)
          (fun e0 he0 j hj => by
            dsimp only at he0; rw [hm1K] at he0; injection he0 with he0'; rw [← he0'] at hj; exact hj)
          hesAll hl0 hchkSub hv0
        refine ⟨hi2, haK1, fun x => (ha1 x).trans (by rw [haT]),
          hmToSt, hfToSt, hfw1.trans hfwT, by rw [← hfarT]; exact hfar1, hcurS,
          fun x => !(k == x) && rs0 x, _, _, by simp [k],
          fun x => hreadSet x,
          fun hno x => ?_,
          hpfCl, hM'k, hV'k⟩
        simp only [Bool.not_eq_false'] at hno
        dsimp only
        rw [← hrdEq x]
        exact (hs_isEmpty_iff _).mp hno x
      | false =>
        simp only [hdiff, Bool.false_eq_true, ↓reduceIte] at hr5
        obtain ⟨_, st3, hmod3, hr6⟩ := sm_bind_ok hr5
        obtain ⟨_, rfl⟩ := sm_pure_ok hmod3
        have hi3 : S.MemoInv ft { st1 with memo := st1.memo.insert k ⟨cur.union es', false, st1.far⟩, reads := outer.insertMany (st1.reads.erase k).toList } := by
          have hiM := hi2.insert_provisional hok (fun e0 he0 => hi2.active_provisional k e0 haK1 he0)
            hnextS (fun g gp hft => (hi2.far_sound g gp hft).1)
          exact MemoInv.of_alpha_eq hiM (S.inv_mono_memo st1 _ _ _ _ _ _ hi1.inv) rfl rfl rfl rfl
        have ⟨hiF, haKF, haF, hmF, hfF, hfwF, hfarF, hresS, rsF, VF, MF, hrsFk, hrdF, hothF, hpfF, hMFk, hVFk⟩ :=
          growAll_spec hok hg hrec n es ps i outer hes hesAll hopen f (cur.union es') _ res others st'
            hi3 haK1 (fun hc k_a hk => (haT ▸ hactM) hc k_a ((ha1 k_a) ▸ hk)) hnextS hr6
        refine ⟨hiF, haKF,
          fun x => (haF x).trans ((ha1 x).trans (by rw [haT])),
          fun x hne hx => ?_,
          fun x e hx he => ?_,
          hfwF.trans (hfw1.trans hfwT),
          Nat.le_trans (by rw [← hfarT]; exact hfar1) hfarF,
          hresS, rsF, VF, MF, hrsFk, hrdF, hothF, hpfF, hMFk, hVFk⟩
        · have hx1 : st1.active.contains x = true := by rw [ha1 x, haT]; exact hx
          have h := hmF x hne hx1; dsimp only at h
          rw [hm_insert_ne _ _ hne.symm] at h
          exact h.trans (hmToSt x hne hx)
        · have hne : k ≠ x := by
            rintro rfl; rw [hinv.active_provisional k e hactK hx] at he; cases he
          refine hfF x e ?_ he
          dsimp only; rw [hm_insert_ne _ _ hne]; exact hfToSt x e hx he

theorem viaLeft_spec (hok : parseTablesOk = true) (hg : A.g = .syntactic ∨ A.g ∈ codeGrammars)
    {c : Bool} {ft : Option (NT × List Param)}
    {rec : NT → List Param → Nat → SM T Ends} (hrec : S.RecSpec c ft rec)
    (n : NT) (ps : List Param) (i : Nat) (es dir rest : List Src) (outer : Std.HashSet Key) (f : Nat) (seed : Ends)
    (st : St T) (res : Ends) (others : Bool) (st' : St T)
    (hinv : S.MemoInv ft st)
    (hactK : st.active.contains (key A c n ps i) = true)
    (hactM : c = true → ∀ k_a, st.active.contains k_a = true → k_a.2.2.2.2 = (true && orderedBy A.cx A.g))
    (hes : ∀ e ∈ es, e ∈ altsOf A.cx A.g n ∧ S.CommitAllow c n ps i e ∧ e.alt.guard.all (Guard.holds ps) = true)
    (hesAll : ∀ n' ps' i', key A c n' ps' i' = key A c n ps i →
      ∀ s ∈ altsOf A.cx A.g n', S.CommitAllow c n' ps' i' s → s.alt.guard.all (Guard.holds ps') = true → s ∈ es)
    (hdir : ∀ e ∈ dir, e ∈ es ∧ leftRec n ps e = true)
    (hrest : ∀ e ∈ rest, e ∈ es)
    (hseedS : ∀ j, seed.mem j = true → ∃ t, S.ModeDerives c n ps i j t)
    (hopen : ∀ g gp, ft = some (g, gp) → S.SpecOpen g gp n ps i)
    (hrun : (viaLeft A rec n ps i es dir rest (key A c n ps i) outer f seed).run st = .ok ((res, others), st')) :
    S.MemoInv ft st' ∧
    st'.active.contains (key A c n ps i) = true ∧
    (∀ x, st'.active.contains x = st.active.contains x) ∧
    (∀ x, x ≠ key A c n ps i → st.active.contains x = true → st'.memo[x]? = st.memo[x]?) ∧
    (∀ (x : Key) (e : Entry), st.memo[x]? = some e → e.final = true → st'.memo[x]? = some e) ∧
    st'.fwd = st.fwd ∧
    st.far ≤ st'.far ∧
    (∀ j, res.mem j = true → ∃ t, S.ModeDerives c n ps i j t) ∧
    ∃ rs V M,
      rs (key A c n ps i) = false ∧
      (∀ x, st'.reads.contains x = (outer.contains x || rs x)) ∧
      (others = false → ∀ x, rs x = false) ∧
      S.PostFix c rs st' V M ∧
      (∀ j, M (key A c n ps i) j → res.mem j = true) ∧
      (orderedBy A.cx A.g = false → V (key A false n ps i)) := by
  let k := key A c n ps i
  unfold viaLeft at hrun
  obtain ⟨_, stT, htk, hr1⟩ := sm_bind_ok hrun
  have ⟨hiT, hmT, haT, _, hfwT, hfiT, hfarT⟩ := hinv.of_tick htk
  obtain ⟨_, st0, hmod0, hr2⟩ := sm_bind_ok hr1
  obtain ⟨_, rfl⟩ := sm_pure_ok hmod0
  have hi0 : S.MemoInv ft { stT with reads := {} } :=
    MemoInv.of_alpha_eq hiT (S.inv_mono_memo stT _ _ _ _ _ _ hiT.inv) rfl rfl rfl rfl
  obtain ⟨restEnds, st1, hrestRun, hr3⟩ := sm_bind_ok hr2
  have ⟨hi1, ha1, hm1, hf1, hfw1, hfar1, hrestS, _⟩ :=
    S.ruleEnds_spec hok hg hrec n rest ps i _ restEnds st1 hi0 (haT ▸ hactM)
      (fun e he => hes e (hrest e he)) hopen hrestRun
  have hr4 := sm_get_bind_ok hr3
  have haK1 : st1.active.contains k = true := by rw [ha1 k, haT]; exact hactK
  have hactM1 : c = true → ∀ k_a, st1.active.contains k_a = true → k_a.2.2.2.2 = (true && orderedBy A.cx A.g) :=
    fun hc k_a hk => (haT ▸ hactM) hc k_a ((ha1 k_a) ▸ hk)
  cases hr1Empty : st1.reads.isEmpty with
  | false =>
    simp only [hr1Empty, Bool.not_false, ↓reduceIte] at hr4
    have ⟨hiF, haKF, haF, hmF, hfF, hfwF, hfarF, hresS, rsF, VF, MF, hrsFk, hrdF, hothF, hpfF, hMFk, hVFk⟩ :=
      S.growAll_spec hok hg hrec n es ps i outer hes hesAll hopen f seed st1 res others st'
        hi1 haK1 hactM1 hseedS hr4
    exact ⟨hiF, haKF,
      fun x => (haF x).trans ((ha1 x).trans (by rw [haT])),
      fun x hne hx => by rw [hmF x hne (by rw [ha1 x, haT]; exact hx), hm1 x (haT ▸ hx), hmT],
      fun x e hx he => hfF x e (hf1 x e (hmT ▸ hx) he) he,
      hfwF.trans (hfw1.trans hfwT),
      Nat.le_trans (by rw [← hfarT]; exact hfar1) hfarF,
      hresS, rsF, VF, MF, hrsFk, hrdF, hothF, hpfF, hMFk, hVFk⟩
  | true =>
    simp only [hr1Empty, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hr4
    obtain ⟨_, st2, hmod2, hr5⟩ := sm_bind_ok hr4
    obtain ⟨_, rfl⟩ := sm_pure_ok hmod2
    let base := seed.union restEnds
    have hbaseS : ∀ j, base.mem j = true → ∃ t, S.ModeDerives c n ps i j t := by
      intro j hj; rw [Ends.mem_union, Bool.or_eq_true] at hj
      exact hj.elim (hseedS j) (hrestS j)
    have hi2 : S.MemoInv ft { st1 with memo := st1.memo.insert k ⟨base, false, st1.far⟩ } :=
      hi1.insert_provisional hok (fun e0 he0 => hi1.active_provisional k e0 haK1 he0)
        hbaseS (fun g gp hft => (hi1.far_sound g gp hft).1)
    obtain ⟨⟨cur, general⟩, st3, hglRun, hr6⟩ := sm_bind_ok hr5
    have hdirFull : ∀ e ∈ dir, e ∈ altsOf A.cx A.g n ∧ S.CommitAllow c n ps i e ∧
        e.alt.guard.all (Guard.holds ps) = true ∧ leftRec n ps e = true := by
      intro e he; obtain ⟨hesE, hlrE⟩ := hdir e he
      obtain ⟨h1, h2, h3⟩ := hes e hesE; exact ⟨h1, h2, h3, hlrE⟩
    have ⟨hi3, haK3, ha3, hm3, hf3, hfw3, hfar3, hcurS⟩ :=
      S.growLeft_sound hok hg hrec n ps i dir hdirFull hopen f base base _ cur general st3
        hi2 haK1 hactM1 hbaseS hbaseS hglRun
    have hactM3 : c = true → ∀ k_a, st3.active.contains k_a = true → k_a.2.2.2.2 = (true && orderedBy A.cx A.g) :=
      fun hc k_a hk => hactM1 hc k_a ((ha3 k_a) ▸ hk)
    have hmToSt : ∀ x, x ≠ k → st.active.contains x = true → st3.memo[x]? = st.memo[x]? := by
      intro x hne hx
      have hx1 : st1.active.contains x = true := by rw [ha1 x, haT]; exact hx
      have h := hm3 x hne hx1; dsimp only at h
      rw [hm_insert_ne _ _ hne.symm] at h
      rw [h, hm1 x (haT ▸ hx), hmT]
    have hfToSt : ∀ (x : Key) (e : Entry), st.memo[x]? = some e → e.final = true → st3.memo[x]? = some e := by
      intro x e hx he
      have hne : k ≠ x := by
        rintro rfl; rw [hinv.active_provisional k e hactK hx] at he; cases he
      have hx1 := hf1 x e (hmT ▸ hx) he
      refine hf3 x e ?_ he
      dsimp only; rw [hm_insert_ne _ _ hne]; exact hx1
    cases general with
    | true =>
      simp only [↓reduceIte] at hr6
      have ⟨hiF, haKF, haF, hmF, hfF, hfwF, hfarF, hresS, rsF, VF, MF, hrsFk, hrdF, hothF, hpfF, hMFk, hVFk⟩ :=
        S.growAll_spec hok hg hrec n es ps i outer hes hesAll hopen f cur st3 res others st'
          hi3 haK3 hactM3 hcurS hr6
      exact ⟨hiF, haKF,
        fun x => (haF x).trans ((ha3 x).trans ((ha1 x).trans (by rw [haT]))),
        fun x hne hx => (hmF x hne (by rw [ha3 x, ha1 x, haT]; exact hx)).trans (hmToSt x hne hx),
        fun x e hx he => hfF x e (hfToSt x e hx he) he,
        hfwF.trans (hfw3.trans (hfw1.trans hfwT)),
        Nat.le_trans (by rw [← hfarT]; exact hfar1) (Nat.le_trans hfar3 hfarF),
        hresS, rsF, VF, MF, hrsFk, hrdF, hothF, hpfF, hMFk, hVFk⟩
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte] at hr6
      obtain ⟨_, st4, hmod4, hr7⟩ := sm_bind_ok hr6
      obtain ⟨_, rfl⟩ := sm_pure_ok hmod4
      have hi4 : S.MemoInv ft { st3 with memo := st3.memo.insert k ⟨cur, false, st3.far⟩, reads := {} } := by
        have hiM := hi3.insert_provisional hok (fun e0 he0 => hi3.active_provisional k e0 haK3 he0)
          hcurS (fun g gp hft => (hi3.far_sound g gp hft).1)
        exact MemoInv.of_alpha_eq hiM (S.inv_mono_memo st3 _ _ _ _ _ _ hi3.inv) rfl rfl rfl rfl
      obtain ⟨chk, st5, hchkRun, hr8⟩ := sm_bind_ok hr7
      have ⟨hi5, ha5, hm5, hf5, hfw5, hfar5, hchkS, rs5, V5, M5, hrd5, hpf5, hl5, hv5⟩ :=
        S.ruleEnds_spec hok hg hrec n es ps i _ chk st5 hi4 hactM3 hes hopen hchkRun
      have hr9 := sm_get_bind_ok hr8
      have haK5 : st5.active.contains k = true := by rw [ha5 k]; exact haK3
      have hactM5 : c = true → ∀ k_a, st5.active.contains k_a = true → k_a.2.2.2.2 = (true && orderedBy A.cx A.g) :=
        fun hc k_a hk => hactM3 hc k_a ((ha5 k_a) ▸ hk)
      have hmToSt5 : ∀ x, x ≠ k → st.active.contains x = true → st5.memo[x]? = st.memo[x]? := by
        intro x hne hx
        have hx3 : st3.active.contains x = true := by rw [ha3 x, ha1 x, haT]; exact hx
        have h := hm5 x hx3; dsimp only at h
        rw [hm_insert_ne _ _ hne.symm] at h
        exact h.trans (hmToSt x hne hx)
      have hfToSt5 : ∀ (x : Key) (e : Entry), st.memo[x]? = some e → e.final = true → st5.memo[x]? = some e := by
        intro x e hx he
        have hne : k ≠ x := by
          rintro rfl; rw [hinv.active_provisional k e hactK hx] at he; cases he
        refine hf5 x e ?_ he
        dsimp only; rw [hm_insert_ne _ _ hne]; exact hfToSt x e hx he
      cases hfb : (!((st5.reads.erase (key A c n ps i)).isEmpty) || !((chk.diff cur).isEmpty)) with
      | true =>
        simp only [hfb, ↓reduceIte] at hr9
        have hccS : ∀ j, (cur.union chk).mem j = true → ∃ t, S.ModeDerives c n ps i j t := by
          intro j hj; rw [Ends.mem_union, Bool.or_eq_true] at hj
          exact hj.elim (hcurS j) (hchkS j)
        have ⟨hiF, haKF, haF, hmF, hfF, hfwF, hfarF, hresS, rsF, VF, MF, hrsFk, hrdF, hothF, hpfF, hMFk, hVFk⟩ :=
          S.growAll_spec hok hg hrec n es ps i outer hes hesAll hopen f (cur.union chk) st5 res others st'
            hi5 haK5 hactM5 hccS hr9
        exact ⟨hiF, haKF,
          fun x => (haF x).trans ((ha5 x).trans ((ha3 x).trans ((ha1 x).trans (by rw [haT])))),
          fun x hne hx => (hmF x hne (by rw [ha5 x, ha3 x, ha1 x, haT]; exact hx)).trans (hmToSt5 x hne hx),
          fun x e hx he => hfF x e (hfToSt5 x e hx he) he,
          hfwF.trans (hfw5.trans (hfw3.trans (hfw1.trans hfwT))),
          Nat.le_trans (by rw [← hfarT]; exact hfar1) (Nat.le_trans hfar3 (Nat.le_trans hfar5 hfarF)),
          hresS, rsF, VF, MF, hrsFk, hrdF, hothF, hpfF, hMFk, hVFk⟩
      | false =>
        simp only [hfb, Bool.false_eq_true, ↓reduceIte] at hr9
        obtain ⟨_, st6, hmod6, hr10⟩ := sm_bind_ok hr9
        obtain ⟨_, rfl⟩ := sm_pure_ok hmod6
        obtain ⟨hpEq, rfl⟩ := sm_pure_ok hr10
        obtain ⟨_, _⟩ := Prod.mk.inj hpEq.symm; subst res others
        simp only [Bool.or_eq_false_iff, Bool.not_eq_false'] at hfb
        obtain ⟨hrdEmpty, hchkEmpty⟩ := hfb
        have hm5K : st5.memo[k]? = some ⟨cur, false, st3.far⟩ := by
          have h := hm5 k haK3; dsimp only at h
          rw [hm_insert_eq] at h; exact h
        have hchkSub : ∀ j, chk.mem j = true → cur.mem j = true := by
          intro j hj
          have hd := (Ends.isEmpty_iff _).mp hchkEmpty j
          rw [Ends.mem_diff] at hd
          cases hc : cur.mem j
          · simp [hj, hc] at hd
          · rfl
        have hi6 : S.MemoInv ft { st5 with reads := outer } :=
          MemoInv.of_alpha_eq hi5 (S.inv_mono_memo st5 _ _ _ _ _ _ hi5.inv) rfl rfl rfl rfl
        have hpf6 := hpf5.mono_state (fun _ => rfl) (fun _ _ => rfl) (Nat.le_refl _) (st' := { st5 with reads := outer })
        obtain ⟨hpfCl, hM'k, hV'k⟩ := S.close_key_postFix hok (cur := cur) hpf6 (Or.inr ⟨st3.far, hm5K⟩)
          (fun e0 he0 j hj => by
            dsimp only at he0; rw [hm5K] at he0; injection he0 with he0'; rw [← he0'] at hj; exact hj)
          hesAll hl5 hchkSub hv5
        have hrs'F : ∀ x, (!(k == x) && rs5 x) = false := by
          intro x
          have he := (hs_isEmpty_iff _).mp hrdEmpty x
          rw [hs_erase] at he
          have hr5x := hrd5 x; dsimp only at hr5x; rw [hs_empty, Bool.false_or] at hr5x
          rw [← hr5x]; exact he
        have hrs'Eq : (fun x => !(k == x) && rs5 x) = (fun _ => false) := funext hrs'F
        rw [hrs'Eq] at hpfCl
        exact ⟨hi6, haK5,
          fun x => (ha5 x).trans ((ha3 x).trans ((ha1 x).trans (by rw [haT]))),
          hmToSt5, hfToSt5,
          hfw5.trans (hfw3.trans (hfw1.trans hfwT)),
          Nat.le_trans (by rw [← hfarT]; exact hfar1) (Nat.le_trans hfar3 hfar5),
          hcurS,
          fun _ => false, _, _, rfl,
          fun x => by simp,
          fun _ _ => rfl,
          hpfCl, hM'k, hV'k⟩

/-! ## `firstAlt_spec` & `ends_spec` -/

def FirstAltRes (n : NT) (ps : List Param) (i : Nat) : Option Src → Prop
  | some s => S.IsFirstAlt n ps i s
  | none => ∀ s' ∈ altsUnder A n ps, ¬ ∃ h m kids, S.SeqWith (fun _ _ _ _ => True) s' ps 0 s'.alt.rhs i h m kids

theorem firstAlt_spec (hok : parseTablesOk = true) (hg : A.g = .syntactic ∨ A.g ∈ codeGrammars)
    {ft : Option (NT × List Param)}
    {pl : NT → List Param → Nat → SM T Ends} (hpl : S.RecSpec false none pl)
    (n : NT) (ps : List Param) (i : Nat)
    (st : St T) (r : Option Src) (st' : St T)
    (hftNone : ft = none)
    (hinv : S.MemoInv ft st)
    (hactT : ∀ k_a, st.active.contains k_a = true → k_a.2.2.2.2 = true)
    (hrun : (firstAlt A pl n ps i).run st = .ok (r, st')) :
    S.MemoInv ft st' ∧
    (∀ x, st'.active.contains x = st.active.contains x) ∧
    (∀ x, st.active.contains x = true → st'.memo[x]? = st.memo[x]?) ∧
    (∀ (x : Key) (e : Entry), st.memo[x]? = some e → e.final = true → st'.memo[x]? = some e) ∧
    (∀ x, st'.reads.contains x = st.reads.contains x) ∧
    st'.fwd = st.fwd ∧
    st.far ≤ st'.far ∧
    S.FirstAltRes n ps i r := by
  subst hftNone
  let kf := key A false n ps i
  unfold firstAlt at hrun; dsimp only at hrun
  have hr1 := sm_get_bind_ok hrun
  cases hhit : st.first[key A false n ps i]? with
  | some r0 =>
    simp only [hhit] at hr1
    obtain ⟨hrEq, rfl⟩ := sm_pure_ok hr1; subst r0
    exact ⟨hinv, fun _ => rfl, fun _ _ => rfl, fun _ _ hm _ => hm, fun _ => rfl, rfl, Nat.le_refl _,
      by have hs := hinv.first_spec kf r hhit n ps i rfl; cases r <;> exact hs⟩
  | none =>
    simp only [hhit] at hr1
    obtain ⟨res, st1, hloop, hr2⟩ := sm_bind_ok hr1
    obtain ⟨_, _, hmod, hr3⟩ := sm_bind_ok hr2
    obtain ⟨_, rfl⟩ := sm_pure_ok hmod
    obtain ⟨hrEq, rfl⟩ := sm_pure_ok hr3; subst res
    have hloopSpec : ∀ (pre rem : List Src) (stA : St T) (ro : Option Src) (stB : St T),
        altsUnder A n ps = pre ++ rem →
        (∀ s' ∈ pre, ¬ ∃ h m kids, S.SeqWith (fun _ _ _ _ => True) s' ps 0 s'.alt.rhs i h m kids) →
        S.MemoInv none stA →
        (∀ k_a, stA.active.contains k_a = true → k_a.2.2.2.2 = true) →
        (firstAltLoop A pl ps i rem).run stA = .ok (ro, stB) →
        S.MemoInv none stB ∧
        (∀ x, stB.active.contains x = stA.active.contains x) ∧
        (∀ x, stA.active.contains x = true → stB.memo[x]? = stA.memo[x]?) ∧
        (∀ (x : Key) (ef : Entry), stA.memo[x]? = some ef → ef.final = true → stB.memo[x]? = some ef) ∧
        (∀ x, stB.reads.contains x = stA.reads.contains x) ∧
        stB.fwd = stA.fwd ∧
        stA.far ≤ stB.far ∧
        S.FirstAltRes n ps i ro := by
      intro pre rem
      induction rem generalizing pre with
      | nil =>
        intro stA ro stB halts hpre hiA _ hlr
        unfold firstAltLoop at hlr
        obtain ⟨rfl, rfl⟩ := sm_pure_ok hlr
        rw [List.append_nil] at halts
        exact ⟨hiA, fun _ => rfl, fun _ _ => rfl, fun _ _ hm _ => hm, fun _ => rfl, rfl, Nat.le_refl _,
          by dsimp [FirstAltRes]; exact halts ▸ hpre⟩
      | cons e rest ihr =>
        intro stA ro stB halts hpre hiA hactA hlr
        unfold firstAltLoop at hlr
        obtain ⟨⟨_, last⟩, stM, hfwr, hlr1⟩ := sm_bind_ok hlr
        have heU : e ∈ altsUnder A n ps := halts ▸ List.mem_append.mpr (Or.inr (List.mem_cons_self ..))
        obtain ⟨heAlts, heGrd⟩ := (mem_altsUnder_iff A n ps e).mp heU
        have ⟨hiM, haM, hmM, hfM, hfwM, hfarM, _, huM, rsM, VM, MM, hrdM, hpfM, hlM, _⟩ :=
          S.forwardGo_spec hpl e ps 0 (.single i) e.alt.rhs stA _ last stM hiA
            (fun hc => nomatch hc) (fun it hit => itemWF_of_mem A hok hg heAlts hit)
            (fun _ _ h => nomatch h) hfwr
        have hrsMF : ∀ x, rsM x = false := by
          intro x; cases hrx : rsM x with
          | false => rfl
          | true =>
            have hm1 := hpfM.rs_mode x hrx
            simp only [Bool.false_and] at hm1
            have ha1 := hpfM.rs_sub_active x hrx
            rw [haM x] at ha1
            have hm2 := hactA x ha1
            exact nomatch (hm1.symm.trans hm2)
        have hrdEqM : ∀ x, stM.reads.contains x = stA.reads.contains x := by
          intro x; rw [hrdM x, hrsMF x, Bool.or_false]
        have hPlainToM : ∀ n' ps' a' b', S.SpanOfAllow (fun _ _ _ _ => True) n' ps' a' b' → S.OfKey false MM n' ps' a' b' := by
          intro n' ps' a' b' ⟨t0, hd0⟩
          have hcl : ∀ k1, S.OneStepClosed false MM k1 := fun k1 => hpfM.closed_outside k1 (hrsMF k1)
          have hcf : S.CommitAllow false = (fun _ _ _ _ => True) := by funext _ _ _ _; simp [CommitAllow]
          exact S.global_postFix_complete hcl (hcf ▸ hd0)
        have hsi : (Ends.single i).mem i = true := by simp [Ends.mem_single]
        cases hlemp : last.isEmpty with
        | false =>
          simp only [hlemp, Bool.not_false, ↓reduceIte] at hlr1
          obtain ⟨hro, rfl⟩ := sm_pure_ok hlr1; subst hro
          have hexJ : ∃ j, last.mem j = true := Classical.byContradiction fun hno => by
            have hall : ∀ x, last.mem x = false := fun x => by
              cases hmx : last.mem x with
              | false => rfl
              | true => exact absurd ⟨x, hmx⟩ hno
            rw [(Ends.isEmpty_iff last).mpr hall] at hlemp; cases hlemp
          obtain ⟨j, hj⟩ := hexJ
          obtain ⟨h0, hh0, hsr⟩ := huM j hj
          rw [Ends.mem_single, beq_iff_eq] at hh0; subst hh0
          have hcf : S.CommitAllow false = (fun _ _ _ _ => True) := by funext _ _ _ _; simp [CommitAllow]
          rw [hcf] at hsr
          obtain ⟨m0, ts0, hsw0⟩ := S.seqRel_iff_seqWith.mp hsr
          have haltsF : (altsOf A.cx A.g n).filter (·.alt.guard.all (Guard.holds ps)) = pre ++ e :: rest := halts
          obtain ⟨pre0, post0, halts0, _, hpreMap⟩ :=
            filter_split_first (·.alt.guard.all (Guard.holds ps)) (altsOf A.cx A.g n) pre rest e haltsF
          exact ⟨hiM, haM, hmM, hfM, hrdEqM, hfwM, hfarM,
            ⟨pre0, post0, halts0, heGrd, ⟨j, m0, ts0, hsw0⟩,
              fun s' hs' hgs' hex' => hpre s' (hpreMap s' hs' hgs') hex'⟩⟩
        | true =>
          simp only [hlemp, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hlr1
          have hnoE : ¬ ∃ h m kids, S.SeqWith (fun _ _ _ _ => True) e ps 0 e.alt.rhs i h m kids := by
            rintro ⟨j, m0, kids0, hsw0⟩
            have hsr0 : S.SeqRel (S.SpanOfAllow (fun _ _ _ _ => True)) e ps 0 e.alt.rhs i j :=
              S.seqRel_iff_seqWith.mpr ⟨m0, kids0, hsw0⟩
            have hjMem : last.mem j = true := hlM i j hsi (S.seqRel_mono hPlainToM hsr0)
            rw [(Ends.isEmpty_iff last).mp hlemp j] at hjMem; cases hjMem
          have halts' : altsUnder A n ps = (pre ++ [e]) ++ rest := by simp [halts]
          have hpre' : ∀ s' ∈ pre ++ [e], ¬ ∃ h m kids, S.SeqWith (fun _ _ _ _ => True) s' ps 0 s'.alt.rhs i h m kids := by
            intro s' hs'
            rcases List.mem_append.mp hs' with hsp | hse
            · exact hpre s' hsp
            · simp only [List.mem_singleton] at hse; subst hse; exact hnoE
          have ⟨hiB, haB, hmB, hfB, hrdB, hfwB, hfarB, hres⟩ :=
            ihr (pre ++ [e]) stM ro stB halts' hpre' hiM (fun k_a hk => hactA k_a ((haM k_a) ▸ hk)) hlr1
          exact ⟨hiB,
            fun x => (haB x).trans (haM x),
            fun x hx => (hmB x ((haM x).symm ▸ hx)).trans (hmM x hx),
            fun x ef hx hef => hfB x ef (hfM x ef hx hef) hef,
            fun x => (hrdB x).trans (hrdEqM x),
            hfwB.trans hfwM,
            Nat.le_trans hfarM hfarB,
            hres⟩
    have ⟨hi1, ha1, hm1, hf1, hrd1, hfw1, hfar1, hres⟩ :=
      hloopSpec [] (altsUnder A n ps) st r st1 rfl (fun _ h => nomatch h) hinv hactT hloop
    have hiF : S.MemoInv none { st1 with first := st1.first.insert kf r } :=
      { inv := S.inv_mono_memo st1 _ _ _ _ _ _ hi1.inv
        memo_sound := hi1.memo_sound
        memo_complete := hi1.memo_complete
        active_in_memo := hi1.active_in_memo
        active_provisional := hi1.active_provisional
        first_spec := fun k' optS hk' n' ps' i' heq => by
          by_cases hkk : kf = k'
          · subst hkk; rw [hm_insert_eq] at hk'; cases hk'
            obtain ⟨rfl, hpbits, rfl, _⟩ := key_inj heq.symm
            cases r with
            | some s0 => exact (S.isFirstAlt_paramBits hpbits).mp hres
            | none =>
              intro s' hs' ⟨h', m', kids', hsw'⟩
              rw [← S.altsUnder_paramBits hpbits] at hs'
              exact hres s' hs' ⟨h', m', kids', (S.seqWith_paramBits hpbits.symm).mp hsw'⟩
          · rw [hm_insert_ne _ _ hkk] at hk'
            exact hi1.first_spec k' optS hk' n' ps' i' heq
        far_sound := fun _ _ h => nomatch h
        far_complete := hi1.far_complete }
    exact ⟨hiF, ha1, hm1, hf1, hrd1, hfw1, hfar1, hres⟩

theorem ends_spec (hok : parseTablesOk = true) (hg : A.g = .syntactic ∨ A.g ∈ codeGrammars) :
    ∀ (d : Nat) (c : Bool) (ft : Option (NT × List Param))
      (_hftOrd : ft.isSome = true → orderedBy A.cx A.g = false)
      (n : NT) (ps : List Param) (i : Nat) (st : St T) (es : Ends) (st' : St T),
      S.MemoInv ft st →
      (c = true → ∀ k_a, st.active.contains k_a = true → k_a.2.2.2.2 = (true && orderedBy A.cx A.g)) →
      (∀ g gp, ft = some (g, gp) → S.SpecOpen g gp n ps i) →
      (ends A size c d n ps i).run st = .ok (es, st') →
      S.MemoInv ft st' ∧
      (∀ x, st'.active.contains x = st.active.contains x) ∧
      (∀ x, st.active.contains x = true → st'.memo[x]? = st.memo[x]?) ∧
      (∀ (x : Key) (e : Entry), st.memo[x]? = some e → e.final = true → st'.memo[x]? = some e) ∧
      st'.fwd = st.fwd ∧
      st.far ≤ st'.far ∧
      (∀ j, es.mem j = true → S.SpanOfAllow (S.CommitAllow c) n ps i j) ∧
      ∃ rs V M,
        (∀ x, st'.reads.contains x = (st.reads.contains x || rs x)) ∧
        S.PostFix c rs st' V M ∧
        (∀ j, M (key A c n ps i) j → es.mem j = true) ∧
        (orderedBy A.cx A.g = false → V (key A false n ps i) ∨ rs (key A false n ps i) = true)
  | 0, _, _, _, _, _, _, _, _, _, _, _, _, hrun => by
    unfold ends at hrun; rw [sm_run_throw] at hrun; cases hrun
  | d + 1, c, ft, hftOrd, n, ps, i, st, es, st', hinv, hactM, hopen, hrun => by
    let k := key A c n ps i
    have hrecC : S.RecSpec c ft (fun n' ps' h' => ends A size c d n' ps' h') :=
      ⟨fun n' ps' h' st0 es0 st1 hi0 ha0 ho0 hr0 =>
        ends_spec hok hg d c ft hftOrd n' ps' h' st0 es0 st1 hi0 ha0 ho0 hr0⟩
    have hrecFalse : S.RecSpec false none (fun n' ps' h' => ends A size false d n' ps' h') :=
      ⟨fun n' ps' h' st0 es0 st1 hi0 ha0 ho0 hr0 =>
        ends_spec hok hg d false none (fun h => nomatch h) n' ps' h' st0 es0 st1 hi0 ha0 ho0 hr0⟩
    have heval : ∀ (seed : Entry)
        (hnotAct : st.active.contains k = false)
        (hnotFin : ∀ e0, st.memo[k]? = some e0 → e0.final = false)
        (hseedS : ∀ j, seed.ends.mem j = true → ∃ t, S.ModeDerives c n ps i j t)
        (hseedFar : ∀ g gp, ft = some (g, gp) → S.SpecHit g gp seed.far)
        (herun : (evalEntry A (fun n' ps' h' => ends A size c d n' ps' h')
          (fun n' ps' h' => ends A size false d n' ps' h') size c n ps i k st.reads st.far seed).run st = .ok (es, st')),
        S.MemoInv ft st' ∧
        (∀ x, st'.active.contains x = st.active.contains x) ∧
        (∀ x, st.active.contains x = true → st'.memo[x]? = st.memo[x]?) ∧
        (∀ (x : Key) (e : Entry), st.memo[x]? = some e → e.final = true → st'.memo[x]? = some e) ∧
        st'.fwd = st.fwd ∧
        st.far ≤ st'.far ∧
        (∀ j, es.mem j = true → S.SpanOfAllow (S.CommitAllow c) n ps i j) ∧
        ∃ rs V M,
          (∀ x, st'.reads.contains x = (st.reads.contains x || rs x)) ∧
          S.PostFix c rs st' V M ∧
          (∀ j, M k j → es.mem j = true) ∧
          (orderedBy A.cx A.g = false → V (key A false n ps i) ∨ rs (key A false n ps i) = true) := by
      intro seed hnotAct hnotFin hseedS hseedFar herun
      unfold evalEntry at herun
      obtain ⟨_, st0, hmod0, hr1⟩ := sm_bind_ok herun
      obtain ⟨_, rfl⟩ := sm_pure_ok hmod0
      have hi0 : S.MemoInv ft { st with active := st.active.insert k, memo := st.memo.insert k { seed with final := false }, far := seed.far } := by
        have hiP := hinv.insert_provisional hok hnotFin hseedS hseedFar
        exact
          { inv := S.inv_mono_memo st _ _ _ _ _ _ hinv.inv
            memo_sound := hiP.memo_sound
            memo_complete := hiP.memo_complete
            active_in_memo := fun k' ha' => by
              rw [hs_insert, Bool.or_eq_true] at ha'
              rcases ha' with hkk | ha0
              · rw [beq_iff_eq] at hkk; subst hkk
                dsimp only; rw [hm_insert_eq]; rfl
              · exact hiP.active_in_memo k' ha0
            active_provisional := fun k' e' ha' hk' => by
              rw [hs_insert, Bool.or_eq_true] at ha'
              rcases ha' with hkk | ha0
              · rw [beq_iff_eq] at hkk; subst hkk
                dsimp only at hk'; rw [hm_insert_eq] at hk'
                cases hk'; rfl
              · exact hiP.active_provisional k' e' ha0 hk'
            first_spec := hiP.first_spec
            far_sound := fun g gp hft => ⟨hseedFar g gp hft, (hiP.far_sound g gp hft).2⟩
            far_complete := hiP.far_complete }
      have hactM0 : c = true → ∀ k_a, (st.active.insert k).contains k_a = true → k_a.2.2.2.2 = (true && orderedBy A.cx A.g) := by
        intro hc k_a hk
        rw [hs_insert, Bool.or_eq_true] at hk
        rcases hk with hkk | hk0
        · rw [beq_iff_eq] at hkk; subst hkk; subst hc; rfl
        · exact hactM hc k_a hk0
      obtain ⟨altsList, st1, haltsRun, hr2⟩ := sm_bind_ok hr1
      have haltsSpec : S.MemoInv ft st1 ∧
          (∀ x, st1.active.contains x = (st.active.insert k).contains x) ∧
          (∀ x, (st.active.insert k).contains x = true → st1.memo[x]? = (st.memo.insert k { seed with final := false })[x]?) ∧
          (∀ (x : Key) (ef : Entry), (st.memo.insert k { seed with final := false })[x]? = some ef → ef.final = true → st1.memo[x]? = some ef) ∧
          (∀ x, st1.reads.contains x = st.reads.contains x) ∧
          st1.fwd = st.fwd ∧
          (∀ e ∈ altsList, e ∈ altsOf A.cx A.g n ∧ S.CommitAllow c n ps i e ∧ e.alt.guard.all (Guard.holds ps) = true) ∧
          (∀ n' ps' i', key A c n' ps' i' = k →
            ∀ s ∈ altsOf A.cx A.g n', S.CommitAllow c n' ps' i' s → s.alt.guard.all (Guard.holds ps') = true → s ∈ altsList) := by
        unfold altsAt at haltsRun
        cases hordNt : (c && (orderedNtsBy A.cx A.g).contains n) with
        | false =>
          simp only [hordNt, Bool.false_eq_true, ↓reduceIte] at haltsRun
          obtain ⟨hEq, rfl⟩ := sm_pure_ok haltsRun; subst hEq
          refine ⟨hi0, fun _ => rfl, fun _ _ => rfl, fun _ _ hm _ => hm, fun _ => rfl, rfl, ?_, ?_⟩
          · intro e he
            obtain ⟨h1, h2⟩ := (mem_altsUnder_iff A n ps e).mp he
            refine ⟨h1, ?_, h2⟩
            unfold CommitAllow; rw [hordNt]; trivial
          · intro n' ps' i' hk' s hs _ hgrd
            obtain ⟨rfl, hpbits, rfl, _⟩ := key_inj hk'
            rw [S.altsUnder_paramBits hpbits.symm]
            exact (mem_altsUnder_iff A n' ps' s).mpr ⟨hs, hgrd⟩
        | true =>
          simp only [hordNt, ↓reduceIte] at haltsRun
          simp only [Bool.and_eq_true] at hordNt
          obtain ⟨rfl, hcnt⟩ := hordNt
          have hordTrue : orderedBy A.cx A.g = true := orderedBy_true_of_contains_orderedNts hok hcnt
          have hftNone : ft = none := by
            cases ft with
            | none => rfl
            | some _ => exfalso; have := hftOrd rfl; rw [hordTrue] at this; cases this
          obtain ⟨ro, _, hfaRun, hpure⟩ := sm_bind_ok haltsRun
          obtain ⟨hEq, rfl⟩ := sm_pure_ok hpure; subst hEq
          have hactT : ∀ k_a, (st.active.insert k).contains k_a = true → k_a.2.2.2.2 = true := by
            intro k_a hk; have := hactM0 rfl k_a hk; simpa [hordTrue] using this
          have ⟨hiF, haF, hmF, hfF, hrdF, hfwF, _, hroSpec⟩ :=
            S.firstAlt_spec hok hg hrecFalse n ps i _ ro st1 hftNone hi0 hactT hfaRun
          refine ⟨hiF, haF, hmF, hfF, hrdF, hfwF, ?_, ?_⟩
          · intro e he
            cases ro with
            | none => cases he
            | some s0 =>
              simp only [Option.toList_some, List.mem_singleton] at he; subst he
              have ⟨pre0, post0, halts0, hgrd0, _⟩ := hroSpec
              have hmem0 : e ∈ altsOf A.cx A.g n := halts0 ▸ List.mem_append.mpr (Or.inr (List.mem_cons_self ..))
              refine ⟨hmem0, ?_, hgrd0⟩
              unfold CommitAllow; simp only [Bool.true_and, hcnt, ↓reduceIte]; exact hroSpec
          · intro n' ps' i' hk' s hs hal hgrd
            obtain ⟨rfl, hpbits, rfl, _⟩ := key_inj hk'
            unfold CommitAllow at hal
            simp only [Bool.true_and, hcnt, ↓reduceIte] at hal
            have halPs : S.IsFirstAlt n' ps i' s := (S.isFirstAlt_paramBits hpbits).mp hal
            cases ro with
            | some s0 =>
              simp only [Option.toList_some, List.mem_singleton]
              exact S.isFirstAlt_unique halPs hroSpec
            | none =>
              obtain ⟨_, _, _, _, ⟨h0, m0, kids0, hsw0⟩, _⟩ := halPs
              exfalso
              exact hroSpec s ((mem_altsUnder_iff A n' ps s).mpr ⟨hs, S.guardAll_paramBits hpbits s.alt.guard ▸ hgrd⟩)
                ⟨h0, m0, kids0, hsw0⟩
      obtain ⟨hi1, ha1, hm1, hf1, hrd1, hfw1, hesOk, hesAll⟩ := haltsSpec
      have haK1 : st1.active.contains k = true := by rw [ha1 k, hs_insert, beq_self_eq_true, Bool.true_or]
      have hactM1 : c = true → ∀ k_a, st1.active.contains k_a = true → k_a.2.2.2.2 = (true && orderedBy A.cx A.g) :=
        fun hc k_a hk => hactM0 hc k_a ((ha1 k_a) ▸ hk)
      have hgrowJoin : ∃ (cur : Ends) (others : Bool) (st2 : St T),
          ((do
            modify fun (s : St T) => { s with active := s.active.erase k, memo := s.memo.insert k ⟨cur, !others, s.far⟩, far := max st.far s.far }
            pure cur : SM T Ends)).run st2 = Except.ok (es, st') ∧
          S.MemoInv ft st2 ∧
          st2.active.contains k = true ∧
          (∀ x, st2.active.contains x = st1.active.contains x) ∧
          (∀ x, x ≠ k → st1.active.contains x = true → st2.memo[x]? = st1.memo[x]?) ∧
          (∀ (x : Key) (ef : Entry), st1.memo[x]? = some ef → ef.final = true → st2.memo[x]? = some ef) ∧
          st2.fwd = st1.fwd ∧
          (∀ j, cur.mem j = true → ∃ t, S.ModeDerives c n ps i j t) ∧
          ∃ rs V M,
            rs k = false ∧
            (∀ x, st2.reads.contains x = (st.reads.contains x || rs x)) ∧
            (others = false → ∀ x, rs x = false) ∧
            S.PostFix c rs st2 V M ∧
            (∀ j, M k j → cur.mem j = true) ∧
            (orderedBy A.cx A.g = false → V (key A false n ps i)) := by
        generalize hpEq : altsList.partition (leftRec n ps) = dp at hr2
        rcases dp with ⟨dir, rest⟩
        dsimp only at hr2
        cases hdEmp : dir.isEmpty with
        | true =>
          simp only [hdEmp, ↓reduceIte] at hr2
          obtain ⟨⟨cur, others⟩, st2, hgrowRun, hr3⟩ := sm_bind_ok hr2
          have ⟨hi2, haK2, ha2, hm2, hf2, hfw2, _, hcurS, rs, V, M, hrsk, hrd2, hoth, hpf2, hMk, hVk⟩ :=
            S.growAll_spec hok hg hrecC n altsList ps i st.reads hesOk hesAll hopen
              (size - i + 2) seed.ends st1 cur others st2 hi1 haK1 hactM1 hseedS hgrowRun
          exact ⟨cur, others, st2, hr3, hi2, haK2, ha2, hm2, hf2, hfw2, hcurS, rs, V, M, hrsk, hrd2, hoth, hpf2, hMk, hVk⟩
        | false =>
          simp only [hdEmp, Bool.false_eq_true, ↓reduceIte] at hr2
          obtain ⟨⟨cur, others⟩, st2, hgrowRun, hr3⟩ := sm_bind_ok hr2
          have hdir : ∀ e ∈ dir, e ∈ altsList ∧ leftRec n ps e = true := by
            intro e he
            have hd : dir = altsList.filter (leftRec n ps) := by
              rw [List.partition_eq_filter_filter] at hpEq; injection hpEq with h1 _; exact h1.symm
            rw [hd, List.mem_filter] at he; exact he
          have hrest : ∀ e ∈ rest, e ∈ altsList := by
            intro e he
            have hr : rest = altsList.filter (fun x => !leftRec n ps x) := by
              rw [List.partition_eq_filter_filter] at hpEq; injection hpEq with _ h2; exact h2.symm
            rw [hr, List.mem_filter] at he; exact he.1
          have ⟨hi2, haK2, ha2, hm2, hf2, hfw2, _, hcurS, rs, V, M, hrsk, hrd2, hoth, hpf2, hMk, hVk⟩ :=
            S.viaLeft_spec hok hg hrecC n ps i altsList dir rest st.reads (size - i + 2) seed.ends
              st1 cur others st2 hi1 haK1 hactM1 hesOk hesAll hdir hrest hseedS hopen hgrowRun
          exact ⟨cur, others, st2, hr3, hi2, haK2, ha2, hm2, hf2, hfw2, hcurS, rs, V, M, hrsk, hrd2, hoth, hpf2, hMk, hVk⟩
      obtain ⟨cur, others, st2, hr3, hi2, haK2, ha2, hm2, hf2, hfw2, hcurS, rs, V, M, hrsk, hrd2, hoth, hpf2, hMk, hVk⟩ := hgrowJoin
      obtain ⟨_, _, hmodF, hr4⟩ := sm_bind_ok hr3
      obtain ⟨_, rfl⟩ := sm_pure_ok hmodF
      obtain ⟨hesEq, rfl⟩ := sm_pure_ok hr4; subst hesEq
      have hactRestore : ∀ x, (st2.active.erase k).contains x = st.active.contains x := by
        intro x
        rw [hs_erase, ha2 x, ha1 x, hs_insert]
        by_cases hkx : k == x
        · rw [beq_iff_eq] at hkx; subst hkx; simp [hnotAct]
        · simp [hkx]
      have hmRestore : ∀ x, st.active.contains x = true →
          (st2.memo.insert k ⟨cur, !others, st2.far⟩)[x]? = st.memo[x]? := by
        intro x hx
        have hne : k ≠ x := by rintro rfl; rw [hnotAct] at hx; cases hx
        rw [hm_insert_ne _ _ hne]
        have hx0 : (st.active.insert k).contains x = true := by rw [hs_insert, hx, Bool.or_true]
        have hx1 : st1.active.contains x = true := by rw [ha1 x]; exact hx0
        rw [hm2 x hne.symm hx1, hm1 x hx0, hm_insert_ne _ _ hne]
      have hfRestore : ∀ (x : Key) (ef : Entry), st.memo[x]? = some ef → ef.final = true →
          (st2.memo.insert k ⟨cur, !others, st2.far⟩)[x]? = some ef := by
        intro x ef hx hef
        have hne : k ≠ x := by rintro rfl; rw [hnotFin ef hx] at hef; cases hef
        rw [hm_insert_ne _ _ hne]
        refine hf2 x ef (hf1 x ef ?_ hef) hef
        rw [hm_insert_ne _ _ hne]; exact hx
      have hiFinal : S.MemoInv ft { st2 with active := st2.active.erase k, memo := st2.memo.insert k ⟨cur, !others, st2.far⟩, far := max st.far st2.far } :=
        { inv := S.inv_mono_memo st2 _ _ _ _ _ _ hi2.inv
          memo_sound := fun k' e' hk' c' n' ps' i' heq j hj => by
            by_cases hkk : k = k'
            · subst hkk; rw [hm_insert_eq] at hk'; cases hk'
              exact (S.modeDerives_key_congr hok heq.symm j).mp (hcurS j hj)
            · rw [hm_insert_ne _ _ hkk] at hk'
              exact hi2.memo_sound k' e' hk' c' n' ps' i' heq j hj
          memo_complete := fun k' e' hk' hfin c' n' ps' i' heq j t hder => by
            by_cases hkk : k = k'
            · subst hkk; rw [hm_insert_eq] at hk'; cases hk'
              dsimp only at hfin
              have hothF : others = false := by cases others <;> simp_all
              have hrsF : ∀ x, rs x = false := hoth hothF
              have hcl : ∀ k1, S.OneStepClosed c M k1 := fun k1 => hpf2.closed_outside k1 (hrsF k1)
              obtain ⟨t2, hder2⟩ := (S.modeDerives_key_congr hok heq j).mp ⟨t, hder⟩
              exact hMk j (S.global_postFix_complete hcl hder2)
            · rw [hm_insert_ne _ _ hkk] at hk'
              exact hi2.memo_complete k' e' hk' hfin c' n' ps' i' heq j t hder
          active_in_memo := fun k' ha' => by
            rw [hs_erase, Bool.and_eq_true, Bool.not_eq_true'] at ha'
            have hne : k ≠ k' := by rintro rfl; have := ha'.1; simp at this
            rw [hm_insert_ne _ _ hne]
            exact hi2.active_in_memo k' ha'.2
          active_provisional := fun k' e' ha' hk' => by
            rw [hs_erase, Bool.and_eq_true, Bool.not_eq_true'] at ha'
            have hne : k ≠ k' := by rintro rfl; have := ha'.1; simp at this
            rw [hm_insert_ne _ _ hne] at hk'
            exact hi2.active_provisional k' e' ha'.2 hk'
          first_spec := hi2.first_spec
          far_sound := fun g gp hft => by
            obtain ⟨hsf0, _⟩ := hinv.far_sound g gp hft
            obtain ⟨hsf2, hmf2⟩ := hi2.far_sound g gp hft
            refine ⟨?_, fun k' e' hk' => ?_⟩
            · by_cases hle : st.far ≤ st2.far
              · rw [Nat.max_eq_right hle]; exact hsf2
              · rw [Nat.max_eq_left (by omega)]; exact hsf0
            · by_cases hkk : k = k'
              · subst hkk; rw [hm_insert_eq] at hk'; cases hk'; exact hsf2
              · rw [hm_insert_ne _ _ hkk] at hk'; exact hmf2 k' e' hk'
          far_complete := fun hord k' e' hk' hfin j hhit => by
            by_cases hkk : k = k'
            · subst hkk; rw [hm_insert_eq] at hk'; cases hk'
              dsimp only at hfin ⊢
              have hothF : others = false := by cases others <;> simp_all
              have hrsF : ∀ x, rs x = false := hoth hothF
              have hcl : ∀ k1, S.OneStepClosed c M k1 := fun k1 => hpf2.closed_outside k1 (hrsF k1)
              have hPlainToM : ∀ n1 ps1 a1 b1, S.SpanOfAllow (fun _ _ _ _ => True) n1 ps1 a1 b1 →
                  S.OfKey false M n1 ps1 a1 b1 := by
                intro n1 ps1 a1 b1 ⟨t0, hd0⟩
                rw [← S.ofKey_eq_false_of_ordered_false hord c M]
                have hcf : S.CommitAllow c = (fun _ _ _ _ => True) := by
                  funext _ _ _ _; unfold CommitAllow; rw [orderedNts_nil_of_ordered_false hok hord]; simp
                exact S.global_postFix_complete hcl (hcf ▸ hd0)
              have hkEq : k = key A false n ps i := key_eq_false_of_ordered_false hord c n ps i
              have hvOpen : ∀ k1, S.OpenFromKey (S.SpanOfAllow (fun _ _ _ _ => True)) k k1 → V k1 := by
                intro k1 ho1
                induction ho1 with
                | root => exact hkEq ▸ hVk hord
                | child _ hk1 hs1 hpr1 hne1 hkind1 iho =>
                  obtain ⟨_, hch⟩ := hpf2.far_visited hord _ iho (hrsF _) _ _ _ _ _ _ _ _ hk1 hs1
                    (S.prefixRel_mono hPlainToM hpr1)
                  rcases hch _ _ hne1 hkind1 with hv' | hr'
                  · exact hv'
                  · rw [hrsF] at hr'; cases hr'
              obtain ⟨k1, n1, ps1, i1, s1, k0, it0, rest0, h0, ho1, hk1, hs1, hpr1, hm1'⟩ := hhit
              obtain ⟨hjb, _⟩ := hpf2.far_visited hord k1 (hvOpen k1 ho1) (hrsF k1) n1 ps1 i1 s1 k0 it0 rest0 h0 hk1 hs1
                (S.prefixRel_mono hPlainToM hpr1)
              exact hjb j (S.itemMatch_mono hPlainToM hm1')
            · rw [hm_insert_ne _ _ hkk] at hk'
              exact hi2.far_complete hord k' e' hk' hfin j hhit }
      have hpfFinal : S.PostFix c rs { st2 with active := st2.active.erase k, memo := st2.memo.insert k ⟨cur, !others, st2.far⟩, far := max st.far st2.far } V M :=
        { rs_mode := hpf2.rs_mode
          rs_sub_active := fun k1 hrk1 => by
            dsimp only; rw [hs_erase]
            have hne : (k == k1) = false := by
              rw [Bool.eq_false_iff, ne_eq, beq_iff_eq]; rintro rfl; rw [hrsk] at hrk1; cases hrk1
            simp [hne, hpf2.rs_sub_active k1 hrk1]
          rs_upper := fun k1 hrk1 => by
            dsimp only
            have hne : k ≠ k1 := by rintro rfl; rw [hrsk] at hrk1; cases hrk1
            rw [hm_insert_ne _ _ hne]
            exact hpf2.rs_upper k1 hrk1
          active_lower := fun k1 e1 ha1' hm1' => by
            dsimp only at ha1' hm1'
            rw [hs_erase, Bool.and_eq_true, Bool.not_eq_true'] at ha1'
            have hne : k ≠ k1 := by rintro rfl; have := ha1'.1; simp at this
            rw [hm_insert_ne _ _ hne] at hm1'
            exact hpf2.active_lower k1 e1 ha1'.2 hm1'
          closed_outside := hpf2.closed_outside
          far_visited := fun hord k1 hv1 hnr1 n1 ps1 i1 s1 k0 it0 rest0 h0 hk1 hs1 hpr1 => by
            obtain ⟨hjb, hch⟩ := hpf2.far_visited hord k1 hv1 hnr1 n1 ps1 i1 s1 k0 it0 rest0 h0 hk1 hs1 hpr1
            exact ⟨fun j hj => Nat.le_trans (hjb j hj) (Nat.le_max_right st.far st2.far), hch⟩ }
      exact ⟨hiFinal, hactRestore, hmRestore, hfRestore,
        hfw2.trans hfw1, Nat.le_max_left st.far st2.far, hcurS,
        rs, V, M, hrd2, hpfFinal, hMk, fun hord => Or.inl (hVk hord)⟩
    -- Unfold `ends` on `d + 1`
    unfold ends at hrun; dsimp only at hrun
    have hr1 := sm_get_bind_ok hrun
    cases hm0 : st.memo[key A c n ps i]? with
    | none =>
      simp only [hm0] at hr1
      exact heval ⟨{}, false, 0⟩
        (by cases ha : st.active.contains k with
            | false => rfl
            | true =>
              have hsome := hinv.active_in_memo k ha
              rw [hm0] at hsome; cases hsome)
        (fun _ h => by rw [hm0] at h; cases h)
        (fun _ h => nomatch h)
        (fun _ _ _ => .zero)
        hr1
    | some e0 =>
      simp only [hm0] at hr1
      cases hfin0 : e0.final with
      | true =>
        simp only [hfin0, ↓reduceIte] at hr1
        obtain ⟨_, _, hset, hpure⟩ := sm_bind_ok hr1
        obtain ⟨_, rfl⟩ := sm_pure_ok hset
        obtain ⟨hesEq, rfl⟩ := sm_pure_ok hpure; subst hesEq
        have hi' : S.MemoInv ft { st with far := max st.far e0.far } :=
          MemoInv.of_hit hinv (S.inv_mono_memo st _ _ _ _ _ _ hinv.inv) rfl rfl rfl rfl
            (fun g gp hft => (hinv.far_sound g gp hft).2 k e0 hm0)
        let M_lfp : Key → Nat → Prop := fun k1 j =>
          ∀ c1 n1 ps1 i1, key A c1 n1 ps1 i1 = k1 → ∃ t, S.ModeDerives c1 n1 ps1 i1 j t
        let Plain := S.SpanOfAllow (fun _ _ _ _ => True)
        let V_open : Key → Prop := S.OpenFromKey Plain (key A false n ps i)
        have hpfLfp : S.PostFix c (fun _ => false) { st with far := max st.far e0.far } V_open M_lfp :=
          { rs_mode := fun _ h => nomatch h
            rs_sub_active := fun _ h => nomatch h
            rs_upper := fun _ h => nomatch h
            active_lower := fun k1 e1 _ hm1 j hj c1 n1 ps1 i1 hk1 =>
              hinv.memo_sound k1 e1 hm1 c1 n1 ps1 i1 hk1 j hj
            closed_outside := fun k1 _ n1 ps1 i1 hk1 s1 hs1 hal1 hgrd1 j hseq1 c2 n2 ps2 i2 hk2 => by
              have hseqL : S.SeqRel (S.SpanOfAllow (S.CommitAllow c)) s1 ps1 0 s1.alt.rhs i1 j :=
                S.seqRel_mono (fun n' p' a' b' hm' => hm' c n' p' a' rfl) hseq1
              have hder1 := S.derivesWith_of_seqRel hok hs1 hal1 hgrd1 hseqL
              exact (S.modeDerives_key_congr hok (hk1.trans hk2.symm) j).mp hder1
            far_visited := fun hord k1 hv1 _ n1 ps1 i1 s1 k0 it0 rest0 h0 hk1 hs1 hpr1 => by
              have hMtoPlain : ∀ n' p' a' b', S.OfKey false M_lfp n' p' a' b' → Plain n' p' a' b' := by
                intro n' p' a' b' hm'
                obtain ⟨t0, hd0⟩ := hm' false n' p' a' rfl
                exact ⟨t0, S.derivesWith_mono_allow (fun _ _ _ _ _ => trivial) hd0⟩
              have hprP := S.prefixRel_mono hMtoPlain hpr1
              refine ⟨fun j hj => ?_, fun m args hne hkind => ?_⟩
              · have hkEq : k = key A false n ps i := key_eq_false_of_ordered_false hord c n ps i
                have hhit0 : S.HitFromKey Plain k j :=
                  ⟨k1, n1, ps1, i1, s1, k0, it0, rest0, h0, hkEq ▸ hv1, hk1, hs1, hprP, S.itemMatch_mono hMtoPlain hj⟩
                have hle0 := hinv.far_complete hord k e0 hm0 hfin0 j hhit0
                exact Nat.le_trans hle0 (Nat.le_max_right st.far e0.far)
              · exact Or.inl (.child hv1 hk1 hs1 hprP hne hkind) }
        exact ⟨hi', fun _ => rfl, fun _ _ => rfl, fun _ _ hm _ => hm, rfl, Nat.le_max_left _ _,
          fun j hj => hinv.memo_sound k e0 hm0 c n ps i rfl j hj,
          fun _ => false, V_open, M_lfp,
          fun x => by simp,
          hpfLfp,
          fun j hj => by
            obtain ⟨t0, hd0⟩ := hj c n ps i rfl
            exact hinv.memo_complete k e0 hm0 hfin0 c n ps i rfl j t0 hd0,
          fun _ => Or.inl .root⟩
      | false =>
        simp only [hfin0, Bool.false_eq_true, ↓reduceIte] at hr1
        cases hact0 : st.active.contains (key A c n ps i) with
        | true =>
          simp only [hact0, ↓reduceIte] at hr1
          obtain ⟨_, _, hset, hpure⟩ := sm_bind_ok hr1
          obtain ⟨_, rfl⟩ := sm_pure_ok hset
          obtain ⟨hesEq, rfl⟩ := sm_pure_ok hpure; subst hesEq
          have hi' : S.MemoInv ft { st with reads := st.reads.insert k } :=
            MemoInv.of_alpha_eq hinv (S.inv_mono_memo st _ _ _ _ _ _ hinv.inv) rfl rfl rfl rfl
          let rs_k : Key → Bool := fun x => k == x
          let M_act : Key → Nat → Prop := fun x j => x = k → e0.ends.mem j = true
          have hpfAct : S.PostFix c rs_k { st with reads := st.reads.insert k } (fun _ => False) M_act :=
            { rs_mode := fun k1 hr => by simp only [rs_k, beq_iff_eq] at hr; subst hr; rfl
              rs_sub_active := fun k1 hr => by simp only [rs_k, beq_iff_eq] at hr; subst hr; exact hact0
              rs_upper := fun k1 hr => by
                simp only [rs_k, beq_iff_eq] at hr; subst hr
                exact ⟨e0, hm0, fun j hj => hj rfl⟩
              active_lower := fun k1 e1 _ hm1 j hj heq => by
                subst heq; dsimp only at hm1; rw [hm0] at hm1; injection hm1 with he; rw [he]; exact hj
              closed_outside := fun k1 hnr _ _ _ _ _ _ _ _ _ _ heq => by
                subst heq; simp [rs_k] at hnr
              far_visited := fun _ _ hv => nomatch hv }
          exact ⟨hi', fun _ => rfl, fun _ _ => rfl, fun _ _ hm _ => hm, rfl, Nat.le_refl _,
            fun j hj => hinv.memo_sound k e0 hm0 c n ps i rfl j hj,
            rs_k, fun _ => False, M_act,
            fun x => by dsimp only; rw [hs_insert]; exact Bool.or_comm _ _,
            hpfAct,
            fun j hj => hj rfl,
            fun hord => Or.inr (by simp [rs_k, k, key_eq_false_of_ordered_false hord c n ps i])⟩
        | false =>
          simp only [hact0, Bool.false_eq_true, ↓reduceIte] at hr1
          exact heval e0 hact0
            (fun e1 he1 => by rw [hm0] at he1; injection he1 with h; rw [← h]; exact hfin0)
            (fun j hj => hinv.memo_sound k e0 hm0 c n ps i rfl j hj)
            (fun g gp hft => (hinv.far_sound g gp hft).2 k e0 hm0)
            hr1

/-! ## Top-level corollaries: `finalEndsAt_spec`, `finalEnds_spec`, and `finalEnds_far_spec` -/

theorem finalEndsAt_spec (hok : parseTablesOk = true) (hg : A.g = .syntactic ∨ A.g ∈ codeGrammars)
    (c : Bool) (d : Nat) (n : NT) (ps : List Param) (i : Nat)
    (st : St T) (es : Ends) (st' : St T)
    (hinv : S.MemoInv none st)
    (hnoAct : ∀ x, st.active.contains x = false)
    (hrun : (finalEndsAt A size c d n ps i).run st = .ok (es, st')) :
    S.MemoInv none st' ∧
    (∀ x, st'.active.contains x = false) ∧
    st'.fwd = st.fwd ∧
    (∀ j, es.mem j = true ↔ S.SpanOfAllow (S.CommitAllow c) n ps i j) := by
  unfold finalEndsAt at hrun
  obtain ⟨es0, st1, hends, hrest⟩ := sm_bind_ok hrun
  have ⟨hi1, ha1, _, _, hfw1, _, hu, rs, _, M, _, hpf, hl, _⟩ :=
    S.ends_spec hok hg d c none (fun h => nomatch h) n ps i st es0 st1 hinv
      (fun _ k_a hk => by rw [hnoAct k_a] at hk; cases hk)
      (fun _ _ h => nomatch h) hends
  have hmchk := sm_get_bind_ok hrest
  have hmOk : es0 = es ∧ st' = st1 := by
    cases hm1 : st1.memo[key A c n ps i]? with
    | none => rw [hm1] at hmchk; dsimp only at hmchk; rw [sm_run_throw] at hmchk; cases hmchk
    | some e =>
      rw [hm1] at hmchk; dsimp only at hmchk
      cases hf : e.final with
      | false =>
        simp only [hf, Bool.false_eq_true, ↓reduceIte] at hmchk
        rw [sm_run_throw] at hmchk; cases hmchk
      | true =>
        simp only [hf, ↓reduceIte] at hmchk
        exact sm_pure_ok hmchk
  obtain ⟨rfl, rfl⟩ := hmOk
  have ha1' : ∀ x, st'.active.contains x = false := fun x => (ha1 x).trans (hnoAct x)
  have hrsF : ∀ x, rs x = false := fun x => by
    cases hrx : rs x with
    | false => rfl
    | true => have := hpf.rs_sub_active x hrx; rw [ha1' x] at this; cases this
  have hcl : ∀ k1, S.OneStepClosed c M k1 := fun k1 => hpf.closed_outside k1 (hrsF k1)
  exact ⟨hi1, ha1', hfw1, fun j =>
    ⟨hu j, fun ⟨t, hd⟩ => hl j (S.global_postFix_complete hcl hd)⟩⟩

theorem finalEnds_spec (hok : parseTablesOk = true) (hg : A.g = .syntactic ∨ A.g ∈ codeGrammars)
    (d : Nat) (n : NT) (ps : List Param) (i : Nat)
    (st : St T) (es : Ends) (st' : St T)
    (hinv : S.MemoInv none st)
    (hnoAct : ∀ x, st.active.contains x = false)
    (hrun : (finalEnds A size d n ps i).run st = .ok (es, st')) :
    S.MemoInv none st' ∧
    (∀ x, st'.active.contains x = false) ∧
    st'.fwd = st.fwd ∧
    (∀ j, es.mem j = true ↔ ∃ t, S.ModeDerives true n ps i j t) :=
  S.finalEndsAt_spec hok hg true d n ps i st es st' hinv hnoAct hrun

theorem finalEnds_far_spec (hok : parseTablesOk = true) (hg : A.g = .syntactic ∨ A.g ∈ codeGrammars)
    (hord : orderedBy A.cx A.g = false)
    (d : Nat) (goal : NT) (goalPs : List Param)
    (st : St T) (es : Ends) (st' : St T)
    (hinv : S.Inv st)
    (hm : st.memo = {}) (ha : st.active = {}) (hf : st.first = {}) (hfar : st.far = 0)
    (hrun : (finalEnds A size d goal goalPs 0).run st = .ok (es, st')) :
    S.MemoInv (some (goal, goalPs)) st' ∧
    (∀ x, st'.active.contains x = false) ∧
    st'.fwd = st.fwd ∧
    (∀ j, es.mem j = true ↔ ∃ t, S.PlainDerives goal goalPs 0 j t) ∧
    S.SpecHit goal goalPs st'.far ∧
    (∀ h, S.SpecHit goal goalPs h → h ≤ st'.far) := by
  have hi0 : S.MemoInv (some (goal, goalPs)) st := MemoInv.fresh S hinv hm ha hf hfar _
  have hnoAct : ∀ x, st.active.contains x = false := fun x => by rw [ha, hs_empty]
  unfold finalEnds finalEndsAt at hrun
  obtain ⟨es0, st1, hends, hrest⟩ := sm_bind_ok hrun
  have ⟨hi1, ha1, _, _, hfw1, _, hu, rs, V, M, _, hpf, hl, hv⟩ :=
    S.ends_spec hok hg d true (some (goal, goalPs)) (fun _ => hord) goal goalPs 0 st es0 st1 hi0
      (fun _ k_a hk => by rw [hnoAct k_a] at hk; cases hk)
      (fun g gp hft => by cases hft; exact .root) hends
  have hmchk := sm_get_bind_ok hrest
  have hmOk : es0 = es ∧ st' = st1 := by
    cases hm1 : st1.memo[key A true goal goalPs 0]? with
    | none => rw [hm1] at hmchk; dsimp only at hmchk; rw [sm_run_throw] at hmchk; cases hmchk
    | some e =>
      rw [hm1] at hmchk; dsimp only at hmchk
      cases hfe : e.final with
      | false =>
        simp only [hfe, Bool.false_eq_true, ↓reduceIte] at hmchk
        rw [sm_run_throw] at hmchk; cases hmchk
      | true =>
        simp only [hfe, ↓reduceIte] at hmchk
        exact sm_pure_ok hmchk
  obtain ⟨rfl, rfl⟩ := hmOk
  have ha1' : ∀ x, st'.active.contains x = false := fun x => (ha1 x).trans (hnoAct x)
  have hrsF : ∀ x, rs x = false := fun x => by
    cases hrx : rs x with
    | false => rfl
    | true => have := hpf.rs_sub_active x hrx; rw [ha1' x] at this; cases this
  have hcl : ∀ k1, S.OneStepClosed true M k1 := fun k1 => hpf.closed_outside k1 (hrsF k1)
  have hcf : S.CommitAllow true = (fun _ _ _ _ => True) := by
    funext _ _ _ _; unfold CommitAllow; rw [orderedNts_nil_of_ordered_false hok hord]; simp
  have hPlainToM : ∀ n1 ps1 a1 b1, S.SpanOfAllow (fun _ _ _ _ => True) n1 ps1 a1 b1 →
      S.OfKey false M n1 ps1 a1 b1 := by
    intro n1 ps1 a1 b1 ⟨t0, hd0⟩
    rw [← S.ofKey_eq_false_of_ordered_false hord true M]
    exact S.global_postFix_complete hcl (hcf ▸ hd0)
  have hvRoot : V (key A false goal goalPs 0) := by
    rcases hv hord with hv0 | hr0
    · exact hv0
    · rw [hrsF] at hr0; cases hr0
  let Plain := S.SpanOfAllow (fun _ _ _ _ => True)
  have hvOpen : ∀ k1, S.OpenFromKey Plain (key A false goal goalPs 0) k1 → V k1 := by
    intro k1 ho1
    induction ho1 with
    | root => exact hvRoot
    | child _ hk1 hs1 hpr1 hne1 hkind1 iho =>
      obtain ⟨_, hch⟩ := hpf.far_visited hord _ iho (hrsF _) _ _ _ _ _ _ _ _ hk1 hs1
        (S.prefixRel_mono hPlainToM hpr1)
      rcases hch _ _ hne1 hkind1 with hv' | hr'
      · exact hv'
      · rw [hrsF] at hr'; cases hr'
  refine ⟨hi1, ha1', hfw1, ?_, (hi1.far_sound goal goalPs rfl).1, ?_⟩
  · intro j
    constructor
    · intro hj; obtain ⟨t, hd⟩ := hu j hj
      exact ⟨t, S.derivesWith_mono_allow (fun _ _ _ _ _ => trivial) hd⟩
    · rintro ⟨t, hd⟩
      exact hl j (S.global_postFix_complete hcl (S.derivesWith_mono_allow (fun _ _ _ _ _ => hcf ▸ trivial) hd))
  · intro h hh
    rcases S.specHit_to_hitFromKey hh with rfl | ⟨k1, n1, ps1, i1, s1, k0, it0, rest0, h0, ho1, hk1, hs1, hpr1, hm1'⟩
    · exact Nat.zero_le _
    · obtain ⟨hjb, _⟩ := hpf.far_visited hord k1 (hvOpen k1 ho1) (hrsF k1) n1 ps1 i1 s1 k0 it0 rest0 h0 hk1 hs1
        (S.prefixRel_mono hPlainToM hpr1)
      exact hjb h (S.itemMatch_mono hPlainToM hm1')

end AlphaSpec

end Engine.Parse
