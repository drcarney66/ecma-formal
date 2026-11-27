module

public import Engine.Proofs.Parse.Tables
public import Engine.Proofs.Parse.Ends

@[expose] public section

/-!
# Parametric specification of `Alpha` and `Kernel.mk`

Defines the pure specification interface `AlphaSpec` for an `Engine.Parse.Alpha N T` over a state
invariant `Inv : St T → Prop`, together with the induced derivation tree (`DTree`), span
derivation (`DerivesWith`), committed derivation (`ModeDerives`), and proves soundness of
`Kernel.lookOk`, `Kernel.excluded`, `Kernel.walk`, and `Kernel.mk`.
-/

namespace Engine.Parse

open Ecma.Grammar

/-! ## `SM` monad helpers -/

@[simp] theorem sm_run_pure {T α : Type} (a : α) (st : St T) :
    (pure a : SM T α).run st = .ok (a, st) := rfl

@[simp] theorem sm_run_throw {T α : Type} (e : Stop) (st : St T) :
    (throw e : SM T α).run st = .error e := rfl

@[simp] theorem sm_run_get {T : Type} (st : St T) :
    (get : SM T (St T)).run st = .ok (st, st) := rfl

@[simp] theorem sm_run_set {T : Type} (s st : St T) :
    (set s : SM T Unit).run st = .ok ((), s) := rfl

@[simp] theorem sm_run_modify {T : Type} (f : St T → St T) (st : St T) :
    (modify f : SM T Unit).run st = .ok ((), f st) := rfl

theorem sm_pure_ok {T α : Type} {a b : α} {st st' : St T}
    (h : (pure a : SM T α).run st = .ok (b, st')) : a = b ∧ st' = st := by
  rw [sm_run_pure] at h
  cases h
  exact ⟨rfl, rfl⟩

theorem sm_bind_ok {T α β : Type} {m : SM T α} {f : α → SM T β} {st : St T} {b : β} {st' : St T}
    (h : (m >>= f).run st = .ok (b, st')) :
    ∃ a st1, m.run st = .ok (a, st1) ∧ (f a).run st1 = .ok (b, st') := by
  rw [StateT.run_bind] at h
  cases hm : m.run st with
  | error e => rw [hm] at h; cases h
  | ok p => rw [hm] at h; exact ⟨p.1, p.2, rfl, h⟩

theorem sm_guard_true {T α : Type} {c : Bool} {err : Stop} {m : SM T α} {st : St T} {v : α} {st' : St T}
    (h : (if c = true then m else ((throw err : SM T Unit) >>= fun _ => m)).run st = .ok (v, st')) :
    c = true ∧ m.run st = .ok (v, st') := by
  cases c with
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h
    obtain ⟨_, _, ht, _⟩ := sm_bind_ok h
    cases ht
  | true =>
    exact ⟨rfl, by simpa using h⟩

/-- Lawfulness of a `Builder N` (`Engine.builder` satisfies all fields by `rfl`). -/
structure BuilderSpec {N : Type} (B : Builder N) : Prop where
  prod_node : ∀ st lo hi p nt ps kids txt, B.prod (B.node st lo hi p nt ps kids txt) = p
  nt_node : ∀ st lo hi p nt ps kids txt, B.nt (B.node st lo hi p nt ps kids txt) = nt
  args_node : ∀ st lo hi p nt ps kids txt, B.args (B.node st lo hi p nt ps kids txt) = ps
  span_node : ∀ st lo hi p nt ps kids txt, B.span (B.node st lo hi p nt ps kids txt) = (lo, hi)
  kids_node : ∀ st lo hi p nt ps kids txt, B.kids (B.node st lo hi p nt ps kids txt) = kids
  stamp_node : ∀ st lo hi p nt ps kids txt, B.stamp (B.node st lo hi p nt ps kids txt) = st
  text_node : ∀ st lo hi p nt ps kids txt, B.text (B.node st lo hi p nt ps kids txt) = txt.toArray

/-- Well-formedness of a `Lookahead` item under `parseTablesOk`. -/
def LookWF {N T : Type} (A : Alpha N T) (l : Lookahead) : Prop :=
  match l with
  | .eq q | .ne q => A.g = .syntactic → lookSeqsOk synLookTermOk [q] = true
  | .mem qs | .notMem qs => A.g = .syntactic → lookSeqsOk synLookTermOk qs = true
  | .notMemNT n => A.g ≠ .syntactic ∧
      (glData.alts A.cx A.g n).isEmpty = false ∧
      (glData.alts A.cx A.g n).all (fun e => e.alt.guard.isEmpty &&
        match e.alt.rhs with | [.sym (.t x) false] => codeLookTermOk x | _ => false) = true

/-- Well-formedness of an `Exclusion` item under `parseTablesOk`. -/
def ExclWF {N T : Type} (A : Alpha N T) (ex : Exclusion) : Prop :=
  let symWF : Sym → Prop
    | .t _ => True
    | .nt m _ => (altsOf A.cx A.g m).isEmpty = false → A.g = .syntactic ∨ posBounded A.cx A.g 16 m = true
  match ex with
  | .sym y => symWF y
  | .oneOf ys _ => ∀ y ∈ ys, symWF y

/-- Well-formedness of an `Item` under `parseTablesOk`. -/
def ItemWF {N T : Type} (A : Alpha N T) : Item → Prop
  | .lookahead l => LookWF A l
  | .butNot _ ex => ExclWF A ex
  | _ => True

theorem itemWF_of_mem {N T : Type} (A : Alpha N T) (hok : parseTablesOk = true)
    (hg : A.g = .syntactic ∨ A.g ∈ codeGrammars)
    {n : NT} {s : Src} (hs : s ∈ altsOf A.cx A.g n) {it : Item} (hit : it ∈ s.alt.rhs) :
    ItemWF A it := by
  rw [altsOf_eq hok] at hs
  rcases hg with hsyn | hcode
  · have hokIt : synItemOk A.cx it = true := synItemOk_of_mem hok (hsyn ▸ hs) hit
    cases it with
    | lookahead l =>
      cases l with
      | eq q | ne q | mem q | notMem q => intro _; exact hokIt
      | notMemNT m => cases hokIt
    | butNot base ex =>
      cases ex with
      | sym y =>
        cases y with
        | t _ => trivial
        | nt m _ => intro _; exact Or.inl hsyn
      | oneOf ys _ =>
        intro y _
        cases y with
        | t _ => trivial
        | nt m _ => intro _; exact Or.inl hsyn
    | _ => trivial
  · have hne : A.g ≠ .syntactic := by
      rintro heq; rw [heq] at hcode; simp [codeGrammars] at hcode
    have hokIt : codeItemOk A.cx A.g it = true := codeItemOk_of_mem hok hcode hs hit
    cases it with
    | lookahead l =>
      cases l with
      | eq q | ne q | mem q | notMem q => intro heq; exact absurd heq hne
      | notMemNT m =>
        simp only [codeItemOk, Bool.and_eq_true, Bool.not_eq_true'] at hokIt
        exact ⟨hne, hokIt⟩
    | butNot base ex =>
      simp only [codeItemOk] at hokIt
      cases ex with
      | sym y =>
        cases y with
        | t _ => trivial
        | nt m _ => intro _; exact Or.inr hokIt
      | oneOf ys _ =>
        intro y hy
        have hy' := List.all_eq_true.mp hokIt y hy
        cases y with
        | t _ => trivial
        | nt m _ => intro _; exact Or.inr hy'
    | _ => trivial

/-- Pure relational specification of an `Alpha N T` under state invariant `Inv`. -/
structure AlphaSpec {N T : Type} (B : Builder N) (A : Alpha N T) (size : Nat) where
  Inv : St T → Prop
  Term : Src → Nat → Terminal → Nat → Nat → Prop
  Leaf : NT → Nat → Nat → Prop
  Phrase : Ecma.Grammar.Phrase → Nat → Nat → Prop
  Cond : Ecma.Grammar.Phrase → Nat → Nat → Prop
  NoLT : Nat → Prop
  Starts : List LookItem → Nat → Prop
  NegSpan : NT → List Param → Nat → Nat → Prop
  NegAny : NT → Nat → Prop
  SpanOf : Nat → Nat → Nat × Nat
  TextOf : Nat → Nat → Array Nat
  LeafNodeRel : (stamp : Nat) → NT → Nat → Nat → N → Prop
  LeafStamp : Option Nat := none
  /-- State transitions preserve `Inv` -/
  inv_mono_memo : ∀ (s : St T) m a r f fw fi, Inv s →
    Inv { s with memo := m, active := a, reads := r, far := f, fwd := fw, first := fi }
  inv_tick : ∀ (s : St T) k, Inv s → Inv { s with steps := k }
  term_bound : ∀ s k x i j, Term s k x i j → i < j ∧ j ≤ size
  leaf_bound : ∀ n i j, Leaf n i j → i < j ∧ j ≤ size
  phrase_bound : ∀ p i j, Phrase p i j → i < j ∧ j ≤ size
  term_det : ∀ s k x i j1 j2, Term s k x i j1 → Term s k x i j2 → j1 = j2
  leaf_det : ∀ n i j1 j2, Leaf n i j1 → Leaf n i j2 → j1 = j2
  phrase_det : ∀ p i j1 j2, Phrase p i j1 → Phrase p i j2 → j1 = j2
  keepAll_sound : ∀ lhs n j, A.keepAll lhs n = true → A.keep lhs n j = true
  hit_spec : ∀ j st, Inv st → ∀ u st', (A.hit j).run st = .ok (u, st') →
    Inv st' ∧ st'.memo = st.memo ∧ st'.active = st.active ∧ st'.reads = st.reads ∧
    st'.fwd = st.fwd ∧ st'.first = st.first ∧ st'.far = max st.far j
  term_spec : ∀ s k x i st, Inv st → ∀ r st', (A.term s k x i).run st = .ok (r, st') →
    Inv st' ∧ st'.memo = st.memo ∧ st'.active = st.active ∧ st'.reads = st.reads ∧
    st'.fwd = st.fwd ∧ st'.first = st.first ∧ st'.far = st.far ∧
    ((∃ j, r = some j ∧ Term s k x i j) ∨ (r = none ∧ ∀ j, ¬ Term s k x i j))
  leaf_spec : ∀ n i st, Inv st → ∀ r st', (A.leaf n i).run st = .ok (r, st') →
    Inv st' ∧ st'.memo = st.memo ∧ st'.active = st.active ∧ st'.reads = st.reads ∧
    st'.fwd = st.fwd ∧ st'.first = st.first ∧ st'.far = st.far ∧
    ((∃ j, r = some j ∧ Leaf n i j) ∨ (r = none ∧ ∀ j, ¬ Leaf n i j))
  phrase_spec : ∀ p i st, Inv st → ∀ r st', (A.phrase p i).run st = .ok (r, st') →
    Inv st' ∧ st'.memo = st.memo ∧ st'.active = st.active ∧ st'.reads = st.reads ∧
    st'.fwd = st.fwd ∧ st'.first = st.first ∧ st'.far = st.far ∧
    ((∃ j, r = some j ∧ Phrase p i j) ∨ (r = none ∧ ∀ j, ¬ Phrase p i j))
  cond_spec : ∀ c a b st, Inv st → ∀ r st', (A.cond c a b).run st = .ok (r, st') →
    Inv st' ∧ st'.memo = st.memo ∧ st'.active = st.active ∧ st'.reads = st.reads ∧
    st'.fwd = st.fwd ∧ st'.first = st.first ∧ st'.far = st.far ∧
    (r = true ↔ Cond c a b)
  noLT_spec : ∀ i st, Inv st → ∀ r st', (A.noLT i).run st = .ok (r, st') →
    Inv st' ∧ st'.memo = st.memo ∧ st'.active = st.active ∧ st'.reads = st.reads ∧
    st'.fwd = st.fwd ∧ st'.first = st.first ∧ st'.far = st.far ∧
    (r = true ↔ NoLT i)
  starts_spec : ∀ (q : List LookItem) i st, Inv st →
    (A.g = .syntactic → lookSeqsOk synLookTermOk [q] = true) →
    ∀ r st', (A.starts q i).run st = .ok (r, st') →
    Inv st' ∧ st'.memo = st.memo ∧ st'.active = st.active ∧ st'.reads = st.reads ∧
    st'.fwd = st.fwd ∧ st'.first = st.first ∧ st'.far = st.far ∧
    (r = true ↔ Starts q i)
  negSpan_spec : ∀ n ps a b st, Inv st →
    (A.g = .syntactic ∨ posBounded A.cx A.g 16 n = true) →
    ∀ r st', (A.negSpan n ps a b).run st = .ok (r, st') →
    Inv st' ∧ st'.memo = st.memo ∧ st'.active = st.active ∧ st'.reads = st.reads ∧
    st'.fwd = st.fwd ∧ st'.first = st.first ∧ st'.far = st.far ∧
    (r = true ↔ NegSpan n ps a b)
  negAny_spec : ∀ n a st, Inv st →
    (A.g ≠ .syntactic →
      (glData.alts A.cx A.g n).isEmpty = false ∧
      (glData.alts A.cx A.g n).all (fun e => e.alt.guard.isEmpty &&
        match e.alt.rhs with | [.sym (.t x) false] => codeLookTermOk x | _ => false) = true) →
    ∀ r st', (A.negAny n a).run st = .ok (r, st') →
    Inv st' ∧ st'.memo = st.memo ∧ st'.active = st.active ∧ st'.reads = st.reads ∧
    st'.fwd = st.fwd ∧ st'.first = st.first ∧ st'.far = st.far ∧
    (r = true ↔ NegAny n a)
  span_spec : ∀ lo hi st, Inv st → ∀ r st', (A.span lo hi).run st = .ok (r, st') →
    Inv st' ∧ st'.memo = st.memo ∧ st'.active = st.active ∧ st'.reads = st.reads ∧
    st'.fwd = st.fwd ∧ st'.first = st.first ∧ st'.far = st.far ∧ r = SpanOf lo hi
  text_spec : ∀ lo hi st, Inv st → ∀ r st', (A.text lo hi).run st = .ok (r, st') →
    Inv st' ∧ st'.memo = st.memo ∧ st'.active = st.active ∧ st'.reads = st.reads ∧
    st'.fwd = st.fwd ∧ st'.first = st.first ∧ st'.far = st.far ∧ r.toArray = TextOf lo hi
  leafNode_spec : ∀ stamp n a b st, LeafStamp.all (· == stamp) = true → Inv st →
    ∀ nd st', (A.leafNode n a b).run st = .ok (nd, st') →
    Inv st' ∧ st'.memo = st.memo ∧ st'.active = st.active ∧ st'.reads = st.reads ∧
    st'.fwd = st.fwd ∧ st'.first = st.first ∧ st'.far = st.far ∧
    B.nt nd = n.ctorIdx ∧ B.args nd = [] ∧ B.span nd = SpanOf a b ∧ B.stamp nd = stamp ∧
    Leaf n a b ∧ LeafNodeRel stamp n a b nd

/-- Derivation tree over `AlphaSpec`'s positions. -/
inductive DTree where
  | leaf (i j : Nat)
  | lex (n : NT) (i j : Nat)
  | node (n : NT) (id : Nat) (s : Src) (ps : List Param) (i j : Nat) (mask : List Bool) (kids : List DTree)

def DTree.isLeaf : DTree → Bool
  | .leaf .. => true
  | _ => false

def DTree.span : DTree → Nat × Nat
  | .leaf i j => (i, j)
  | .lex _ i j => (i, j)
  | .node _ _ _ _ i j _ _ => (i, j)

namespace AlphaSpec

variable {N T : Type} {B : Builder N} {A : Alpha N T} {size : Nat} (S : AlphaSpec B A size)

/-- Pure lookahead satisfaction under `S`. -/
def LookHolds : Lookahead → Nat → Prop
  | .eq q, j => S.Starts q j
  | .ne q, j => ¬ S.Starts q j
  | .mem qs, j => ∃ q ∈ qs, S.Starts q j
  | .notMem qs, j => ∀ q ∈ qs, ¬ S.Starts q j
  | .notMemNT n, j => ¬ S.NegAny n j

/-- Pure symbol exclusion under `S`. -/
def SymHolds (s : Src) (k : Nat) (ps : List Param) (i h : Nat) : Sym → Prop
  | .t x => S.Term s k x i h
  | .nt n args =>
    if !(altsOf A.cx A.g n).isEmpty then S.NegSpan n (applyArgs ps args) i h
    else S.Leaf n i h

/-- Pure `Exclusion` satisfaction under `S`. -/
def ExclHolds (s : Src) (k : Nat) (ps : List Param) (i h : Nat) : Exclusion → Prop
  | .sym y => S.SymHolds s k ps i h y
  | .oneOf ys _ => ∃ y ∈ ys, S.SymHolds s k ps i h y

/-- Pure post-item condition satisfaction under `S`. -/
def CondHolds (is : List Item) (i h : Nat) : Prop :=
  match condAfter is with
  | some c => S.Cond c i h
  | none => True

mutual
/-- One-stratum derivation tree under `S`, optionally restricted by `allow` (for B.1.2 commitment). -/
inductive DerivesWith (allow : NT → List Param → Nat → Src → Prop) :
    NT → List Param → Nat → Nat → DTree → Prop where
  | node {n ps i j m kids id} (s : Src) :
      s ∈ altsOf A.cx A.g n →
      allow n ps i s →
      s.alt.guard.all (Guard.holds ps) = true →
      prodIdOf s m = some id →
      SeqWith allow s ps 0 s.alt.rhs i j m kids →
      DerivesWith allow n ps i j (.node n id s ps i j m kids)

/-- Right-hand side sequence derivation under `S`. -/
inductive SeqWith (allow : NT → List Param → Nat → Src → Prop) :
    Src → List Param → Nat → List Item → Nat → Nat → List Bool → List DTree → Prop where
  | nil {s ps k i} : SeqWith allow s ps k [] i i [] []
  | absent {s ps k x is i j m ts} :
      SeqWith allow s ps (k + 1) is i j m ts →
      SeqWith allow s ps k (.sym x true :: is) i j (false :: m) ts
  | term {s ps k x o is i h j m ts} :
      S.Term s k x i h →
      SeqWith allow s ps (k + 1) is h j m ts →
      SeqWith allow s ps k (.sym (.t x) o :: is) i j (if o then true :: m else m) (.leaf i h :: ts)
  | nt {s ps k n args o is i h j m t ts} :
      (altsOf A.cx A.g n).isEmpty = false →
      DerivesWith allow n (applyArgs ps args) i h t →
      A.keep s.rule.lhs n h = true →
      S.CondHolds is i h →
      SeqWith allow s ps (k + 1) is h j m ts →
      SeqWith allow s ps k (.sym (.nt n args) o :: is) i j (if o then true :: m else m) (t :: ts)
  | leaf {s ps k n args o is i h j m ts} :
      (altsOf A.cx A.g n).isEmpty = true →
      S.Leaf n i h →
      A.keep s.rule.lhs n h = true →
      S.CondHolds is i h →
      SeqWith allow s ps (k + 1) is h j m ts →
      SeqWith allow s ps k (.sym (.nt n args) o :: is) i j (if o then true :: m else m) (.lex n i h :: ts)
  | butNotT {s ps k x ex is i h j m ts} :
      S.Term s k x i h →
      ¬ S.ExclHolds s k ps i h ex →
      SeqWith allow s ps (k + 1) is h j m ts →
      SeqWith allow s ps k (.butNot (.t x) ex :: is) i j m (.leaf i h :: ts)
  | butNotN {s ps k n args ex is i h j m t ts} :
      (altsOf A.cx A.g n).isEmpty = false →
      DerivesWith allow n (applyArgs ps args) i h t →
      A.keep s.rule.lhs n h = true →
      ¬ S.ExclHolds s k ps i h ex →
      SeqWith allow s ps (k + 1) is h j m ts →
      SeqWith allow s ps k (.butNot (.nt n args) ex :: is) i j m (t :: ts)
  | butNotLeaf {s ps k n args ex is i h j m ts} :
      (altsOf A.cx A.g n).isEmpty = true →
      S.Leaf n i h →
      A.keep s.rule.lhs n h = true →
      ¬ S.ExclHolds s k ps i h ex →
      SeqWith allow s ps (k + 1) is h j m ts →
      SeqWith allow s ps k (.butNot (.nt n args) ex :: is) i j m (.lex n i h :: ts)
  | phrase {s ps k p is i h j m ts} :
      S.Phrase p i h →
      SeqWith allow s ps (k + 1) is h j m ts →
      SeqWith allow s ps k (.phrase p :: is) i j m (.leaf i h :: ts)
  | look {s ps k l is i j m ts} :
      S.LookHolds l i →
      SeqWith allow s ps (k + 1) is i j m ts →
      SeqWith allow s ps k (.lookahead l :: is) i j m ts
  | noLT {s ps k is i j m ts} :
      S.NoLT i →
      SeqWith allow s ps (k + 1) is i j m ts →
      SeqWith allow s ps k (.noLT :: is) i j m ts
  | empty {s ps k is i j m ts} :
      SeqWith allow s ps (k + 1) is i j m ts →
      SeqWith allow s ps k (.empty :: is) i j m ts
  | onlyIf {s ps k c is i j m ts} :
      SeqWith allow s ps (k + 1) is i j m ts →
      SeqWith allow s ps k (.onlyIf c :: is) i j m ts
end

theorem DerivesWith.not_isLeaf {allow n ps i j t} (h : S.DerivesWith allow n ps i j t) :
    (!t.isLeaf) = true := by
  cases h; rfl

/-- Uncommitted derivation (`c = false` or `orderedBy = false`). -/
abbrev PlainDerives : NT → List Param → Nat → Nat → DTree → Prop :=
  S.DerivesWith (fun _ _ _ _ => True)

/-- Whether `s` is the first alternative of `n` under `ps` at `i` deriving some span in `PlainDerives`. -/
def IsFirstAlt (n : NT) (ps : List Param) (i : Nat) (s : Src) : Prop :=
  ∃ pre post, altsOf A.cx A.g n = pre ++ s :: post ∧
    s.alt.guard.all (Guard.holds ps) = true ∧
    (∃ h m kids, S.SeqWith (fun _ _ _ _ => True) s ps 0 s.alt.rhs i h m kids) ∧
    ∀ s' ∈ pre, s'.alt.guard.all (Guard.holds ps) = true →
      ¬ ∃ h m kids, S.SeqWith (fun _ _ _ _ => True) s' ps 0 s'.alt.rhs i h m kids

/-- Commitment predicate for mode `c : Bool`. -/
def CommitAllow (c : Bool) (n : NT) (ps : List Param) (i : Nat) (s : Src) : Prop :=
  if c && (orderedNtsBy A.cx A.g).contains n then S.IsFirstAlt n ps i s else True

/-- Derivation in mode `c : Bool` (`false` = plain, `true` = committed where B.1.2 orders). -/
abbrev ModeDerives (c : Bool) : NT → List Param → Nat → Nat → DTree → Prop :=
  S.DerivesWith (S.CommitAllow c)

mutual
/-- Relation between a built node `nd : N` and a `DTree` at parser invocation `stamp`. -/
inductive DNodeRel (stamp : Nat) : N → DTree → Prop where
  | lex {nd : N} {n : NT} {i j : Nat} :
      B.nt nd = n.ctorIdx →
      B.args nd = [] →
      B.span nd = S.SpanOf i j →
      B.stamp nd = stamp →
      S.LeafNodeRel stamp n i j nd →
      DNodeRel stamp nd (.lex n i j)
  | node {nd : N} {n : NT} {id : Nat} {s : Src} {ps : List Param} {i j : Nat}
      {mask : List Bool} {kids : List DTree} :
      B.nt nd = n.ctorIdx →
      B.prod nd = id →
      B.args nd = ps →
      B.stamp nd = stamp →
      B.span nd = S.SpanOf i j →
      B.text nd = S.TextOf i j →
      DNodeRelList stamp ((B.kids nd).toList.filterMap Prod.snd) (kids.filter fun t => !t.isLeaf) →
      DNodeRel stamp nd (.node n id s ps i j mask kids)

/-- Pointwise `DNodeRel` over lists of children and non-leaf `DTree`s. -/
inductive DNodeRelList (stamp : Nat) : List N → List DTree → Prop where
  | nil : DNodeRelList stamp [] []
  | cons {c : N} {t : DTree} {cs : List N} {ts : List DTree} :
      DNodeRel stamp c t →
      DNodeRelList stamp cs ts →
      DNodeRelList stamp (c :: cs) (t :: ts)
end

/-! ## Soundness of `lookOk` and `excluded` -/

private theorem anyM_starts_spec (qs : List (List LookItem)) (j : Nat) (st : St T)
    (hinv : S.Inv st)
    (hwf : A.g = .syntactic → lookSeqsOk synLookTermOk qs = true)
    (r : Bool) (st' : St T)
    (hrun : (qs.anyM (A.starts · j)).run st = .ok (r, st')) :
    S.Inv st' ∧ st'.memo = st.memo ∧ st'.active = st.active ∧ st'.reads = st.reads ∧
    st'.fwd = st.fwd ∧ st'.first = st.first ∧ st'.far = st.far ∧
    (r = true ↔ ∃ q ∈ qs, S.Starts q j) := by
  induction qs generalizing st with
  | nil =>
    rw [List.anyM_nil] at hrun
    obtain ⟨hfalse, rfl⟩ := sm_pure_ok hrun
    subst hfalse
    exact ⟨hinv, rfl, rfl, rfl, rfl, rfl, rfl, by simp⟩
  | cons q rest ih =>
    rw [List.anyM_cons] at hrun
    have hqwf : A.g = .syntactic → lookSeqsOk synLookTermOk [q] = true := fun hg => by
      have h := hwf hg; simp only [lookSeqsOk, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true] at h ⊢
      exact h.1
    have hrwf : A.g = .syntactic → lookSeqsOk synLookTermOk rest = true := fun hg => by
      have h := hwf hg; simp only [lookSeqsOk, List.all_cons, Bool.and_eq_true] at h; exact h.2
    obtain ⟨b, st1, hs, hrun⟩ := sm_bind_ok hrun
    have ⟨hi1, hm1, ha1, hrd1, hfw1, hfi1, hfar1, hb1⟩ := S.starts_spec q j st hinv hqwf b st1 hs
    cases b with
    | true =>
      obtain ⟨htrue, rfl⟩ := sm_pure_ok hrun
      subst htrue
      exact ⟨hi1, hm1, ha1, hrd1, hfw1, hfi1, hfar1,
        ⟨fun _ => ⟨q, List.mem_cons_self .., hb1.mp rfl⟩, fun _ => rfl⟩⟩
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte] at hrun
      have ⟨hi2, hm2, ha2, hrd2, hfw2, hfi2, hfar2, hb2⟩ := ih st1 hi1 hrwf hrun
      refine ⟨hi2, hm2.trans hm1, ha2.trans ha1, hrd2.trans hrd1, hfw2.trans hfw1, hfi2.trans hfi1,
        hfar2.trans hfar1, ?_⟩
      rw [hb2]
      constructor
      · rintro ⟨q', hq', hst⟩; exact ⟨q', List.mem_cons_of_mem _ hq', hst⟩
      · rintro ⟨q', hq', hst⟩
        rcases List.mem_cons.mp hq' with rfl | hq'
        · exact absurd (hb1.mpr hst) Bool.false_ne_true
        · exact ⟨q', hq', hst⟩

theorem lookOk_spec (l : Lookahead) (j : Nat) (st : St T) (hinv : S.Inv st) (hwf : LookWF A l)
    (r : Bool) (st' : St T) (hrun : (lookOk A l j).run st = .ok (r, st')) :
    S.Inv st' ∧ st'.memo = st.memo ∧ st'.active = st.active ∧ st'.reads = st.reads ∧
    st'.fwd = st.fwd ∧ st'.first = st.first ∧ st'.far = st.far ∧
    (r = true ↔ S.LookHolds l j) := by
  cases l with
  | eq q =>
    exact S.starts_spec q j st hinv hwf r st' hrun
  | ne q =>
    unfold lookOk at hrun
    obtain ⟨b, st1, hs, hrun⟩ := sm_bind_ok hrun
    have ⟨hi, hm, ha, hrd, hfw, hfi, hfar, hb⟩ := S.starts_spec q j st hinv hwf b st1 hs
    obtain ⟨hr, rfl⟩ := sm_pure_ok hrun
    subst hr
    exact ⟨hi, hm, ha, hrd, hfw, hfi, hfar, by simp [LookHolds, ← hb]⟩
  | mem qs =>
    exact anyM_starts_spec S qs j st hinv hwf r st' hrun
  | notMem qs =>
    unfold lookOk at hrun
    obtain ⟨b, st1, hs, hrun⟩ := sm_bind_ok hrun
    have ⟨hi, hm, ha, hrd, hfw, hfi, hfar, hb⟩ := anyM_starts_spec S qs j st hinv hwf b st1 hs
    obtain ⟨hr, rfl⟩ := sm_pure_ok hrun
    subst hr
    refine ⟨hi, hm, ha, hrd, hfw, hfi, hfar, ?_⟩
    simp only [Bool.not_eq_true', LookHolds]
    rw [← Bool.not_eq_true, hb]
    simp
  | notMemNT n =>
    unfold lookOk at hrun
    obtain ⟨hne, hwf'⟩ := hwf
    obtain ⟨b, st1, hs, hrun⟩ := sm_bind_ok hrun
    have ⟨hi, hm, ha, hrd, hfw, hfi, hfar, hb⟩ := S.negAny_spec n j st hinv (fun _ => hwf') b st1 hs
    obtain ⟨hr, rfl⟩ := sm_pure_ok hrun
    subst hr
    exact ⟨hi, hm, ha, hrd, hfw, hfi, hfar, by simp [LookHolds, ← hb]⟩

theorem symDerives_spec (s : Src) (k : Nat) (ps : List Param) (i h : Nat) (y : Sym)
    (st : St T) (hinv : S.Inv st)
    (hwf : match y with
      | .t _ => True
      | .nt m _ => (altsOf A.cx A.g m).isEmpty = false → A.g = .syntactic ∨ posBounded A.cx A.g 16 m = true)
    (r : Bool) (st' : St T) (hrun : (symDerives A s k ps i h y).run st = .ok (r, st')) :
    S.Inv st' ∧ st'.memo = st.memo ∧ st'.active = st.active ∧ st'.reads = st.reads ∧
    st'.fwd = st.fwd ∧ st'.first = st.first ∧ st'.far = st.far ∧
    (r = true ↔ S.SymHolds s k ps i h y) := by
  cases y with
  | t x =>
    unfold symDerives at hrun
    obtain ⟨o, st1, hs, hrun⟩ := sm_bind_ok hrun
    have ⟨hi, hm, ha, hrd, hfw, hfi, hfar, ho⟩ := S.term_spec s k x i st hinv o st1 hs
    obtain ⟨hr, rfl⟩ := sm_pure_ok hrun
    subst hr
    refine ⟨hi, hm, ha, hrd, hfw, hfi, hfar, ?_⟩
    simp only [SymHolds, beq_iff_eq]
    rcases ho with ⟨j, rfl, htj⟩ | ⟨rfl, hno⟩
    · simp only [Option.some.injEq]
      exact ⟨fun heq => heq ▸ htj, fun hth => S.term_det s k x i j h htj hth⟩
    · simp only [reduceCtorEq, false_iff]
      exact hno h
  | nt n args =>
    unfold symDerives at hrun
    cases hempty : (altsOf A.cx A.g n).isEmpty with
    | false =>
      have hrun' : (A.negSpan n (applyArgs ps args) i h).run st = .ok (r, st') := by
        simpa [hempty] using hrun
      have ⟨hi, hm, ha, hrd, hfw, hfi, hfar, hb⟩ :=
        S.negSpan_spec n (applyArgs ps args) i h st hinv (hwf hempty) r st' hrun'
      exact ⟨hi, hm, ha, hrd, hfw, hfi, hfar, by simp [SymHolds, hempty, hb]⟩
    | true =>
      have hrun' : (do let o ← A.leaf n i; pure (o == some h)).run st = .ok (r, st') := by
        simpa [hempty] using hrun
      obtain ⟨o, st1, hs, hrun'⟩ := sm_bind_ok hrun'
      have ⟨hi, hm, ha, hrd, hfw, hfi, hfar, ho⟩ := S.leaf_spec n i st hinv o st1 hs
      obtain ⟨hr, rfl⟩ := sm_pure_ok hrun'
      subst hr
      refine ⟨hi, hm, ha, hrd, hfw, hfi, hfar, ?_⟩
      simp only [SymHolds, hempty, Bool.not_true, Bool.false_eq_true, ↓reduceIte, beq_iff_eq]
      rcases ho with ⟨j, rfl, hlj⟩ | ⟨rfl, hno⟩
      · simp only [Option.some.injEq]
        exact ⟨fun heq => heq ▸ hlj, fun hlh => S.leaf_det n i j h hlj hlh⟩
      · simp only [reduceCtorEq, false_iff]
        exact hno h

theorem excluded_spec (s : Src) (k : Nat) (ps : List Param) (i h : Nat) (ex : Exclusion)
    (st : St T) (hinv : S.Inv st) (hwf : ExclWF A ex)
    (r : Bool) (st' : St T) (hrun : (excluded A s k ps i h ex).run st = .ok (r, st')) :
    S.Inv st' ∧ st'.memo = st.memo ∧ st'.active = st.active ∧ st'.reads = st.reads ∧
    st'.fwd = st.fwd ∧ st'.first = st.first ∧ st'.far = st.far ∧
    (r = true ↔ S.ExclHolds s k ps i h ex) := by
  cases ex with
  | sym y =>
    exact symDerives_spec S s k ps i h y st hinv hwf r st' hrun
  | oneOf ys sep =>
    unfold excluded at hrun
    have hany : ∀ (ys : List Sym) (st0 : St T), S.Inv st0 →
        (∀ y ∈ ys, match y with
          | .t _ => True
          | .nt m _ => (altsOf A.cx A.g m).isEmpty = false → A.g = .syntactic ∨ posBounded A.cx A.g 16 m = true) →
        ∀ r0 st1, (ys.anyM (symDerives A s k ps i h)).run st0 = .ok (r0, st1) →
        S.Inv st1 ∧ st1.memo = st0.memo ∧ st1.active = st0.active ∧ st1.reads = st0.reads ∧
        st1.fwd = st0.fwd ∧ st1.first = st0.first ∧ st1.far = st0.far ∧
        (r0 = true ↔ ∃ y ∈ ys, S.SymHolds s k ps i h y) := by
      intro ys
      induction ys with
      | nil =>
        intro st0 hi0 _ r0 st1 hr0
        rw [List.anyM_nil] at hr0
        obtain ⟨hfalse, rfl⟩ := sm_pure_ok hr0
        subst hfalse
        exact ⟨hi0, rfl, rfl, rfl, rfl, rfl, rfl, by simp⟩
      | cons y rest ih =>
        intro st0 hi0 hywf r0 st1 hr0
        rw [List.anyM_cons] at hr0
        obtain ⟨b, stMid, hy, hr0⟩ := sm_bind_ok hr0
        have ⟨hiM, hmM, haM, hrdM, hfwM, hfiM, hfarM, hbM⟩ :=
          symDerives_spec S s k ps i h y st0 hi0 (hywf y (List.mem_cons_self ..)) b stMid hy
        cases b with
        | true =>
          obtain ⟨htrue, rfl⟩ := sm_pure_ok hr0
          subst htrue
          exact ⟨hiM, hmM, haM, hrdM, hfwM, hfiM, hfarM,
            ⟨fun _ => ⟨y, List.mem_cons_self .., hbM.mp rfl⟩, fun _ => rfl⟩⟩
        | false =>
          simp only [Bool.false_eq_true, ↓reduceIte] at hr0
          have ⟨hi1, hm1, ha1, hrd1, hfw1, hfi1, hfar1, hb1⟩ :=
            ih stMid hiM (fun y' hy' => hywf y' (List.mem_cons_of_mem _ hy')) r0 st1 hr0
          refine ⟨hi1, hm1.trans hmM, ha1.trans haM, hrd1.trans hrdM, hfw1.trans hfwM,
            hfi1.trans hfiM, hfar1.trans hfarM, ?_⟩
          rw [hb1]
          constructor
          · rintro ⟨y', hy', hsh⟩; exact ⟨y', List.mem_cons_of_mem _ hy', hsh⟩
          · rintro ⟨y', hy', hsh⟩
            rcases List.mem_cons.mp hy' with rfl | hy'
            · exact absurd (hbM.mpr hsh) Bool.false_ne_true
            · exact ⟨y', hy', hsh⟩
    exact hany ys st hinv hwf r st' hrun

/-! ## Soundness of `walk` and `mk` -/

/-- Pre-condition on a `Piece N` supplied to `Kernel.walk` / `Kernel.mk`. -/
inductive PieceValid (allow : NT → List Param → Nat → Src → Prop) (stamp : Nat) : Piece N → Prop where
  | span (a b : Nat) : PieceValid allow stamp (.span a b)
  | absent : PieceValid allow stamp .absent
  | zero : PieceValid allow stamp .zero
  | kidRule {c : N} {n : NT} {a b : Nat} {t : DTree} :
      (altsOf A.cx A.g n).isEmpty = false →
      B.nt c = n.ctorIdx →
      S.DerivesWith allow n (B.args c) a b t →
      S.DNodeRel stamp c t →
      PieceValid allow stamp (.kid c a b)
  | kidLeaf {c : N} {n : NT} {a b : Nat} :
      (altsOf A.cx A.g n).isEmpty = true →
      B.nt c = n.ctorIdx →
      S.DNodeRel stamp c (.lex n a b) →
      PieceValid allow stamp (.kid c a b)

theorem DNodeRelList.append {stamp : Nat} : ∀ {cs1 cs2 : List N} {ts1 ts2 : List DTree},
    S.DNodeRelList stamp cs1 ts1 → S.DNodeRelList stamp cs2 ts2 →
    S.DNodeRelList stamp (cs1 ++ cs2) (ts1 ++ ts2)
  | _, _, _, _, .nil, h2 => h2
  | _, _, _, _, .cons hd tl, h2 => .cons hd (DNodeRelList.append tl h2)

private theorem walk_one_sound {allow : NT → List Param → Nat → Src → Prop} {stamp : Nat}
    {s : Src} {ps : List Param} {k : Nat} {x : Sym} {is : List Item} {pc : Piece N}
    {pos : Nat} {kids : Array (Nat × Option N)} {st : St T} {pos' : Nat} {kids' : Array (Nat × Option N)} {st' : St T}
    (hinv : S.Inv st)
    (hpc : S.PieceValid allow stamp pc)
    (hrun : (walk.one B A s ps k x is pc pos kids).run st = .ok ((pos', kids'), st')) :
    S.Inv st' ∧ st'.memo = st.memo ∧ st'.active = st.active ∧ st'.reads = st.reads ∧
    st'.fwd = st.fwd ∧ st'.first = st.first ∧ st'.far = st.far ∧
    match x with
    | .t tm =>
      S.Term s k tm pos pos' ∧ kids' = kids
    | .nt n args =>
      A.keep s.rule.lhs n pos' = true ∧ S.CondHolds is pos pos' ∧
      ∃ c t, kids' = kids.push (n.ctorIdx, some c) ∧ (!t.isLeaf) = true ∧ S.DNodeRel stamp c t ∧
        (((altsOf A.cx A.g n).isEmpty = false ∧ S.DerivesWith allow n (applyArgs ps args) pos pos' t) ∨
         ((altsOf A.cx A.g n).isEmpty = true ∧ S.Leaf n pos pos' ∧ t = .lex n pos pos')) := by
  cases pc with
  | absent | zero =>
    unfold walk.one at hrun; rw [sm_run_throw] at hrun; cases hrun
  | span a b =>
    cases x with
    | nt n args =>
      unfold walk.one at hrun; rw [sm_run_throw] at hrun; cases hrun
    | t tm =>
      dsimp only
      unfold walk.one at hrun
      obtain ⟨o, st1, ht, hrun⟩ := sm_bind_ok hrun
      dsimp only at hrun
      obtain ⟨hchk, hrun⟩ := sm_guard_true hrun
      have ⟨hi1, hm1, ha1, hrd1, hfw1, hfi1, hfar1, ho⟩ := S.term_spec s k tm a st hinv o st1 ht
      obtain ⟨hpEq, rfl⟩ := sm_pure_ok hrun
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj hpEq.symm
      simp only [Bool.and_eq_true, beq_iff_eq] at hchk
      obtain ⟨rfl, rfl⟩ := hchk
      rcases ho with ⟨j, hj, hterm⟩ | ⟨hnone, _⟩
      · cases hj; exact ⟨hi1, hm1, ha1, hrd1, hfw1, hfi1, hfar1, hterm, rfl⟩
      · cases hnone
  | kid c a b =>
    cases x with
    | t tm =>
      unfold walk.one at hrun; rw [sm_run_throw] at hrun; cases hrun
    | nt n args =>
      dsimp only
      unfold walk.one at hrun
      obtain ⟨sp, st1, hsp, hr1⟩ := sm_bind_ok hrun
      dsimp only at hr1
      obtain ⟨hchk1, hr2⟩ := sm_guard_true hr1
      have ⟨hi1, hm1, ha1, hrd1, hfw1, hfi1, hfar1, _⟩ := S.span_spec a b st hinv sp st1 hsp
      simp only [Bool.and_eq_true, beq_iff_eq] at hchk1
      obtain ⟨⟨⟨hntc, rfl⟩, hkeep⟩, _⟩ := hchk1
      have hcondStep : ∀ (stMid : St T) (hiM : S.Inv stMid)
          (hmM : stMid.memo = st.memo) (haM : stMid.active = st.active)
          (hrdM : stMid.reads = st.reads) (hfwM : stMid.fwd = st.fwd)
          (hfiM : stMid.first = st.first) (hfarM : stMid.far = st.far),
          (do
            if let some p := condAfter is then
              unless ← A.cond p a b do throw (Stop.check "a condition")
            pure (b, kids.push (n.ctorIdx, some c))).run stMid = .ok ((pos', kids'), st') →
          S.Inv st' ∧ st'.memo = st.memo ∧ st'.active = st.active ∧ st'.reads = st.reads ∧
          st'.fwd = st.fwd ∧ st'.first = st.first ∧ st'.far = st.far ∧
          pos' = b ∧ kids' = kids.push (n.ctorIdx, some c) ∧ S.CondHolds is a b := by
        intro stMid hiM hmM haM hrdM hfwM hfiM hfarM hcrun
        cases hca : condAfter is with
        | none =>
          have hcrun' : (pure (b, kids.push (n.ctorIdx, some c)) : SM T _).run stMid = .ok ((pos', kids'), st') := by
            simpa [hca] using hcrun
          obtain ⟨hpEq, rfl⟩ := sm_pure_ok hcrun'
          obtain ⟨rfl, rfl⟩ := Prod.mk.inj hpEq.symm
          exact ⟨hiM, hmM, haM, hrdM, hfwM, hfiM, hfarM, rfl, rfl, by simp [CondHolds, hca]⟩
        | some p =>
          simp only [hca] at hcrun
          obtain ⟨cb, st2, hcd, hcr1⟩ := sm_bind_ok hcrun
          obtain ⟨rfl, hcr2⟩ := sm_guard_true hcr1
          have ⟨hi2, hm2, ha2, hrd2, hfw2, hfi2, hfar2, hcb⟩ := S.cond_spec p a b stMid hiM true st2 hcd
          obtain ⟨hpEq, rfl⟩ := sm_pure_ok hcr2
          obtain ⟨rfl, rfl⟩ := Prod.mk.inj hpEq.symm
          exact ⟨hi2, hm2.trans hmM, ha2.trans haM, hrd2.trans hrdM, hfw2.trans hfwM,
            hfi2.trans hfiM, hfar2.trans hfarM, rfl, rfl, by simp [CondHolds, hca, hcb.mp rfl]⟩
      cases hempty : (altsOf A.cx A.g n).isEmpty with
      | false =>
        simp only [hempty, Bool.not_false, ↓reduceIte] at hr2
        obtain ⟨hargs, hr3⟩ := sm_guard_true hr2
        rw [beq_iff_eq] at hargs
        have ⟨hiF, hmF, haF, hrdF, hfwF, hfiF, hfarF, hposEq, hkidsEq, hch⟩ :=
          hcondStep st1 hi1 hm1 ha1 hrd1 hfw1 hfi1 hfar1 hr3
        cases hpc with
        | kidRule hne' hnt' hder hdrel =>
          have heqn := nt_ctorIdx_inj (hntc.symm.trans hnt')
          subst heqn
          rw [hargs] at hder
          rw [hposEq, hkidsEq]
          exact ⟨hiF, hmF, haF, hrdF, hfwF, hfiF, hfarF, hkeep, hch, c, _, rfl,
            hder.not_isLeaf, hdrel, Or.inl ⟨rfl, hder⟩⟩
        | kidLeaf hemp' hnt' _ =>
          have heqn := nt_ctorIdx_inj (hntc.symm.trans hnt')
          subst heqn
          rw [hempty] at hemp'; cases hemp'
      | true =>
        simp only [hempty, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hr2
        obtain ⟨lo, stL, hlf, hr3⟩ := sm_bind_ok hr2
        obtain ⟨hchkL, hr4⟩ := sm_guard_true hr3
        have ⟨hiL, hmL, haL, hrdL, hfwL, hfiL, hfarL, hlo⟩ := S.leaf_spec n a st1 hi1 lo stL hlf
        simp only [Bool.and_eq_true, beq_iff_eq] at hchkL
        obtain ⟨_, hloEq⟩ := hchkL
        rcases hlo with ⟨j, hj, hleaf⟩ | ⟨hnone, _⟩
        · have hjb : j = b := Option.some.inj (hj.symm.trans hloEq)
          subst hjb
          have ⟨hiF, hmF, haF, hrdF, hfwF, hfiF, hfarF, hposEq, hkidsEq, hch⟩ :=
            hcondStep stL hiL (hmL.trans hm1) (haL.trans ha1) (hrdL.trans hrd1)
              (hfwL.trans hfw1) (hfiL.trans hfi1) (hfarL.trans hfar1) hr4
          cases hpc with
          | kidRule hne' hnt' _ _ =>
            have heqn := nt_ctorIdx_inj (hntc.symm.trans hnt')
            subst heqn
            rw [hempty] at hne'; cases hne'
          | kidLeaf _ hnt' hdrel =>
            have heqn := nt_ctorIdx_inj (hntc.symm.trans hnt')
            subst heqn
            rw [hposEq, hkidsEq]
            exact ⟨hiF, hmF, haF, hrdF, hfwF, hfiF, hfarF, hkeep, hch, c, .lex n a j, rfl,
              rfl, hdrel, Or.inr ⟨rfl, hleaf, rfl⟩⟩
        · rw [hnone] at hloEq; cases hloEq

theorem walk_sound {allow : NT → List Param → Nat → Src → Prop} {stamp : Nat}
    (s : Src) (ps : List Param) :
    ∀ (k : Nat) (is : List Item) (ms : List Bool) (pcs : List (Piece N))
      (pos : Nat) (kids : Array (Nat × Option N)) (st : St T) (pos' : Nat) (kids' : Array (Nat × Option N)) (st' : St T),
      S.Inv st →
      (∀ it ∈ is, ItemWF A it) →
      (∀ pc ∈ pcs, S.PieceValid allow stamp pc) →
      (walk B A s ps k is ms pcs pos kids).run st = .ok ((pos', kids'), st') →
      S.Inv st' ∧ st'.memo = st.memo ∧ st'.active = st.active ∧ st'.reads = st.reads ∧
      st'.fwd = st.fwd ∧ st'.first = st.first ∧ st'.far = st.far ∧
      ms ∈ masks ((is.filter fun | .sym _ true => true | _ => false).length) ∧
      ∃ ts, S.SeqWith allow s ps k is pos pos' ms ts ∧
        ∃ newNodes, kids'.toList.filterMap Prod.snd = kids.toList.filterMap Prod.snd ++ newNodes ∧
          S.DNodeRelList stamp newNodes (ts.filter fun t => !t.isLeaf) := by
  intro k is
  induction is generalizing k with
  | nil =>
    intro ms pcs pos kids st pos' kids' st' hinv _ _ hrun
    cases ms with
    | cons _ _ => unfold walk at hrun; rw [sm_run_throw] at hrun; cases hrun
    | nil =>
      cases pcs with
      | cons _ _ => unfold walk at hrun; rw [sm_run_throw] at hrun; cases hrun
      | nil =>
        unfold walk at hrun
        obtain ⟨hpEq, rfl⟩ := sm_pure_ok hrun
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj hpEq.symm
        exact ⟨hinv, rfl, rfl, rfl, rfl, rfl, rfl, by simp [masks], [], .nil, [], by simp, .nil⟩
  | cons it rest ih =>
    intro ms pcs pos kids st pos' kids' st' hinv hwf hpcs hrun
    have hitwf : ItemWF A it := hwf it (List.mem_cons_self ..)
    have hrwf : ∀ it' ∈ rest, ItemWF A it' := fun it' h => hwf it' (List.mem_cons_of_mem _ h)
    cases it with
    | sym x o =>
      cases o with
      | true =>
        cases ms with
        | nil => unfold walk at hrun; rw [sm_run_throw] at hrun; cases hrun
        | cons b ms' =>
          cases pcs with
          | nil => cases b <;> (unfold walk at hrun; rw [sm_run_throw] at hrun; cases hrun)
          | cons pc pcs' =>
            have hpc : S.PieceValid allow stamp pc := hpcs pc (List.mem_cons_self ..)
            have hpcs' : ∀ p ∈ pcs', S.PieceValid allow stamp p := fun p hp => hpcs p (List.mem_cons_of_mem _ hp)
            cases b with
            | false =>
              cases pc with
              | absent =>
                unfold walk at hrun
                cases x with
                | nt n args =>
                  dsimp only at hrun
                  have ⟨hi2, hm2, ha2, hrd2, hfw2, hfi2, hfar2, hmasks, ts, hseq, nn, hkidsEq, hf2⟩ :=
                    ih (k + 1) ms' pcs' pos (kids.push (n.ctorIdx, none)) st pos' kids' st' hinv hrwf hpcs' hrun
                  simp only [Array.toList_push, List.filterMap_append, List.filterMap_cons,
                    List.filterMap_nil, List.append_nil] at hkidsEq
                  have hmasks' : (false :: ms') ∈ masks (((.sym (.nt n args) true :: rest).filter fun | .sym _ true => true | _ => false).length) := by
                    rw [List.filter_cons_of_pos rfl, List.length_cons, masks]
                    exact List.mem_append.mpr (Or.inl (List.mem_map.mpr ⟨ms', hmasks, rfl⟩))
                  exact ⟨hi2, hm2, ha2, hrd2, hfw2, hfi2, hfar2, hmasks', ts, .absent hseq, nn, hkidsEq, hf2⟩
                | t tm =>
                  dsimp only at hrun
                  have ⟨hi2, hm2, ha2, hrd2, hfw2, hfi2, hfar2, hmasks, ts, hseq, nn, hkidsEq, hf2⟩ :=
                    ih (k + 1) ms' pcs' pos kids st pos' kids' st' hinv hrwf hpcs' hrun
                  have hmasks' : (false :: ms') ∈ masks (((.sym (.t tm) true :: rest).filter fun | .sym _ true => true | _ => false).length) := by
                    rw [List.filter_cons_of_pos rfl, List.length_cons, masks]
                    exact List.mem_append.mpr (Or.inl (List.mem_map.mpr ⟨ms', hmasks, rfl⟩))
                  exact ⟨hi2, hm2, ha2, hrd2, hfw2, hfi2, hfar2, hmasks', ts, .absent hseq, nn, hkidsEq, hf2⟩
              | span a b | kid c a b | zero =>
                unfold walk at hrun; rw [sm_run_throw] at hrun; cases hrun
            | true =>
              unfold walk at hrun
              obtain ⟨⟨mid, kidsMid⟩, stMid, hone, hrun⟩ := sm_bind_ok hrun
              have ⟨hi1, hm1, ha1, hrd1, hfw1, hfi1, hfar1, h1⟩ := walk_one_sound S hinv hpc hone
              have ⟨hi2, hm2, ha2, hrd2, hfw2, hfi2, hfar2, hmasks, ts, hseq, nn, hkidsEq, hf2⟩ :=
                ih (k + 1) ms' pcs' mid kidsMid stMid pos' kids' st' hi1 hrwf hpcs' hrun
              have hmasks' : (true :: ms') ∈ masks (((.sym x true :: rest).filter fun | .sym _ true => true | _ => false).length) := by
                rw [List.filter_cons_of_pos rfl, List.length_cons, masks]
                exact List.mem_append.mpr (Or.inr (List.mem_map.mpr ⟨ms', hmasks, rfl⟩))
              refine ⟨hi2, hm2.trans hm1, ha2.trans ha1, hrd2.trans hrd1, hfw2.trans hfw1,
                hfi2.trans hfi1, hfar2.trans hfar1, hmasks', ?_⟩
              cases x with
              | t tm =>
                obtain ⟨hterm, rfl⟩ := h1
                exact ⟨.leaf pos mid :: ts, .term hterm hseq, nn, hkidsEq, hf2⟩
              | nt n args =>
                obtain ⟨hkeep, hch, c, t, rfl, hnotLeaf, hdrel, hkind⟩ := h1
                simp only [Array.toList_push, List.filterMap_append, List.filterMap_cons,
                  List.filterMap_nil, List.append_assoc] at hkidsEq
                rcases hkind with ⟨hne, hder⟩ | ⟨hemp, hleaf, rfl⟩
                · refine ⟨t :: ts, .nt hne hder hkeep hch hseq, c :: nn, hkidsEq, ?_⟩
                  simp only [List.filter_cons, hnotLeaf, ↓reduceIte]
                  exact .cons hdrel hf2
                · refine ⟨.lex n pos mid :: ts, .leaf hemp hleaf hkeep hch hseq, c :: nn, hkidsEq, ?_⟩
                  simp only [List.filter_cons, DTree.isLeaf, Bool.not_false, ↓reduceIte]
                  exact .cons hdrel hf2
      | false =>
        cases pcs with
        | nil => unfold walk at hrun; rw [sm_run_throw] at hrun; cases hrun
        | cons pc pcs' =>
          have hpc : S.PieceValid allow stamp pc := hpcs pc (List.mem_cons_self ..)
          have hpcs' : ∀ p ∈ pcs', S.PieceValid allow stamp p := fun p hp => hpcs p (List.mem_cons_of_mem _ hp)
          unfold walk at hrun
          obtain ⟨⟨mid, kidsMid⟩, stMid, hone, hrun⟩ := sm_bind_ok hrun
          have ⟨hi1, hm1, ha1, hrd1, hfw1, hfi1, hfar1, h1⟩ := walk_one_sound S hinv hpc hone
          have ⟨hi2, hm2, ha2, hrd2, hfw2, hfi2, hfar2, hmasks, ts, hseq, nn, hkidsEq, hf2⟩ :=
            ih (k + 1) ms pcs' mid kidsMid stMid pos' kids' st' hi1 hrwf hpcs' hrun
          refine ⟨hi2, hm2.trans hm1, ha2.trans ha1, hrd2.trans hrd1, hfw2.trans hfw1,
            hfi2.trans hfi1, hfar2.trans hfar1, hmasks, ?_⟩
          cases x with
          | t tm =>
            obtain ⟨hterm, rfl⟩ := h1
            exact ⟨.leaf pos mid :: ts, .term hterm hseq, nn, hkidsEq, hf2⟩
          | nt n args =>
            obtain ⟨hkeep, hch, c, t, rfl, hnotLeaf, hdrel, hkind⟩ := h1
            simp only [Array.toList_push, List.filterMap_append, List.filterMap_cons,
              List.filterMap_nil, List.append_assoc] at hkidsEq
            rcases hkind with ⟨hne, hder⟩ | ⟨hemp, hleaf, rfl⟩
            · refine ⟨t :: ts, .nt hne hder hkeep hch hseq, c :: nn, hkidsEq, ?_⟩
              simp only [List.filter_cons, hnotLeaf, ↓reduceIte]
              exact .cons hdrel hf2
            · refine ⟨.lex n pos mid :: ts, .leaf hemp hleaf hkeep hch hseq, c :: nn, hkidsEq, ?_⟩
              simp only [List.filter_cons, DTree.isLeaf, Bool.not_false, ↓reduceIte]
              exact .cons hdrel hf2
    | butNot base ex =>
      cases pcs with
      | nil => unfold walk at hrun; rw [sm_run_throw] at hrun; cases hrun
      | cons pc pcs' =>
        have hpc : S.PieceValid allow stamp pc := hpcs pc (List.mem_cons_self ..)
        have hpcs' : ∀ p ∈ pcs', S.PieceValid allow stamp p := fun p hp => hpcs p (List.mem_cons_of_mem _ hp)
        unfold walk at hrun
        obtain ⟨⟨mid, kidsMid⟩, st1, hone, hrun⟩ := sm_bind_ok hrun
        have ⟨hi1, hm1, ha1, hrd1, hfw1, hfi1, hfar1, h1⟩ := walk_one_sound S hinv hpc hone
        obtain ⟨eb, st2, hex, hrun⟩ := sm_bind_ok hrun
        have ⟨hi2, hm2, ha2, hrd2, hfw2, hfi2, hfar2, heb⟩ :=
          excluded_spec S s k ps pos mid ex st1 hi1 hitwf eb st2 hex
        dsimp only at hrun
        cases eb with
        | true =>
          simp only [↓reduceIte] at hrun
          obtain ⟨_, _, ht, _⟩ := sm_bind_ok hrun; cases ht
        | false =>
          simp only [Bool.false_eq_true, ↓reduceIte] at hrun
          have hnotEx : ¬ S.ExclHolds s k ps pos mid ex := fun hexh => Bool.false_ne_true (heb.mpr hexh)
          have ⟨hi3, hm3, ha3, hrd3, hfw3, hfi3, hfar3, hmasks, ts, hseq, nn, hkidsEq, hf2⟩ :=
            ih (k + 1) ms pcs' mid kidsMid st2 pos' kids' st' hi2 hrwf hpcs' hrun
          refine ⟨hi3, hm3.trans (hm2.trans hm1), ha3.trans (ha2.trans ha1),
            hrd3.trans (hrd2.trans hrd1), hfw3.trans (hfw2.trans hfw1),
            hfi3.trans (hfi2.trans hfi1), hfar3.trans (hfar2.trans hfar1), hmasks, ?_⟩
          cases base with
          | t tm =>
            obtain ⟨hterm, rfl⟩ := h1
            exact ⟨.leaf pos mid :: ts, .butNotT hterm hnotEx hseq, nn, hkidsEq, hf2⟩
          | nt n args =>
            obtain ⟨hkeep, _, c, t, rfl, hnotLeaf, hdrel, hkind⟩ := h1
            simp only [Array.toList_push, List.filterMap_append, List.filterMap_cons,
              List.filterMap_nil, List.append_assoc] at hkidsEq
            rcases hkind with ⟨hne, hder⟩ | ⟨hemp, hleaf, rfl⟩
            · refine ⟨t :: ts, .butNotN hne hder hkeep hnotEx hseq, c :: nn, hkidsEq, ?_⟩
              simp only [List.filter_cons, hnotLeaf, ↓reduceIte]
              exact .cons hdrel hf2
            · refine ⟨.lex n pos mid :: ts, .butNotLeaf hemp hleaf hkeep hnotEx hseq, c :: nn, hkidsEq, ?_⟩
              simp only [List.filter_cons, DTree.isLeaf, Bool.not_false, ↓reduceIte]
              exact .cons hdrel hf2
    | phrase p =>
      cases pcs with
      | nil => unfold walk at hrun; rw [sm_run_throw] at hrun; cases hrun
      | cons pc pcs' =>
        cases pc with
        | kid _ _ _ | absent | zero => unfold walk at hrun; rw [sm_run_throw] at hrun; cases hrun
        | span a b =>
          have hpcs' : ∀ p' ∈ pcs', S.PieceValid allow stamp p' := fun p' hp => hpcs p' (List.mem_cons_of_mem _ hp)
          unfold walk at hrun
          obtain ⟨po, st1, hph, hr1⟩ := sm_bind_ok hrun
          dsimp only at hr1
          obtain ⟨hchk, hr2⟩ := sm_guard_true hr1
          clear hrun hr1
          have ⟨hi1, hm1, ha1, hrd1, hfw1, hfi1, hfar1, hpo⟩ := S.phrase_spec p a st hinv po st1 hph
          simp only [Bool.and_eq_true, beq_iff_eq] at hchk
          obtain ⟨rfl, hpob⟩ := hchk
          rcases hpo with ⟨j, rfl, hphr⟩ | ⟨hnone, _⟩
          · cases hpob
            have ⟨hi2, hm2, ha2, hrd2, hfw2, hfi2, hfar2, hmasks, ts, hseq, nn, hkidsEq, hf2⟩ :=
              ih (k + 1) ms pcs' b kids st1 pos' kids' st' hi1 hrwf hpcs' hr2
            exact ⟨hi2, hm2.trans hm1, ha2.trans ha1, hrd2.trans hrd1, hfw2.trans hfw1,
              hfi2.trans hfi1, hfar2.trans hfar1, hmasks,
              .leaf a b :: ts, .phrase hphr hseq, nn, hkidsEq, hf2⟩
          · rw [hnone] at hpob; cases hpob
    | lookahead l =>
      cases pcs with
      | nil => unfold walk at hrun; rw [sm_run_throw] at hrun; cases hrun
      | cons pc pcs' =>
        cases pc with
        | span _ _ | kid _ _ _ | absent => unfold walk at hrun; rw [sm_run_throw] at hrun; cases hrun
        | zero =>
          have hpcs' : ∀ p' ∈ pcs', S.PieceValid allow stamp p' := fun p' hp => hpcs p' (List.mem_cons_of_mem _ hp)
          unfold walk at hrun
          obtain ⟨lb, st1, hlk, hrun⟩ := sm_bind_ok hrun
          dsimp only at hrun
          obtain ⟨rfl, hrun⟩ := sm_guard_true hrun
          have ⟨hi1, hm1, ha1, hrd1, hfw1, hfi1, hfar1, hlb⟩ :=
            lookOk_spec S l pos st hinv hitwf true st1 hlk
          have ⟨hi2, hm2, ha2, hrd2, hfw2, hfi2, hfar2, hmasks, ts, hseq, nn, hkidsEq, hf2⟩ :=
            ih (k + 1) ms pcs' pos kids st1 pos' kids' st' hi1 hrwf hpcs' hrun
          exact ⟨hi2, hm2.trans hm1, ha2.trans ha1, hrd2.trans hrd1, hfw2.trans hfw1,
            hfi2.trans hfi1, hfar2.trans hfar1, hmasks,
            ts, .look (hlb.mp rfl) hseq, nn, hkidsEq, hf2⟩
    | noLT =>
      cases pcs with
      | nil => unfold walk at hrun; rw [sm_run_throw] at hrun; cases hrun
      | cons pc pcs' =>
        cases pc with
        | span _ _ | kid _ _ _ | absent => unfold walk at hrun; rw [sm_run_throw] at hrun; cases hrun
        | zero =>
          have hpcs' : ∀ p' ∈ pcs', S.PieceValid allow stamp p' := fun p' hp => hpcs p' (List.mem_cons_of_mem _ hp)
          unfold walk at hrun
          obtain ⟨nb, st1, hnl, hrun⟩ := sm_bind_ok hrun
          dsimp only at hrun
          obtain ⟨rfl, hrun⟩ := sm_guard_true hrun
          have ⟨hi1, hm1, ha1, hrd1, hfw1, hfi1, hfar1, hnb⟩ := S.noLT_spec pos st hinv true st1 hnl
          have ⟨hi2, hm2, ha2, hrd2, hfw2, hfi2, hfar2, hmasks, ts, hseq, nn, hkidsEq, hf2⟩ :=
            ih (k + 1) ms pcs' pos kids st1 pos' kids' st' hi1 hrwf hpcs' hrun
          exact ⟨hi2, hm2.trans hm1, ha2.trans ha1, hrd2.trans hrd1, hfw2.trans hfw1,
            hfi2.trans hfi1, hfar2.trans hfar1, hmasks,
            ts, .noLT (hnb.mp rfl) hseq, nn, hkidsEq, hf2⟩
    | empty =>
      cases pcs with
      | nil => unfold walk at hrun; rw [sm_run_throw] at hrun; cases hrun
      | cons pc pcs' =>
        cases pc with
        | span _ _ | kid _ _ _ | absent => unfold walk at hrun; rw [sm_run_throw] at hrun; cases hrun
        | zero =>
          have hpcs' : ∀ p' ∈ pcs', S.PieceValid allow stamp p' := fun p' hp => hpcs p' (List.mem_cons_of_mem _ hp)
          unfold walk at hrun
          have ⟨hi2, hm2, ha2, hrd2, hfw2, hfi2, hfar2, hmasks, ts, hseq, nn, hkidsEq, hf2⟩ :=
            ih (k + 1) ms pcs' pos kids st pos' kids' st' hinv hrwf hpcs' hrun
          exact ⟨hi2, hm2, ha2, hrd2, hfw2, hfi2, hfar2, hmasks, ts, .empty hseq, nn, hkidsEq, hf2⟩
    | onlyIf c =>
      cases pcs with
      | nil => unfold walk at hrun; rw [sm_run_throw] at hrun; cases hrun
      | cons pc pcs' =>
        cases pc with
        | span _ _ | kid _ _ _ | absent => unfold walk at hrun; rw [sm_run_throw] at hrun; cases hrun
        | zero =>
          have hpcs' : ∀ p' ∈ pcs', S.PieceValid allow stamp p' := fun p' hp => hpcs p' (List.mem_cons_of_mem _ hp)
          unfold walk at hrun
          have ⟨hi2, hm2, ha2, hrd2, hfw2, hfi2, hfar2, hmasks, ts, hseq, nn, hkidsEq, hf2⟩ :=
            ih (k + 1) ms pcs' pos kids st pos' kids' st' hinv hrwf hpcs' hrun
          exact ⟨hi2, hm2, ha2, hrd2, hfw2, hfi2, hfar2, hmasks, ts, .onlyIf hseq, nn, hkidsEq, hf2⟩

/-- Soundness of `Kernel.mk`: when `mk` succeeds on valid child pieces, it returns a node `nd`
matching a valid `DTree.node` derivation and preserves all state invariants. -/
theorem mk_sound (hok : parseTablesOk = true) (hB : BuilderSpec B)
    (hg : A.g = .syntactic ∨ A.g ∈ codeGrammars)
    {allow : NT → List Param → Nat → Src → Prop}
    {stamp p : Nat} {ps : List Param} {lo hi : Nat} {pieces : List (Piece N)}
    {st : St T} {nd : N} {st' : St T}
    (hinv : S.Inv st)
    (hpcs : ∀ pc ∈ pieces, S.PieceValid allow stamp pc)
    (hallow : ∀ P ef, prodOf p = some P →
      (altsOf A.cx A.g P.rule.lhs).find? (fun e => e.grammar == P.grammar && e.idx == P.alt && e.rule == P.rule) = some ef →
      prodIdOf ef P.mask = some p →
      allow P.rule.lhs ps lo ef)
    (hrun : (Engine.Parse.mk B A stamp p ps lo hi pieces).run st = .ok (nd, st')) :
    S.Inv st' ∧ st'.memo = st.memo ∧ st'.active = st.active ∧ st'.reads = st.reads ∧
    st'.fwd = st.fwd ∧ st'.first = st.first ∧ st'.far = st.far ∧
    ∃ n ef mask kids,
      B.nt nd = n.ctorIdx ∧
      S.DerivesWith allow n ps lo hi (.node n p ef ps lo hi mask kids) ∧
      S.DNodeRel stamp nd (.node n p ef ps lo hi mask kids) := by
  unfold Engine.Parse.mk at hrun
  cases hpo : prodOf p with
  | none => rw [hpo] at hrun; dsimp only at hrun; rw [sm_run_throw] at hrun; cases hrun
  | some P =>
    rw [hpo] at hrun; dsimp only at hrun
    cases hfind : (altsOf A.cx A.g P.rule.lhs).find?
        (fun e => e.grammar == P.grammar && e.idx == P.alt && e.rule == P.rule) with
    | none => rw [hfind] at hrun; dsimp only at hrun; rw [sm_run_throw] at hrun; cases hrun
    | some ef =>
      have hefMem : ef ∈ altsOf A.cx A.g P.rule.lhs := List.mem_of_find?_eq_some hfind
      rw [hfind] at hrun; dsimp only at hrun
      obtain ⟨hpid, hr1⟩ := sm_guard_true hrun
      rw [beq_iff_eq] at hpid
      obtain ⟨hgrd, hr2⟩ := sm_guard_true hr1
      obtain ⟨⟨eEnd, kidsArr⟩, st1, hwk, hr3⟩ := sm_bind_ok hr2
      have hwfAll : ∀ it ∈ ef.alt.rhs, ItemWF A it :=
        fun it hit => itemWF_of_mem A hok hg hefMem hit
      have ⟨hi1, hm1, ha1, hrd1, hfw1, hfi1, hfar1, _, ts, hseq, nn, hkidsEq, hf2⟩ :=
        walk_sound S ef ps 0 ef.alt.rhs P.mask pieces lo #[] st eEnd kidsArr st1 hinv hwfAll hpcs hwk
      dsimp only at hr3
      obtain ⟨hehi, hr4⟩ := sm_guard_true hr3
      clear hrun hr1 hr2 hr3
      rw [beq_iff_eq] at hehi; subst hehi
      obtain ⟨⟨spLo, spHi⟩, st2, hsp, hr5⟩ := sm_bind_ok hr4
      have ⟨hi2, hm2, ha2, hrd2, hfw2, hfi2, hfar2, hspEq⟩ :=
        S.span_spec lo eEnd st1 hi1 (spLo, spHi) st2 hsp
      obtain ⟨txtSub, st3, htx, hr6⟩ := sm_bind_ok hr5
      have ⟨hi3, hm3, ha3, hrd3, hfw3, hfi3, hfar3, htxEq⟩ :=
        S.text_spec lo eEnd st2 hi2 txtSub st3 htx
      obtain ⟨hndEq, rfl⟩ := sm_pure_ok hr6
      subst hndEq
      simp only [List.filterMap_nil, List.nil_append] at hkidsEq
      have hal : allow P.rule.lhs ps lo ef := hallow P ef hpo hfind hpid
      have hder : S.DerivesWith allow P.rule.lhs ps lo eEnd (.node P.rule.lhs p ef ps lo eEnd P.mask ts) :=
        .node ef hefMem hal hgrd hpid hseq
      have hdrel : S.DNodeRel stamp
          (B.node stamp spLo spHi p P.rule.lhs.ctorIdx ps kidsArr txtSub)
          (.node P.rule.lhs p ef ps lo eEnd P.mask ts) := by
        refine .node (hB.nt_node ..) (hB.prod_node ..) (hB.args_node ..)
          (hB.stamp_node ..) ?_ ?_ ?_
        · rw [hB.span_node, hspEq]
        · rw [hB.text_node, htxEq]
        · rw [hB.kids_node, hkidsEq]; exact hf2
      exact ⟨hi3, hm3.trans (hm2.trans hm1), ha3.trans (ha2.trans ha1),
        hrd3.trans (hrd2.trans hrd1), hfw3.trans (hfw2.trans hfw1),
        hfi3.trans (hfi2.trans hfi1), hfar3.trans (hfar2.trans hfar1),
        P.rule.lhs, ef, P.mask, ts, hB.nt_node .., hder, hdrel⟩

end AlphaSpec

end Engine.Parse
