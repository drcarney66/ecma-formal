module

public import Engine.Proofs.Seq
public import Ecma.Prims.Nodes
public import Ecma.Model.NodeRel
public import Ecma.Model.Laws

@[expose] public section

/-!
# The laws of Parent and of the Parse Node accessors at the engine's model

`nodeParent r n` is the search of the tree below `r` to its height (`parentBelow`): it answers only parents, and one
wherever there is one (`Model.ParentLaws.sound`, `complete`). A parent is higher than its child and no node of the
tree is higher than the root, so the parents from a node are fewer than the root's height
(`Model.ParentLaws.ancestors`); a child is lower than its parent (`Model.ParentLaws.height`). The occurrences and
descendants are `Model.NodeLaws`' but for `child_parse`, which is the checked parse's (`Proofs/Parse/Shape.lean`:
`Engine.Impl.nodeLaws`).
-/

namespace Engine.Impl
open Ecma Ecma.Model Engine.Model

/-- The engine's Parse Nodes. -/
local notation "Node" => Engine.Model.Node

/-- A Prop-valued membership fold is membership. -/
theorem foldl_mem {α : Type} (c : α) : ∀ (l : List α) (P : Prop), l.foldl (fun P x => P ∨ x = c) P ↔ P ∨ c ∈ l
  | [], P => by simp
  | x :: l, P => by
    rw [List.foldl_cons, foldl_mem c l]
    simp only [List.mem_cons]
    constructor
    · rintro ((h | rfl) | h) <;> simp_all
    · rintro (h | rfl | h) <;> simp_all

/-- An or-fold is `any`. -/
theorem foldl_or {α : Type} (g : α → Bool) : ∀ (l : List α) (b : Bool), l.foldl (fun b x => b || g x) b = (b || l.any g)
  | [], b => by simp
  | x :: l, b => by rw [List.foldl_cons, foldl_or g l, List.any_cons, Bool.or_assoc]

/-- An orElse-fold is `findSome?`. -/
theorem foldl_orElse {α β : Type} (h : α → Option β) :
    ∀ (l : List α) (a : Option β), l.foldl (fun acc x => acc <|> h x) a = (a <|> l.findSome? h)
  | [], a => by cases a <;> rfl
  | x :: l, a => by
    rw [List.foldl_cons, foldl_orElse h l, List.findSome?_cons]
    cases a <;> cases h x <;> rfl

/-- `findSome?` answers where some element does. -/
theorem findSome?_isSome {α β : Type} {h : α → Option β} {x : α} :
    ∀ {l : List α}, x ∈ l → (h x).isSome = true → (l.findSome? h).isSome = true
  | y :: l, hx, hs => by
    rw [List.findSome?_cons]
    cases hy : h y with
    | some _ => rfl
    | none =>
      rcases List.mem_cons.1 hx with rfl | hx
      · rw [hy] at hs; nomatch hs
      · exact findSome?_isSome hx hs

/-- `InSeq` is membership in the array. -/
theorem inSeq_iff {α : Type} (c : α) (s : Array α) : InSeq (M := Impl) c s ↔ c ∈ s.toList := by
  show Array.foldl (fun P x => P ∨ x = c) False s ↔ _
  rw [← Array.foldl_toList, foldl_mem]
  simp

theorem nodeKids_eq (p : Node) : Impl.nodeKids p = kidsOf p := by cases p; rfl

/-- A child is one of the node's children. -/
theorem kidOf_iff (n p : Node) : KidOf (M := Impl) n p ↔ n ∈ (kidsOf p).toList := by
  unfold KidOf
  constructor
  · rintro ⟨c, hc, hs⟩
    have : c = n := of_decide_eq_true hs
    subst this
    rw [nodeKids_eq] at hc
    exact (inSeq_iff c _).1 hc
  · intro h
    exact ⟨n, by rw [nodeKids_eq]; exact (inSeq_iff n _).2 h, decide_eq_true rfl⟩

theorem inKids_iff (c r : Node) : InSeq (M := Impl) c (Impl.nodeKids r) ↔ c ∈ (kidsOf r).toList := by
  rw [nodeKids_eq]; exact inSeq_iff c _

/-- The search's first test is `KidOf`. -/
theorem kidTest (n r : Node) : (kidsOf r).foldl (fun b c => b || decide (c = n)) false = true ↔ n ∈ (kidsOf r).toList := by
  rw [← Array.foldl_toList, foldl_or, Bool.false_or, List.any_eq_true]
  constructor
  · rintro ⟨c, hc, h⟩
    rw [← of_decide_eq_true h]; exact hc
  · intro h
    exact ⟨n, h, decide_eq_true rfl⟩

/-- `p` is `r` or a Parse Node below it, fewer than `f` child steps down. -/
inductive Reach : Nat → Node → Node → Prop
  | root (f : Nat) (r : Node) : Reach (f + 1) r r
  | kid {f : Nat} {r c p : Node} : c ∈ (kidsOf r).toList → Reach f c p → Reach (f + 1) r p

theorem Reach.mono {f g : Nat} {r p : Node} (h : Reach f r p) (hfg : f ≤ g) : Reach g r p := by
  induction h generalizing g with
  | root f r =>
    obtain ⟨g, rfl⟩ : ∃ g', g = g' + 1 := ⟨g - 1, by omega⟩
    exact .root g r
  | kid hc _ ih =>
    obtain ⟨g, rfl⟩ : ∃ g', g = g' + 1 := ⟨g - 1, by omega⟩
    exact .kid hc (ih (by omega))

/-- The search answers only a node at or below `r` of which `n` is a child. -/
theorem parentBelow_sound (n : Node) :
    ∀ f r p, parentBelow n f r = some p → Within (M := Impl) r p ∧ KidOf (M := Impl) n p
  | 0, _, _, h => nomatch h
  | f + 1, r, p, h => by
    unfold parentBelow at h
    split at h
    · next hk => cases h; exact ⟨Within.root (M := Impl) r, (kidOf_iff n r).2 ((kidTest n r).1 hk)⟩
    · rw [← Array.foldl_toList, foldl_orElse] at h
      change List.findSome? _ _ = some p at h
      obtain ⟨c, hc, hcp⟩ := List.exists_of_findSome?_eq_some h
      have ⟨hw, hk⟩ := parentBelow_sound n f c p hcp
      exact ⟨.kid ((inKids_iff c r).2 hc) hw, hk⟩

/-- The search answers wherever a parent of `n` lies fewer than its fuel steps down. -/
theorem parentBelow_complete (n : Node) {f : Nat} {r p : Node} (h : Reach f r p) (hk : n ∈ (kidsOf p).toList) :
    (parentBelow n f r).isSome = true := by
  induction h with
  | root f r =>
    unfold parentBelow
    rw [if_pos ((kidTest n r).2 hk)]; rfl
  | @kid f r c p hc _ ih =>
    unfold parentBelow
    split
    · rfl
    · rw [← Array.foldl_toList, foldl_orElse]
      exact findSome?_isSome hc (ih hk)

/-! Heights. -/

theorem heightList_le {c : Node} : ∀ {l : List (NtId × Option Node)}, c ∈ l.filterMap Prod.snd →
    c.height ≤ Node.heightList l
  | [], h => nomatch h
  | (_, none) :: r, h => by
    simp only [List.filterMap_cons] at h
    simp only [Node.heightList, Node.heightOpt]
    exact Nat.le_trans (heightList_le h) (Nat.le_max_right _ _)
  | (_, some d) :: r, h => by
    simp only [List.filterMap_cons, List.mem_cons] at h
    simp only [Node.heightList, Node.heightOpt]
    rcases h with rfl | h
    · exact Nat.le_max_left _ _
    · exact Nat.le_trans (heightList_le h) (Nat.le_max_right _ _)

/-- A child is lower than its parent. -/
theorem height_kid {c r : Node} (h : c ∈ (kidsOf r).toList) : c.height < r.height := by
  obtain ⟨k, i, j, p, n, as, ⟨l⟩, t⟩ := r
  have h : c ∈ l.filterMap Prod.snd := by simpa [kidsOf] using h
  simp only [Node.height, Node.heightArr]
  exact Nat.lt_succ_of_le (heightList_le h)

theorem height_pos (r : Node) : ∃ g, r.height = g + 1 := by cases r; exact ⟨_, rfl⟩

/-- Every node within a tree is reached within its height. -/
theorem reach_height : ∀ {r p : Impl.Node}, Within (M := Impl) r p → Reach (Node.height r) r p
  | _, _, .root r => by
    obtain ⟨g, hg⟩ := height_pos r
    rw [hg]; exact .root _ _
  | _, _, .kid (r := r) (c := c) hc hw => by
    have hc' := (inKids_iff c r).1 hc
    have := height_kid hc'
    obtain ⟨g, hg⟩ := height_pos r
    rw [hg]
    exact .kid hc' ((reach_height hw).mono (by omega))

/-- No node within a tree is higher than its root. -/
theorem height_within : ∀ {r p : Impl.Node}, Within (M := Impl) r p → Node.height p ≤ Node.height r
  | _, _, .root r => Nat.le_refl _
  | _, _, .kid (r := r) (c := c) hc hw =>
    Nat.le_trans (height_within hw) (Nat.le_of_lt (height_kid ((inKids_iff c r).1 hc)))

theorem parent_sound (r n p : Node) (h : Impl.nodeParent r n = some p) :
    Within (M := Impl) r p ∧ KidOf (M := Impl) n p := parentBelow_sound n _ r p h

theorem parent_complete (r n p : Node) (hw : Within (M := Impl) r p) (hk : KidOf (M := Impl) n p) :
    (Impl.nodeParent r n).isSome = true :=
  parentBelow_complete n (reach_height hw) ((kidOf_iff n p).1 hk)

/-- The parents from a node within the tree: as many as there are, given fuel past the height left above it. -/
theorem ancestorsBy_stable (r : Node) : ∀ (f g : Nat) (x : Node), Within (M := Impl) r x →
    r.height ≤ f + x.height → r.height ≤ g + x.height →
    ancestorsBy (Engine.parent r) f x = ancestorsBy (Engine.parent r) g x := by
  have step : ∀ x p, Within (M := Impl) r x → Engine.parent r x = some p →
      Within (M := Impl) r p ∧ x.height < p.height := fun x p _ hp =>
    have ⟨hw, hk⟩ := parent_sound r x p hp
    ⟨hw, height_kid ((kidOf_iff x p).1 hk)⟩
  intro f
  induction f with
  | zero =>
    intro g x hx hf _
    cases hp : Engine.parent r x with
    | none => cases g <;> simp [ancestorsBy, hp]
    | some p =>
      have ⟨hw, hl⟩ := step x p hx hp
      have := height_within hw
      omega
  | succ f ih =>
    intro g x hx hf hg
    cases hp : Engine.parent r x with
    | none => cases g <;> simp [ancestorsBy, hp]
    | some p =>
      have ⟨hw, hl⟩ := step x p hx hp
      have := height_within hw
      cases g with
      | zero => omega
      | succ g =>
        simp only [ancestorsBy, hp]
        rw [ih g p hw (by omega) (by omega)]

theorem ancestorsBy_succ (P : Node → Option Node) (f : Nat) (x : Node) :
    ancestorsBy P (f + 1) x = match P x with
      | some p => p :: ancestorsBy P f p
      | none => [] := rfl

theorem ancestors_none (r n : Impl.Node) (hp : Impl.nodeParent r n = none) : Impl.nodeAncestors r n = [] := by
  have hp : Engine.parent r n = none := hp
  show ancestorsBy (Engine.parent r) (Node.height r) n = []
  obtain ⟨g, hg⟩ := height_pos r
  rw [hg, ancestorsBy_succ, hp]

theorem ancestors_some (r n p : Impl.Node) (hp : Impl.nodeParent r n = some p) :
    Impl.nodeAncestors r n = p :: Impl.nodeAncestors r p := by
  have ⟨hw, _⟩ := parent_sound r n p hp
  have hp : Engine.parent r n = some p := hp
  show ancestorsBy (Engine.parent r) (Node.height r) n = p :: ancestorsBy (Engine.parent r) (Node.height r) p
  obtain ⟨g, hg⟩ := height_pos r
  obtain ⟨_, hq⟩ := height_pos p
  rw [hg, ancestorsBy_succ _ g n, hp]
  show p :: ancestorsBy (Engine.parent r) g p = p :: ancestorsBy (Engine.parent r) (g + 1) p
  rw [ancestorsBy_stable r g (g + 1) p hw (by omega) (by omega)]

/-- The engine's Parent meets its laws. -/
theorem parentLaws : Model.ParentLaws Impl where
  sound := parent_sound
  complete := parent_complete
  ancestors r n := by
    split
    · next p h => exact ancestors_some r n p h
    · next h => exact ancestors_none r n h
  height n c h := by
    show Node.height c < Node.height n
    exact height_kid ((inKids_iff c n).1 h)

/-! The accessors (§5.1.2). -/

/-- The occurrences of `nt`: their children are the children whose nonterminal is `nt`. -/
theorem filterMap_slots (nt : NtId) : ∀ kids : List (NtId × Option Node),
    ((kids.filter fun c => slotNt c == nt).map Prod.snd).filterMap id =
      (kids.filterMap Prod.snd).filter (Impl.nodeNt · == nt)
  | [] => rfl
  | (t, none) :: r => by
    have ih := filterMap_slots nt r
    by_cases h : t = nt <;> simp_all [slotNt]
  | (t, some (.mk k i j p n as ks tx)) :: r => by
    have ih := filterMap_slots nt r
    by_cases h : n = nt <;> simp_all [slotNt]

/-- A fold over `attach` whose step reads only the element. -/
theorem foldl_attach_eq {α β : Type} {xs : Array α} {F : β → {x // x ∈ xs} → β} (G : β → α → β)
    (h : ∀ b x, F b x = G b x.1) (b : β) : xs.attach.foldl F b = xs.foldl G b := by
  have : F = fun b x => G b x.1 := funext fun b => funext fun x => h b x
  subst this; exact Array.foldl_attach

theorem descendantsInto_unfold (acc : Array Node) (st lo hi : Nat) (pr : ProdId) (nt : NtId)
    (as : List Grammar.Param) (kids : Array (NtId × Option Node)) (tx : Subarray Nat) :
    descendantsInto acc (.mk st lo hi pr nt as kids tx) =
      kids.foldl (fun a (p : NtId × Option Node) => match p.2 with
        | some c => descendantsInto (a.push c) c
        | none => a) acc := by
  rw [descendantsInto]
  exact foldl_attach_eq _ (fun _ x => by obtain ⟨⟨_, _ | _⟩, _⟩ := x <;> rfl) acc

/-- The descendants of children, from an accumulator: each, then its descendants. -/
theorem descendants_foldl : ∀ (k : Nat) (kids : List (NtId × Option Node)),
    (∀ c ∈ kids.filterMap Prod.snd, c.height ≤ k) →
    ∀ (acc : Array Node),
      (kids.foldl (fun a (p : NtId × Option Node) => match p.2 with
        | some c => descendantsInto (a.push c) c
        | none => a) acc).toList =
      acc.toList ++ (kids.filterMap Prod.snd).flatMap fun c => c :: (descendants c).toList
  | _, [], _, acc => by simp
  | k, (_, none) :: r, hk, acc => by
    simp only [List.filterMap_cons] at hk ⊢
    simpa using descendants_foldl k r hk acc
  | 0, (_, some c) :: _, hk, _ => by
    simp only [List.filterMap_cons, List.mem_cons, forall_eq_or_imp] at hk
    obtain ⟨g, hg⟩ := height_pos c
    omega
  | k + 1, (_, some c) :: r, hk, acc => by
    simp only [List.filterMap_cons, List.mem_cons, forall_eq_or_imp] at hk
    obtain ⟨st, lo, hi, pr, nt, as, ks, tx⟩ := c
    have hsub : ∀ d ∈ ks.toList.filterMap Prod.snd, d.height ≤ k := fun d hd => by
      have hlt := height_kid (r := .mk st lo hi pr nt as ks tx) (by simpa [kidsOf] using hd)
      omega
    simp only [List.foldl_cons, List.filterMap_cons, List.flatMap_cons]
    rw [descendants_foldl (k + 1) r hk.2, descendantsInto_unfold (acc.push _) st lo hi pr nt as ks tx,
      ← Array.foldl_toList, descendants_foldl k ks.toList hsub,
      descendants, descendantsInto_unfold #[] st lo hi pr nt as ks tx,
      ← Array.foldl_toList, descendants_foldl k ks.toList hsub]
    simp [List.append_assoc]

theorem child_kids : ∀ (n : Impl.Node) (nt : NtId), ∃ os : List (Option Impl.Node),
    (∀ k, Impl.nodeChild n nt k = os[k]?) ∧
      os.filterMap id = (seqList (M := Impl) (Impl.nodeKids n)).filter (Impl.nodeNt · == nt)
  | .mk _ _ _ _ _ _ kids _, nt => ⟨((kids.filter fun c => slotNt c == nt).map Prod.snd).toList,
      fun k => (Array.getElem?_toList ..).symm, by
        rw [seqList_eq]
        show (((kids.filter _).map Prod.snd).toList).filterMap id = ((kids.filterMap Prod.snd).toList).filter _
        simpa using filterMap_slots nt kids.toList⟩

theorem descendants_eq : ∀ n : Impl.Node, seqList (M := Impl) (Impl.nodeDescendants n) =
    (seqList (M := Impl) (Impl.nodeKids n)).flatMap fun c => c :: seqList (M := Impl) (Impl.nodeDescendants c)
  | .mk st lo hi pr nt as kids tx => by
    have hk : ∀ c ∈ kids.toList.filterMap Prod.snd, c.height ≤ (Node.mk st lo hi pr nt as kids tx).height :=
      fun c hc => Nat.le_of_lt (height_kid (r := .mk st lo hi pr nt as kids tx) (by simpa [kidsOf] using hc))
    rw [seqList_eq, seqList_eq]
    show (descendants (.mk st lo hi pr nt as kids tx)).toList = _
    rw [descendants, descendantsInto_unfold, ← Array.foldl_toList, descendants_foldl _ kids.toList hk #[]]
    simp only [seqList_eq]
    show _ = List.flatMap _ (Array.filterMap _ kids).toList
    simp only [Array.toList_filterMap]
    rfl

/-- The engine's accessors meet their laws, given the two about its parser and its covered nodes: that a parsed
node's occurrences are its production's (`child_parse`), and a covered node's (`child_cover`; of the engine's
grammar context, `Engine.Impl.child_parse` and `Engine.Impl.child_cover` in `Proofs/Parse/Shape.lean`). -/
theorem nodeLaws_of (G : GrammarCtx)
    (child_parse : ∀ pc st src goal args n d nt k,
      Impl.parse pc st (Impl.seqOfNats src) goal args = some (some n) →
      (d = n ∨ d ∈ seqList (M := Impl) (Impl.nodeDescendants n)) →
      Impl.nodeChild d nt k = (((Grammar.fillOccs (Grammar.occsAt G.gl (Impl.nodeProd d))
        (seqList (M := Impl) (Impl.nodeKids d))).filter (·.1 == nt)).map (·.2))[k]?)
    (child_cover : ∀ pc st c goal args n d nt k,
      Impl.cover pc st c goal args = some n →
      (d = n ∨ d ∈ seqList (M := Impl) (Impl.nodeDescendants n)) →
      Impl.nodeChild d nt k = (((Grammar.fillOccs (Grammar.occsAt G.gl (Impl.nodeProd d))
        (seqList (M := Impl) (Impl.nodeKids d))).filter (·.1 == nt)).map (·.2))[k]?) :
    Model.NodeLaws Impl G where
  child_kids := child_kids
  child_parse := child_parse
  child_cover := child_cover
  descendants := descendants_eq

end Engine.Impl
