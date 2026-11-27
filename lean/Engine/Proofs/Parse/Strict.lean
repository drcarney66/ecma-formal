module

public import Engine.Parse.Strict
public import Engine.Proofs.Parse.Tables
public import Engine.Proofs.Parse.Kernel
public import Engine.Proofs.Parse.Code
public import Ecma.Grammar.StrictCode
public import Ecma.Spec.Program

@[expose] public section

/-!
# Soundness and completeness of `Engine.Parse.Strict.sloppyOk` against `Grammar.NonStrictOk`

Connects `Strict.view Engine.builder d` to `Grammar.Tree.view (Grammar.tokenText src els toks)` over
syntactic derivation trees related by `Model.NodeRel`, proving:
1. `nonStrictOk_of_not_annexB`: when `!cx.annexB.any = true`, `NonStrictOk` holds unconditionally on
   every syntactic derivation tree.
2. `sloppyOk_true_sound`: when `Strict.sloppyOk Engine.builder d strict d [] nd = some true`,
   `NonStrictOk` holds (with no external height hypothesis needed).
3. `sloppyOk_false_sound`: when `Strict.sloppyOk Engine.builder d strict d [] nd = some false` and
   `synHeight t ≤ d`, `¬ NonStrictOk` holds.
-/

namespace Engine.Parse.Strict

open Ecma.Grammar Engine.Parse

private theorem opt_none_or_some {α : Type} (o : Option α) :
    o = none ∨ ∃ x, o = some x :=
  match o with
  | none => Or.inl rfl
  | some x => Or.inr ⟨x, rfl⟩

/-! ## Non-leaf tree height (`synHeight`) and stabilization of `NodeView` walks -/

mutual
/-- Height of a `Tree` counting only non-leaf children (matching `(Tree.view _).kids`). -/
def synHeight : Tree → Nat
  | .node _ _ _ _ _ kids => synHeightKids kids + 1
  | _ => 1

def synHeightKids : List Tree → Nat
  | [] => 0
  | k :: ks => max (if k.isLeaf then 0 else synHeight k) (synHeightKids ks)
end

private theorem le_foldl_max_init (xs : List Nat) (init : Nat) :
    init ≤ xs.foldl max init := by
  induction xs generalizing init with
  | nil => exact Nat.le_refl _
  | cons x xs ih =>
    simp only [List.foldl_cons]
    exact Nat.le_trans (Nat.le_max_left init x) (ih (max init x))

private theorem mem_le_foldl_max {xs : List Nat} {x : Nat} (hx : x ∈ xs) (init : Nat) :
    x ≤ xs.foldl max init := by
  induction xs generalizing init with
  | nil => nomatch hx
  | cons y ys ih =>
    simp only [List.foldl_cons]
    rcases List.mem_cons.mp hx with rfl | hmem
    · exact Nat.le_trans (Nat.le_max_right init x) (le_foldl_max_init ys (max init x))
    · exact ih hmem (max init y)

private theorem list_any_congr {α : Type} {xs : List α} {f g : α → Bool}
    (h : ∀ x ∈ xs, f x = g x) : xs.any f = xs.any g := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.any_cons, h x List.mem_cons_self, ih (fun y hy => h y (List.mem_cons_of_mem _ hy))]

private theorem findSome_congr {α β : Type} {xs : List α} {f g : α → Option β}
    (h : ∀ x ∈ xs, f x = g x) : xs.findSome? f = xs.findSome? g := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.findSome?_cons, h x List.mem_cons_self]
    cases g x with
    | some _ => rfl
    | none => exact ih fun y hy => h y (List.mem_cons_of_mem _ hy)

theorem synHeight_pos (t : Tree) : 1 ≤ synHeight t := by
  cases t <;> simp [synHeight]

private theorem mem_le_synHeightKids {kids : List Tree} {c : Tree}
    (hc : c ∈ kids) (hnl : c.isLeaf = false) :
    synHeight c ≤ synHeightKids kids := by
  induction kids with
  | nil => nomatch hc
  | cons k ks ih =>
    rw [synHeightKids]
    rcases List.mem_cons.mp hc with rfl | hmem
    · simp only [hnl, Bool.false_eq_true, ↓reduceIte]
      exact Nat.le_max_left _ _
    · exact Nat.le_trans (ih hmem) (Nat.le_max_right _ _)

theorem synHeight_child_lt {nt : NT} {id : Nat} {ps : List Param} {i j : Nat} {kids : List Tree}
    {c : Tree} (hc : c ∈ kids.filter fun x => !x.isLeaf) :
    synHeight c < synHeight (.node nt id ps i j kids) := by
  obtain ⟨hmem, hnlB⟩ := List.mem_filter.mp hc
  have hnl : c.isLeaf = false := Bool.eq_false_iff.mpr (fun h => by rw [h] at hnlB; cases hnlB)
  have hle := mem_le_synHeightKids hmem hnl
  rw [synHeight]
  omega

theorem synHeightKids_le_of_all {kids : List Tree} {b : Nat}
    (hall : ∀ c ∈ kids.filter (fun x => !x.isLeaf), synHeight c ≤ b) :
    synHeightKids kids ≤ b := by
  induction kids with
  | nil => rw [synHeightKids]; exact Nat.zero_le _
  | cons k ks ih =>
    rw [synHeightKids]
    apply Nat.max_le.mpr
    refine ⟨?_, ih (fun c hc => hall c ?_)⟩
    · cases hl : k.isLeaf with
      | true => simp
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte]
        exact hall k (List.mem_filter.mpr ⟨List.mem_cons_self, by simp [hl]⟩)
    · obtain ⟨hm, hnl⟩ := List.mem_filter.mp hc
      exact List.mem_filter.mpr ⟨List.mem_cons_of_mem _ hm, hnl⟩

private theorem treeSize_mem_lt {c : Tree} :
    ∀ {kids : List Tree}, c ∈ kids → treeSize c ≤ treeSize.treeListSize kids
  | [], h => nomatch h
  | k :: ks, h => by
    dsimp only [treeSize.treeListSize]
    rcases List.mem_cons.mp h with rfl | hm
    · omega
    · have := treeSize_mem_lt hm; omega

theorem synHeight_le_height (t : Tree) : synHeight t ≤ t.height := by
  have hgen : ∀ (sz : Nat) (u : Tree), treeSize u ≤ sz → synHeight u ≤ u.height := by
    intro sz
    induction sz using Nat.strongRecOn with
    | ind sz ih =>
      intro u hsz
      cases u with
      | leaf _ _ => simp [synHeight, Tree.height]
      | lex _ _ => simp [synHeight, Tree.height]
      | node nt id ps i j kids =>
        dsimp only [treeSize] at hsz
        rw [synHeight, Tree.height]
        apply Nat.succ_le_succ
        apply synHeightKids_le_of_all
        intro c hc
        have hcMem := (List.mem_filter.mp hc).1
        have hcSz := treeSize_mem_lt hcMem
        have hcLe := ih (treeSize c) (by omega) c (Nat.le_refl _)
        have hmemH : c.height ∈ kids.attach.map (fun ⟨k, _⟩ => k.height) := by
          rw [List.mem_map]
          exact ⟨⟨c, hcMem⟩, List.mem_attach _ _, rfl⟩
        exact Nat.le_trans hcLe (mem_le_foldl_max hmemH 0)
  exact hgen (treeSize t) t (Nat.le_refl _)

theorem oneNode_tree_stab (text : Nat → Nat → List Nat) (m : NT) (sp : Nat × Nat)
    (t : Tree) {d1 d2 : Nat} (h1 : synHeight t ≤ d1) (h2 : synHeight t ≤ d2) :
    oneNode (Tree.view text) m sp d1 t = oneNode (Tree.view text) m sp d2 t := by
  have hgen : ∀ (sz : Nat) (u : Tree) {k1 k2 : Nat},
      treeSize u ≤ sz → synHeight u ≤ k1 → synHeight u ≤ k2 →
      oneNode (Tree.view text) m sp k1 u = oneNode (Tree.view text) m sp k2 u := by
    intro sz
    induction sz using Nat.strongRecOn with
    | ind sz ih =>
      intro u a1 a2 hsz ha1 ha2
      have p1 := synHeight_pos u
      obtain ⟨b1, rfl⟩ : ∃ b1, a1 = b1 + 1 := ⟨a1 - 1, by omega⟩
      obtain ⟨b2, rfl⟩ : ∃ b2, a2 = b2 + 1 := ⟨a2 - 1, by omega⟩
      cases u with
      | leaf _ _ => simp [oneNode, Tree.view]
      | lex _ _ => simp [oneNode, Tree.view]
      | node nt id ps i j kids =>
        dsimp only [treeSize] at hsz
        simp only [oneNode, Tree.view]
        congr 1; congr 1
        apply list_any_congr
        intro c hc
        have hlt := synHeight_child_lt (nt := nt) (id := id) (ps := ps) (i := i) (j := j) hc
        have hcSz := treeSize_mem_lt (List.mem_filter.mp hc).1
        exact ih (treeSize c) (by omega) c (Nat.le_refl _) (by omega) (by omega)
  exact hgen (treeSize t) t (Nat.le_refl _) h1 h2

private theorem directive_tree_stab (text : Nat → Nat → List Nat) (item : Tree) {d1 d2 : Nat}
    (h1 : synHeight item ≤ d1 + 1) (h2 : synHeight item ≤ d2 + 1) :
    directive (Tree.view text) d1 item = directive (Tree.view text) d2 item := by
  unfold directive
  cases item with
  | leaf _ _ | lex _ _ => rfl
  | node nt id ps i j kids =>
    have h1' : synHeight (.node nt id ps i j kids) ≤ d1 + 1 := h1
    have h2' : synHeight (.node nt id ps i j kids) ≤ d2 + 1 := h2
    have hkv1 : (Tree.view text).kids (.node nt id ps i j kids) = kids.filter (fun x => !x.isLeaf) := rfl
    rw [hkv1]
    cases hk1 : kids.filter (fun x => !x.isLeaf) with
    | nil => rfl
    | cons s rest1 =>
      cases rest1 with
      | cons _ _ => rfl
      | nil =>
        have hsLt : synHeight s < synHeight (.node nt id ps i j kids) :=
          synHeight_child_lt (by rw [hk1]; exact List.mem_cons_self)
        dsimp only
        cases hSt : (Tree.view text).isA s .Statement with
        | false => rfl
        | true =>
          simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
          cases s with
          | leaf _ _ | lex _ _ => rfl
          | node ntS idS psS iS jS kidsS =>
            have hkv2 : (Tree.view text).kids (.node ntS idS psS iS jS kidsS) = kidsS.filter (fun x => !x.isLeaf) := rfl
            rw [hkv2]
            cases hk2 : kidsS.filter (fun x => !x.isLeaf) with
            | nil => rfl
            | cons es rest2 =>
              cases rest2 with
              | cons _ _ => rfl
              | nil =>
                have hesLt : synHeight es < synHeight (.node ntS idS psS iS jS kidsS) :=
                  synHeight_child_lt (by rw [hk2]; exact List.mem_cons_self)
                dsimp only
                cases hEs : (Tree.view text).isA es .ExpressionStatement with
                | false => rfl
                | true =>
                  simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
                  cases es with
                  | leaf _ _ | lex _ _ => rfl
                  | node ntE idE psE iE jE kidsE =>
                    have hkv3 : (Tree.view text).kids (.node ntE idE psE iE jE kidsE) = kidsE.filter (fun x => !x.isLeaf) := rfl
                    rw [hkv3]
                    cases hk3 : kidsE.filter (fun x => !x.isLeaf) with
                    | nil => rfl
                    | cons e rest3 =>
                      cases rest3 with
                      | cons _ _ => rfl
                      | nil =>
                        have heLt : synHeight e < synHeight (.node ntE idE psE iE jE kidsE) :=
                          synHeight_child_lt (by rw [hk3]; exact List.mem_cons_self)
                        dsimp only
                        have he1 : synHeight e ≤ d1 := by omega
                        have he2 : synHeight e ≤ d2 := by omega
                        rw [oneNode_tree_stab text .StringLiteral ((Tree.view text).span e) e he1 he2]

theorem prologueScan_tree_stab (text : Nat → Nat → List Nat) (t : Tree) {d1 d2 : Nat}
    (h1 : synHeight t ≤ d1) (h2 : synHeight t ≤ d2) :
    prologueScan (Tree.view text) d1 t = prologueScan (Tree.view text) d2 t := by
  have hgen : ∀ (sz : Nat) (u : Tree) {a1 a2 : Nat},
      treeSize u ≤ sz → synHeight u ≤ a1 → synHeight u ≤ a2 →
      prologueScan (Tree.view text) a1 u = prologueScan (Tree.view text) a2 u := by
    intro sz
    induction sz using Nat.strongRecOn with
    | ind sz ih =>
      intro u a1 a2 hsz ha1 ha2
      have p1 := synHeight_pos u
      obtain ⟨k1, rfl⟩ : ∃ k1, a1 = k1 + 1 := ⟨a1 - 1, by omega⟩
      obtain ⟨k2, rfl⟩ : ∃ k2, a2 = k2 + 1 := ⟨a2 - 1, by omega⟩
      unfold prologueScan
      cases hA : (Tree.view text).isA u .StatementListItem with
      | true =>
        simp only [↓reduceIte]
        rw [directive_tree_stab text u ha1 ha2]
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte]
        cases u with
        | leaf _ _ | lex _ _ => rfl
        | node nt id ps i j kids =>
          dsimp only [treeSize] at hsz
          dsimp only [Tree.view]
          apply findSome_congr
          intro c hc
          have hlt := synHeight_child_lt (nt := nt) (id := id) (ps := ps) (i := i) (j := j) hc
          have hcSz := treeSize_mem_lt (List.mem_filter.mp hc).1
          exact ih (treeSize c) (by omega) c (Nat.le_refl _) (by omega) (by omega)
  exact hgen (treeSize t) t (Nat.le_refl _) h1 h2

theorem bodyOf_tree_stab_and_le (text : Nat → Nat → List Nat) (t : Tree) {d1 d2 : Nat}
    (h1 : synHeight t ≤ d1) (h2 : synHeight t ≤ d2) :
    bodyOf (Tree.view text) d1 t = bodyOf (Tree.view text) d2 t ∧
    ∀ b, bodyOf (Tree.view text) d1 t = some b → synHeight b ≤ synHeight t := by
  have hgen : ∀ (sz : Nat) (u : Tree) {a1 a2 : Nat},
      treeSize u ≤ sz → synHeight u ≤ a1 → synHeight u ≤ a2 →
      bodyOf (Tree.view text) a1 u = bodyOf (Tree.view text) a2 u ∧
      ∀ b, bodyOf (Tree.view text) a1 u = some b → synHeight b ≤ synHeight u := by
    intro sz
    induction sz using Nat.strongRecOn with
    | ind sz ih =>
      intro u a1 a2 hsz ha1 ha2
      have p1 := synHeight_pos u
      obtain ⟨k1, rfl⟩ : ∃ k1, a1 = k1 + 1 := ⟨a1 - 1, by omega⟩
      obtain ⟨k2, rfl⟩ : ∃ k2, a2 = k2 + 1 := ⟨a2 - 1, by omega⟩
      unfold bodyOf
      cases hF : (Tree.view text).isA u .FunctionBody with
      | true =>
        simp only [↓reduceIte]
        exact ⟨trivial, fun b hb => by injection hb with hbEq; subst hbEq; exact Nat.le_refl _⟩
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte]
        cases u with
        | leaf _ _ | lex _ _ => exact ⟨rfl, fun _ hb => by cases hb⟩
        | node nt id ps i j kids =>
          dsimp only [treeSize] at hsz
          have hkv : (Tree.view text).kids (.node nt id ps i j kids) = kids.filter (fun x => !x.isLeaf) := rfl
          rw [hkv]
          have hcongr : List.findSome? (fun k => if (Tree.view text).isIn bodyPath k then bodyOf (Tree.view text) k1 k else none)
              (kids.filter fun x => !x.isLeaf) =
            List.findSome? (fun k => if (Tree.view text).isIn bodyPath k then bodyOf (Tree.view text) k2 k else none)
              (kids.filter fun x => !x.isLeaf) := by
            apply findSome_congr
            intro c hc
            cases hIn : (Tree.view text).isIn bodyPath c with
            | true =>
              simp only [↓reduceIte]
              have hlt := synHeight_child_lt (nt := nt) (id := id) (ps := ps) (i := i) (j := j) hc
              have hcSz := treeSize_mem_lt (List.mem_filter.mp hc).1
              exact (ih (treeSize c) (by omega) c (Nat.le_refl _) (by omega) (by omega)).1
            | false => rfl
          refine ⟨hcongr, fun b hb => ?_⟩
          obtain ⟨c, hc, hcb⟩ := List.exists_of_findSome?_eq_some hb
          cases hIn : (Tree.view text).isIn bodyPath c with
          | true =>
            simp only [hIn, ↓reduceIte] at hcb
            have hlt := synHeight_child_lt (nt := nt) (id := id) (ps := ps) (i := i) (j := j) hc
            have hcSz := treeSize_mem_lt (List.mem_filter.mp hc).1
            have hleB := (ih (treeSize c) (by omega) c (a1 := k1) (a2 := k1) (Nat.le_refl _) (by omega) (by omega)).2 b hcb
            omega
          | false =>
            simp only [hIn, Bool.false_eq_true, ↓reduceIte] at hcb
            cases hcb
  exact hgen (treeSize t) t (Nat.le_refl _) h1 h2

/-! ## Positive syntactic step (`PosSynStep`) and `!cx.annexB.any → NonStrictOk` -/

private theorem excluded_mono {α : Type} {A : Alphabet α} {inp : List α} {s : Src} {k : Nat}
    {ps : List Param} {i j : Nat} {ex : Exclusion}
    {neg1 neg2 : NT → List Param → Nat → Nat → Prop}
    (himp : ∀ n ps i j, neg2 n ps i j → neg1 n ps i j)
    (hex : Excluded A neg2 inp s k ps i j ex) : Excluded A neg1 inp s k ps i j ex := by
  cases ex with
  | sym y => cases y with | t _ => exact hex | nt _ _ => exact himp _ _ _ _ hex
  | oneOf ys _ =>
    obtain ⟨y, hy, hsy⟩ := hex
    refine ⟨y, hy, ?_⟩
    cases y with | t _ => exact hsy | nt _ _ => exact himp _ _ _ _ hsy

private theorem lookOk_antitone {α : Type} {A : Alphabet α} {inp : List α} {s : Src}
    {lk : Lookahead} {i : Nat}
    {neg1 neg2 : NT → List Param → Nat → Nat → Prop}
    (himp : ∀ n ps i j, neg2 n ps i j → neg1 n ps i j)
    (hlk : LookOk A neg1 inp s lk i) : LookOk A neg2 inp s lk i := by
  cases lk with
  | eq _ | ne _ | mem _ | notMem _ => exact hlk
  | notMemNT _ => exact fun ⟨h, hn2⟩ => hlk ⟨h, himp _ _ _ _ hn2⟩

theorem step_antitone_neg {α : Type} {A : Alphabet α} {inp : List α} {gl : GL} {cx : Ctx} {g : GrammarId}
    {neg1 neg2 : NT → List Param → Nat → Nat → Prop}
    (himp : ∀ n ps i j, neg2 n ps i j → neg1 n ps i j) :
    ∀ (sz : Nat),
      (∀ {n ps i j t}, treeSize t ≤ sz → Step A neg1 inp gl cx g n ps i j t → Step A neg2 inp gl cx g n ps i j t) ∧
      (∀ {s ps k is i j m ts}, treeSize.treeListSize ts ≤ sz →
        Ecma.Grammar.Seq A neg1 inp gl cx g s ps k is i j m ts →
        Ecma.Grammar.Seq A neg2 inp gl cx g s ps k is i j m ts) := by
  intro sz
  induction sz using Nat.strongRecOn with
  | ind sz ih =>
    have hst : ∀ {n ps i j t}, treeSize t ≤ sz →
        Step A neg1 inp gl cx g n ps i j t → Step A neg2 inp gl cx g n ps i j t := by
      intro n ps i j t hsz hs
      cases hs with
      | lex ha hg hl => exact .lex ha hg hl
      | node s hsMem hgrd hpid hseq =>
        dsimp only [treeSize] at hsz
        exact .node s hsMem hgrd hpid ((ih _ (by omega)).2 (Nat.le_refl _) hseq)
    refine ⟨hst, ?_⟩
    intro s ps k is
    induction is generalizing k with
    | nil => intro _ _ _ _ _ hs; cases hs; exact .nil
    | cons _ _ ihr =>
      intro i j m ts hsz hs
      cases hs with
      | absent hr => exact .absent (ihr hsz hr)
      | term ht hr =>
        dsimp only [treeSize.treeListSize, treeSize] at hsz
        exact .term ht (ihr (by omega) hr)
      | nt hs0 hcd hr =>
        dsimp only [treeSize.treeListSize] at hsz
        exact .nt (hst (by omega) hs0) hcd (ihr (by omega) hr)
      | butNotT ht hne hr =>
        dsimp only [treeSize.treeListSize, treeSize] at hsz
        exact .butNotT ht (fun hex => hne (excluded_mono himp hex)) (ihr (by omega) hr)
      | butNotN hs0 hne hr =>
        dsimp only [treeSize.treeListSize] at hsz
        exact .butNotN (hst (by omega) hs0) (fun hex => hne (excluded_mono himp hex)) (ihr (by omega) hr)
      | phrase hp hr =>
        dsimp only [treeSize.treeListSize, treeSize] at hsz
        exact .phrase hp (ihr (by omega) hr)
      | look hlk hr => exact .look (lookOk_antitone himp hlk) (ihr hsz hr)
      | noLT hn hr => exact .noLT hn (ihr hsz hr)
      | empty hr => exact .empty (ihr hsz hr)
      | onlyIf hr => exact .onlyIf (ihr hsz hr)

abbrev PosSynStep (cx : Ctx) (P : CodePrims) (toks : List Token) :
    NT → List Param → Nat → Nat → Tree → Prop :=
  Step (tokenAlphabet Ecma.Spec.gl cx P) (fun _ _ _ _ => False) toks Ecma.Spec.gl cx .syntactic

abbrev PosSynSeq (cx : Ctx) (P : CodePrims) (toks : List Token) :
    Src → List Param → Nat → List Item → Nat → Nat → List Bool → List Tree → Prop :=
  Ecma.Grammar.Seq (tokenAlphabet Ecma.Spec.gl cx P) (fun _ _ _ _ => False) toks Ecma.Spec.gl cx .syntactic

theorem posSynStep_of_derives {cx : Ctx} {P : CodePrims} {toks : List Token}
    {n : NT} {ps : List Param} {i j : Nat} {t : Tree}
    (hd : Derives Ecma.Spec.gl cx .syntactic (tokenAlphabet Ecma.Spec.gl cx P) toks n ps i j t) :
    PosSynStep cx P toks n ps i j t := by
  obtain ⟨K, hK⟩ := hd
  have hs := hK (max K 1) (Nat.le_max_left K 1)
  obtain ⟨k0, hk0⟩ : ∃ k0, max K 1 = k0 + 1 := ⟨max K 1 - 1, by omega⟩
  rw [hk0] at hs
  exact (step_antitone_neg (fun _ _ _ _ f => nomatch f) (treeSize t)).1 (Nat.le_refl _) hs

private theorem syn_step_le_mutual {cx : Ctx} {P : CodePrims} {toks : List Token} :
    ∀ (sz : Nat),
      (∀ {n ps i j t}, treeSize t ≤ sz → PosSynStep cx P toks n ps i j t → i ≤ j) ∧
      (∀ {s ps k is i j m ts}, treeSize.treeListSize ts ≤ sz → PosSynSeq cx P toks s ps k is i j m ts → i ≤ j) := by
  intro sz
  induction sz using Nat.strongRecOn with
  | ind sz ih =>
    have hst : ∀ {n ps i j t}, treeSize t ≤ sz → PosSynStep cx P toks n ps i j t → i ≤ j := by
      intro n ps i j t hsz hs
      cases hs with
      | lex _ _ _ => omega
      | node s _ _ _ hseq =>
        dsimp only [treeSize] at hsz
        exact (ih _ (by omega)).2 (Nat.le_refl _) hseq
    refine ⟨hst, ?_⟩
    intro s ps k is
    induction is generalizing k with
    | nil => intro _ _ _ _ _ hs; cases hs; exact Nat.le_refl _
    | cons _ _ ihr =>
      intro i j m ts hsz hs
      cases hs with
      | absent hr | look _ hr | noLT _ hr | empty hr | onlyIf hr => exact ihr hsz hr
      | @term _ _ _ x _ _ _ h _ _ _ ht hr =>
        dsimp only [treeSize.treeListSize, treeSize] at hsz
        have hih : i < h := by
          dsimp only [tokenAlphabet] at ht
          cases x with
          | cp _ => cases ht
          | text _ _ =>
            cases hsc : slice toks i h with
            | nil => rw [hsc] at ht; cases ht
            | cons _ _ => exact (slice_nonempty_lt (by rw [hsc]; exact List.cons_ne_nil _ _)).1
        have hhj := ihr (by omega) hr
        omega
      | @butNotT _ _ _ x _ _ _ h _ _ _ ht _ hr =>
        dsimp only [treeSize.treeListSize, treeSize] at hsz
        have hih : i < h := by
          dsimp only [tokenAlphabet] at ht
          cases x with
          | cp _ => cases ht
          | text _ _ =>
            cases hsc : slice toks i h with
            | nil => rw [hsc] at ht; cases ht
            | cons _ _ => exact (slice_nonempty_lt (by rw [hsc]; exact List.cons_ne_nil _ _)).1
        have hhj := ihr (by omega) hr
        omega
      | nt hs0 _ hr | butNotN hs0 _ hr =>
        dsimp only [treeSize.treeListSize] at hsz
        exact Nat.le_trans (hst (by omega) hs0) (ihr (by omega) hr)
      | phrase hp _ => cases hp

theorem posSynStep_le {cx : Ctx} {P : CodePrims} {toks : List Token}
    {n : NT} {ps : List Param} {i j : Nat} {t : Tree}
    (hs : PosSynStep cx P toks n ps i j t) : i ≤ j :=
  (syn_step_le_mutual (treeSize t)).1 (Nat.le_refl _) hs

theorem posSynSeq_le {cx : Ctx} {P : CodePrims} {toks : List Token}
    {s : Src} {ps : List Param} {k : Nat} {is : List Item} {i j : Nat} {m : List Bool} {ts : List Tree}
    (hs : PosSynSeq cx P toks s ps k is i j m ts) : i ≤ j :=
  (syn_step_le_mutual (treeSize.treeListSize ts)).2 (Nat.le_refl _) hs

theorem posSynSeq_child_step {cx : Ctx} {P : CodePrims} {toks : List Token}
    {s : Src} {ps : List Param} {k : Nat} {is : List Item} {i j : Nat} {m : List Bool} {ts : List Tree}
    (hj : j ≤ toks.length)
    (hseq : PosSynSeq cx P toks s ps k is i j m ts) :
    ∀ c ∈ ts.filter (fun x => !x.isLeaf),
      ∃ m' ps' a b, i ≤ a ∧ a ≤ b ∧ b ≤ j ∧ b ≤ toks.length ∧ PosSynStep cx P toks m' ps' a b c := by
  induction is generalizing k i m ts with
  | nil => intro c hc; cases hseq; simp at hc
  | cons _ _ ih =>
    cases hseq with
    | absent hr | look _ hr | noLT _ hr | empty hr | onlyIf hr => exact ih hr
    | @term _ _ _ x _ _ _ h _ _ _ ht hr =>
      intro c hc
      simp only [List.filter_cons, Tree.isLeaf, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hc
      obtain ⟨m', ps', a, b, hha, hab, hbj, hbL, hst⟩ := ih hr c hc
      have hih : i ≤ h := by
        dsimp only [tokenAlphabet] at ht
        cases x with
        | cp _ => cases ht
        | text _ _ =>
          cases hsc : slice toks i h with
          | nil => rw [hsc] at ht; cases ht
          | cons _ _ => exact Nat.le_of_lt (slice_nonempty_lt (by rw [hsc]; exact List.cons_ne_nil _ _)).1
      exact ⟨m', ps', a, b, Nat.le_trans hih hha, hab, hbj, hbL, hst⟩
    | @butNotT _ _ _ x _ _ _ h _ _ _ ht _ hr =>
      intro c hc
      simp only [List.filter_cons, Tree.isLeaf, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hc
      obtain ⟨m', ps', a, b, hha, hab, hbj, hbL, hst⟩ := ih hr c hc
      have hih : i ≤ h := by
        dsimp only [tokenAlphabet] at ht
        cases x with
        | cp _ => cases ht
        | text _ _ =>
          cases hsc : slice toks i h with
          | nil => rw [hsc] at ht; cases ht
          | cons _ _ => exact Nat.le_of_lt (slice_nonempty_lt (by rw [hsc]; exact List.cons_ne_nil _ _)).1
      exact ⟨m', ps', a, b, Nat.le_trans hih hha, hab, hbj, hbL, hst⟩
    | phrase hp _ => cases hp
    | @nt _ _ _ m0 args0 _ _ _ h _ _ t0 _ hs0 _ hr =>
      have hih := posSynStep_le hs0
      have hhj := posSynSeq_le hr
      intro c hc
      rw [List.filter_cons] at hc
      by_cases hnl : (!t0.isLeaf) = true
      · simp only [hnl, ↓reduceIte, List.mem_cons] at hc
        rcases hc with rfl | hrest
        · exact ⟨m0, applyArgs ps args0, i, h, Nat.le_refl _, hih, hhj, by omega, hs0⟩
        · obtain ⟨m', ps', a, b, hha, hab, hbj, hbL, hst⟩ := ih hr c hrest
          exact ⟨m', ps', a, b, Nat.le_trans hih hha, hab, hbj, hbL, hst⟩
      · simp only [hnl, Bool.false_eq_true, ↓reduceIte] at hc
        obtain ⟨m', ps', a, b, hha, hab, hbj, hbL, hst⟩ := ih hr c hc
        exact ⟨m', ps', a, b, Nat.le_trans hih hha, hab, hbj, hbL, hst⟩
    | @butNotN _ _ _ m0 args0 _ _ _ h _ _ t0 _ hs0 _ hr =>
      have hih := posSynStep_le hs0
      have hhj := posSynSeq_le hr
      intro c hc
      rw [List.filter_cons] at hc
      by_cases hnl : (!t0.isLeaf) = true
      · simp only [hnl, ↓reduceIte, List.mem_cons] at hc
        rcases hc with rfl | hrest
        · exact ⟨m0, applyArgs ps args0, i, h, Nat.le_refl _, hih, hhj, by omega, hs0⟩
        · obtain ⟨m', ps', a, b, hha, hab, hbj, hbL, hst⟩ := ih hr c hrest
          exact ⟨m', ps', a, b, Nat.le_trans hih hha, hab, hbj, hbL, hst⟩
      · simp only [hnl, Bool.false_eq_true, ↓reduceIte] at hc
        obtain ⟨m', ps', a, b, hha, hab, hbj, hbL, hst⟩ := ih hr c hc
        exact ⟨m', ps', a, b, Nat.le_trans hih hha, hab, hbj, hbL, hst⟩

private theorem seq_masks_syn {cx : Ctx} {P : CodePrims} {toks : List Token} {s : Src} :
    ∀ {ps : List Param} {k : Nat} {is : List Item} {a b : Nat} {m : List Bool} {ts : List Tree},
      PosSynSeq cx P toks s ps k is a b m ts →
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

private theorem zipIdx_getElem? {α : Type} {xs : List α} {a : α} {idx : Nat}
    (h : (a, idx) ∈ xs.zipIdx) : xs[idx]? = some a := by
  have hgen : ∀ (l : List α) (k : Nat), (a, idx) ∈ l.zipIdx k → k ≤ idx ∧ l[idx - k]? = some a := by
    intro l; induction l with
    | nil => intro _ hm; nomatch hm
    | cons hd tl ihl =>
      intro k hm
      rcases List.mem_cons.mp hm with heq | htl
      · injection heq with ha hi; subst ha; subst hi; simp
      · obtain ⟨hle, hg⟩ := ihl (k + 1) htl
        refine ⟨by omega, ?_⟩
        have hdIdx : idx - k = (idx - (k + 1)) + 1 := by omega
        rw [hdIdx, List.getElem?_cons_succ]; exact hg
  simpa using (hgen xs 0 h).2

private theorem not_sloppy_of_not_annexB (hok : parseTablesOk = true) {cx : Ctx}
    (hnoB : (!cx.annexB.any) = true) {n : NT} {s : Src} {m : List Bool} {id : Nat}
    (hs : s ∈ Ecma.Spec.gl.alts cx .syntactic n)
    (hm : m ∈ masks s.alt.opts)
    (hpid : Ecma.Spec.gl.prodId s m = some id) :
    id ∉ Ecma.Spec.gl.sloppyIds := by
  obtain ⟨_, id', P, hid', hpo, hgEq, _, _, _, _⟩ := prodIdOf_spec hok hs hm
  have hidEq : id' = id := Option.some.inj (hid'.symm.trans hpid)
  subst id'
  have hsPin : s ∈ Ecma.Spec.gl.pinned .syntactic n := by
    unfold GL.alts GL.overlays at hs
    simpa [hnoB] using hs
  have hsGram : s.grammar = .syntactic := by
    unfold GL.pinned at hsPin
    rcases opt_none_or_some ((Ecma.Spec.gl.rulesOf .syntactic).find? (·.lhs == n)) with hnone | ⟨r, hr⟩
    · rw [hnone] at hsPin; simp [baseGrammar] at hsPin
    · rw [hr] at hsPin
      unfold srcsOf at hsPin
      rw [List.mem_map] at hsPin
      obtain ⟨⟨_, _⟩, _, rfl⟩ := hsPin; rfl
  intro hslop
  unfold GL.sloppyIds at hslop
  rw [List.mem_filterMap] at hslop
  obtain ⟨⟨o, idx⟩, hmemZ, hbind⟩ := hslop
  have hget : Ecma.Spec.gl.byId.toList[idx]? = some o := zipIdx_getElem? hmemZ
  cases o with
  | none => cases hbind
  | some P' =>
    dsimp only [Option.bind] at hbind
    split at hbind
    · next hif =>
      injection hbind with hidxEq
      subst idx
      rw [prodOf_eq, ← Array.getElem?_toList, hget] at hpo
      injection hpo with hPP
      subst hPP
      simp only [Bool.and_eq_true, beq_iff_eq] at hif
      rw [hgEq, hsGram] at hif
      cases hif.1
    · cases hbind

private theorem nonStrictOk_all_iff {L : GL} {strict : List Tree → Tree → Prop} {up : List Tree} :
    ∀ ks : List Tree, NonStrictOk.all L strict up ks ↔ ∀ k ∈ ks, NonStrictOk L strict up k
  | [] => by simp [NonStrictOk.all]
  | d :: ds => by simp only [NonStrictOk.all, nonStrictOk_all_iff ds, List.mem_cons, forall_eq_or_imp]

theorem nonStrictOk_of_not_annexB (hok : parseTablesOk = true) {cx : Ctx} {P : CodePrims}
    {toks : List Token} (hnoB : (!cx.annexB.any) = true)
    (strict : List Tree → Tree → Prop)
    (t : Tree) (up : List Tree) {n : NT} {ps : List Param} {a b : Nat}
    (hb : b ≤ toks.length)
    (hs : PosSynStep cx P toks n ps a b t) :
    NonStrictOk Ecma.Spec.gl strict up t := by
  have hgen : ∀ (sz : Nat) (u : Tree) (anc : List Tree) {m : NT} {qs : List Param} {i j : Nat},
      treeSize u ≤ sz → j ≤ toks.length → PosSynStep cx P toks m qs i j u →
      NonStrictOk Ecma.Spec.gl strict anc u := by
    intro sz
    induction sz using Nat.strongRecOn with
    | ind sz ih =>
      intro u anc m qs i j hsz hj hsu
      cases u with
      | leaf _ _ | lex _ _ => trivial
      | node nt id ps0 i0 j0 kids =>
        dsimp only [treeSize] at hsz
        cases hsu with
        | node s hsMem _ hpid hseq =>
          obtain ⟨_, hopts⟩ := alt_lhs_and_opts hok hsMem
          have hm := hopts ▸ seq_masks_syn hseq
          have hnotSlop := not_sloppy_of_not_annexB hok hnoB hsMem hm hpid
          have hchildSteps := posSynSeq_child_step hj hseq
          unfold NonStrictOk
          refine ⟨fun hsl => absurd hsl hnotSlop, (nonStrictOk_all_iff _).mpr ?_⟩
          intro c hc
          cases hl : c.isLeaf with
          | true => cases c <;> simp [Tree.isLeaf, NonStrictOk] at hl ⊢
          | false =>
            have hcFilt : c ∈ kids.filter (fun x => !x.isLeaf) := List.mem_filter.mpr ⟨hc, by simp [hl]⟩
            obtain ⟨m', ps', a', b', _, _, _, hb'L, hst'⟩ := hchildSteps c hcFilt
            have hcSz := treeSize_mem_lt hc
            exact ih (treeSize c) (by omega) c (.node m id qs i j kids :: anc) (Nat.le_refl _) hb'L hst'
  exact hgen (treeSize t) t up (Nat.le_refl _) hb hs

/-! ## Syntactic rules, virtual semicolons, and `Expression` unit-chain dichotomy -/

private theorem syn_rules_and_blocks_nonempty :
    (((glData.rulesOf .syntactic).all fun r => !(writtenAlts r).isEmpty) &&
     (glData.blocks.all fun b => b.rules.all fun r => !(writtenAlts r).isEmpty)) = true := by
  decide

theorem hasRule_syntactic_eq (hok : parseTablesOk = true) (cx : Ctx) (m : NT) :
    hasRule .syntactic m.ctorIdx = !(Ecma.Spec.gl.alts cx .syntactic m).isEmpty := by
  apply Bool.eq_iff_iff.mpr
  rw [hasRule_iff hok .syntactic m.ctorIdx]
  constructor
  · rintro ⟨lhs, hidx, hmem⟩
    have hlhs : lhs = m := nt_ctorIdx_inj hidx
    subst lhs
    rw [List.any_eq_true] at hmem
    obtain ⟨r, hrMem, hrEq⟩ := hmem
    rw [beq_iff_eq] at hrEq; subst hrEq
    have ⟨hSyn, hBlk⟩ := Bool.and_eq_true_iff.mp syn_rules_and_blocks_nonempty
    rw [← glData_eq]
    have hpinNe : glData.pinned .syntactic r.lhs ≠ [] := by
      unfold GL.pinned
      rcases opt_none_or_some ((glData.rulesOf .syntactic).find? (·.lhs == r.lhs)) with hnone | ⟨r', hr'⟩
      · exfalso
        have := List.find?_eq_none.mp hnone r hrMem
        simp at this
      · rw [hr']
        have hr'Mem := List.mem_of_find?_eq_some hr'
        have hw := List.all_eq_true.mp hSyn r' hr'Mem
        unfold srcsOf
        dsimp only
        cases hwa : writtenAlts r' with
        | nil => rw [hwa] at hw; cases hw
        | cons _ _ => intro h; cases h
    have hov : ∀ (bs : List (Block × OverlayMode)) (acc : List Src),
        (∀ pm ∈ bs, pm.1 ∈ glData.blocks) →
        acc ≠ [] →
        bs.foldl (fun a (b, md) =>
          match b.rules.find? (·.lhs == r.lhs), md with
          | none, _ => a
          | some rB, .extend => a ++ (srcsOf .annexB rB).filter fun s => !a.any (·.alt == s.alt)
          | some rB, .replace => srcsOf .annexB rB) acc ≠ [] := by
      intro bs
      induction bs with
      | nil => intro acc _ hacc; exact hacc
      | cons hd tl ih =>
        rcases hd with ⟨b, md⟩
        intro acc hbs hacc
        have hbMem := hbs (b, md) List.mem_cons_self
        have hbs' := fun pm hpm => hbs pm (List.mem_cons_of_mem _ hpm)
        simp only [List.foldl_cons]
        rcases opt_none_or_some (b.rules.find? (·.lhs == r.lhs)) with hnone | ⟨rB, hrB⟩
        · rw [hnone]; exact ih acc hbs' hacc
        · rw [hrB]
          cases md with
          | extend =>
            refine ih _ hbs' ?_
            intro hnil
            exact hacc (List.append_eq_nil_iff.mp hnil).1
          | replace =>
            refine ih _ hbs' ?_
            have hrBMem := List.mem_of_find?_eq_some hrB
            have hw := List.all_eq_true.mp (List.all_eq_true.mp hBlk b hbMem) rB hrBMem
            unfold srcsOf
            dsimp only
            cases hwa : writtenAlts rB with
            | nil => rw [hwa] at hw; cases hw
            | cons _ _ => intro h; cases h
    have haltsNe : glData.alts cx .syntactic r.lhs ≠ [] := by
      unfold GL.alts
      refine hov (glData.overlays cx .syntactic) _ ?_ hpinNe
      intro ⟨b, md⟩ hbm
      unfold GL.overlays at hbm
      split at hbm
      · cases hbm
      · rw [List.mem_filterMap] at hbm
        obtain ⟨⟨bg, bcl, bkind, brules⟩, hb0Mem, hfb⟩ := hbm
        dsimp only at hfb
        cases bkind with
        | main | supplemental _ => cases hfb
        | overlay sec mode cond =>
          dsimp only at hfb
          cases hcond : (overlayGrammar sec == .syntactic && cx.annexB.has sec && condHolds cx cond) with
          | false => simp [hcond] at hfb
          | true =>
            simp only [hcond, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at hfb
            rw [← hfb.1]
            exact hb0Mem
    cases hL : glData.alts cx .syntactic r.lhs with
    | nil => exact absurd hL haltsNe
    | cons _ _ => rfl
  · intro hne
    have hneNil : Ecma.Spec.gl.alts cx .syntactic m ≠ [] := by
      intro hnil; rw [hnil] at hne; cases hne
    exact ⟨m, rfl, syn_nonempty_in_rulesOf hok hneNil⟩

private def semiInsertNTs : List NT :=
  [.LexicalDeclaration, .UsingDeclaration, .AwaitUsingDeclaration, .VariableStatement,
   .ExpressionStatement, .DoWhileStatement, .ContinueStatement, .BreakStatement,
   .ReturnStatement, .ThrowStatement, .DebuggerStatement, .ClassElement,
   .ImportDeclaration, .ExportDeclaration]

private def checkSemisRules : List Rule → Nat → Bool
  | [], _ => true
  | r :: rs, c =>
    let n := r.written.length
    ((glData.semis.all fun (sc, _, cls) =>
        !(c ≤ sc && sc < c + n && cls != .emptyStatement && cls != .forHeader)) ||
      semiInsertNTs.contains r.lhs) &&
    checkSemisRules rs (c + n)

private theorem semis_lhs_in_semiInsertNTs :
    (glData.grammars.all fun (g, rules) =>
      !(g == .syntactic || g == .annexB) || checkSemisRules rules 0) = true := by
  decide

private theorem syn_alt_grammar {cx : Ctx} {n : NT} {s : Src}
    (hs : s ∈ Ecma.Spec.gl.alts cx .syntactic n) :
    (s.grammar == .syntactic || s.grammar == .annexB) = true := by
  unfold GL.alts at hs
  have hpin : ∀ x ∈ Ecma.Spec.gl.pinned .syntactic n, (x.grammar == .syntactic || x.grammar == .annexB) = true := by
    intro x hx
    unfold GL.pinned at hx
    rcases opt_none_or_some ((Ecma.Spec.gl.rulesOf .syntactic).find? (·.lhs == n)) with hnone | ⟨r, hr⟩
    · rw [hnone] at hx; simp [baseGrammar] at hx
    · rw [hr] at hx; unfold srcsOf at hx; rw [List.mem_map] at hx
      obtain ⟨⟨_, _⟩, _, rfl⟩ := hx; rfl
  have hov : ∀ (bs : List (Block × OverlayMode)) (acc : List Src),
      (∀ x ∈ acc, (x.grammar == .syntactic || x.grammar == .annexB) = true) →
      ∀ x ∈ bs.foldl (fun a (b, md) =>
        match b.rules.find? (·.lhs == n), md with
        | none, _ => a
        | some rB, .extend => a ++ (srcsOf .annexB rB).filter fun s => !a.any (·.alt == s.alt)
        | some rB, .replace => srcsOf .annexB rB) acc,
      (x.grammar == .syntactic || x.grammar == .annexB) = true := by
    intro bs
    induction bs with
    | nil => intro acc hacc; exact hacc
    | cons hd tl ih =>
      rcases hd with ⟨b, md⟩
      intro acc hacc
      simp only [List.foldl_cons]
      rcases opt_none_or_some (b.rules.find? (·.lhs == n)) with hnone | ⟨rB, hrB⟩
      · rw [hnone]; exact ih acc hacc
      · rw [hrB]
        have hannex : ∀ y ∈ srcsOf .annexB rB, (y.grammar == .syntactic || y.grammar == .annexB) = true := by
          intro y hy; unfold srcsOf at hy; rw [List.mem_map] at hy
          obtain ⟨⟨_, _⟩, _, rfl⟩ := hy; rfl
        cases md with
        | extend =>
          refine ih _ (fun y hy => ?_)
          rcases List.mem_append.mp hy with h1 | h2
          · exact hacc y h1
          · exact hannex y (List.mem_filter.mp h2).1
        | replace => exact ih _ hannex
  exact hov (Ecma.Spec.gl.overlays cx .syntactic) _ hpin s hs

private theorem zipIdx_mem_bounds {α : Type} {a : α} {idx : Nat} :
    ∀ (xs : List α) (k : Nat), (a, idx) ∈ xs.zipIdx k → a ∈ xs ∧ k ≤ idx ∧ idx < k + xs.length
  | [], _, h => nomatch h
  | x :: xs, k, h => by
    rcases List.mem_cons.mp h with heq | htl
    · injection heq with ha hi; subst ha; subst hi
      exact ⟨List.mem_cons_self, Nat.le_refl _, by simp⟩
    · obtain ⟨hm, hlo, hhi⟩ := zipIdx_mem_bounds xs (k + 1) htl
      exact ⟨List.mem_cons_of_mem _ hm, by omega, by simp; omega⟩

private theorem checkSemisRules_sound {r0 : Rule} {i0 k0 c0 : Nat} :
    ∀ (rules : List Rule) (c : Nat),
      checkSemisRules rules c = true →
      ((r0, i0, k0), c0) ∈ (rules.flatMap fun r => r.written.zipIdx.map fun (w, i) => (r, i, w)).zipIdx c →
      ∀ sc pos cls, (sc, pos, cls) ∈ glData.semis → sc = c0 →
        cls != .emptyStatement → cls != .forHeader → semiInsertNTs.contains r0.lhs = true
  | [], _, _, hmem, _, _, _, _, _, _, _ => nomatch hmem
  | r :: rs, c, hchk, hmem, sc, pos, cls, hsem, hscEq, hne1, hne2 => by
    dsimp only [checkSemisRules] at hchk
    obtain ⟨hhead, htail⟩ := Bool.and_eq_true_iff.mp hchk
    rw [List.flatMap_cons, List.zipIdx_append] at hmem
    rcases List.mem_append.mp hmem with hleft | hright
    · obtain ⟨hm, hlo, hhi⟩ := zipIdx_mem_bounds _ c hleft
      rw [List.length_map, List.length_zipIdx] at hhi
      rw [List.mem_map] at hm
      obtain ⟨⟨_, _⟩, _, heq⟩ := hm
      injection heq with hrEq _
      subst hrEq; subst hscEq
      rcases Bool.or_eq_true_iff.mp hhead with hallNot | hcont
      · exfalso
        have h1 := List.all_eq_true.mp hallNot (sc, pos, cls) hsem
        have hloB : decide (c ≤ sc) = true := decide_eq_true hlo
        have hhiB : decide (sc < c + r.written.length) = true := decide_eq_true hhi
        simp [hloB, hhiB, hne1, hne2] at h1
      · exact hcont
    · rw [List.length_map, List.length_zipIdx] at hright
      exact checkSemisRules_sound rs (c + r.written.length) htail hright sc pos cls hsem hscEq hne1 hne2

private theorem term_is_real_of_not_semiInsertNT (hok : parseTablesOk = true)
    {P : CodePrims} {cx : Ctx} {n : NT} {s : Src} {k : Nat} {x : Terminal} {w : List Token}
    (hs : s ∈ Ecma.Spec.gl.alts cx .syntactic n)
    (hnotSemi : semiInsertNTs.contains n = false)
    (ht : (tokenAlphabet Ecma.Spec.gl cx P).term s k x w) :
    ∃ tok, w = [tok] ∧ tok.virt = none := by
  dsimp only [tokenAlphabet] at ht
  cases x with
  | cp _ => cases ht
  | text str b =>
    cases w with
    | nil => cases ht
    | cons tok tl =>
      cases tl with
      | cons _ _ => cases ht
      | nil =>
        obtain ⟨_, hvirt⟩ := ht
        cases hv : tok.virt with
        | none => exact ⟨tok, rfl, hv⟩
        | some why =>
          rw [hv] at hvirt
          obtain ⟨c, hctor, cls, hmemSemis, hclsOk⟩ := hvirt
          have ⟨hlhsEq, _⟩ := alt_lhs_and_opts hok hs
          have hsGram := syn_alt_grammar hs
          rw [← glData_eq] at hctor hmemSemis
          unfold GL.ctorOf at hctor
          rcases opt_none_or_some ((prodsOf glData.grammars).find? fun p =>
              p.grammar == s.grammar && p.rule.lhs == s.rule.lhs && p.alt == s.idx) with hnone | ⟨p, hpFind⟩
          · rw [hnone] at hctor; cases hctor
          · rw [hpFind, Option.map_some, Option.some.injEq] at hctor
            subst c
            have hpMem := List.mem_of_find?_eq_some hpFind
            have hpPred := List.find?_some hpFind
            simp only [Bool.and_eq_true, beq_iff_eq] at hpPred
            obtain ⟨⟨hpGramEq, hplhsEq⟩, _⟩ := hpPred
            unfold prodsOf at hpMem
            rw [List.mem_flatMap] at hpMem
            obtain ⟨⟨g', rules⟩, hgMem, hwMem⟩ := hpMem
            rw [List.mem_flatMap] at hwMem
            obtain ⟨⟨⟨r, i0, k0⟩, c0⟩, hwsMem, hmMap⟩ := hwMem
            rw [List.mem_map] at hmMap
            obtain ⟨_, _, hpEq⟩ := hmMap
            have hctorEq : p.ctor = c0 := by rw [← hpEq]
            have hruleEq : p.rule = r := by rw [← hpEq]
            have hgEq : p.grammar = g' := by rw [← hpEq]
            have hg'Ok : (g' == .syntactic || g' == .annexB) = true := by
              rw [← hgEq, hpGramEq]; exact hsGram
            have hgOk0 := List.all_eq_true.mp semis_lhs_in_semiInsertNTs (g', rules) hgMem
            simp only [hg'Ok, Bool.not_true, Bool.false_or] at hgOk0
            have ⟨hne1, hne2⟩ : (cls != .emptyStatement) = true ∧ (cls != .forHeader) = true := by
              cases cls <;> simp at hclsOk ⊢ <;> decide
            have hcont := checkSemisRules_sound rules 0 hgOk0 hwsMem p.ctor k cls hmemSemis hctorEq hne1 hne2
            rw [← hruleEq, hplhsEq, hlhsEq, hnotSemi] at hcont
            cases hcont

private def exprUnitNTs : List NT :=
  [.Expression, .AssignmentExpression, .ConditionalExpression, .ShortCircuitExpression,
   .CoalesceExpression, .LogicalORExpression, .LogicalANDExpression, .BitwiseORExpression,
   .BitwiseXORExpression, .BitwiseANDExpression, .EqualityExpression, .RelationalExpression,
   .ShiftExpression, .AdditiveExpression, .MultiplicativeExpression, .ExponentiationExpression,
   .UnaryExpression, .UpdateExpression, .LeftHandSideExpression, .CallExpression, .NewExpression,
   .MemberExpression, .OptionalExpression, .PrimaryExpression, .Literal, .IdentifierReference,
   .Identifier, .TemplateLiteral, .SubstitutionTemplate, .YieldExpression,
   .CoverParenthesizedExpressionAndArrowParameterList, .CoverCallExpressionAndAsyncArrowHead,
   .CoverAwaitExpressionAndAwaitUsingDeclarationHead, .ArrowFunction, .AsyncArrowFunction,
   .SuperCall, .ImportCall, .SuperProperty, .MetaProperty, .NewTarget, .ImportMeta,
   .ArrayLiteral, .ObjectLiteral, .FunctionExpression, .ClassExpression, .GeneratorExpression,
   .AsyncFunctionExpression, .AsyncGeneratorExpression]

private def realCertList : List NT :=
  [.Expression, .AssignmentExpression, .ConditionalExpression, .ShortCircuitExpression,
   .CoalesceExpression, .CoalesceExpressionHead, .BitwiseORExpression, .LogicalORExpression,
   .LogicalANDExpression, .BitwiseXORExpression, .BitwiseANDExpression, .EqualityExpression,
   .RelationalExpression, .ShiftExpression, .AdditiveExpression, .MultiplicativeExpression,
   .ExponentiationExpression, .UnaryExpression, .UpdateExpression, .LeftHandSideExpression,
   .CallExpression, .NewExpression, .MemberExpression, .OptionalExpression, .OptionalChain,
   .PrimaryExpression, .Literal, .IdentifierReference, .Identifier, .BindingIdentifier,
   .LabelIdentifier, .TemplateLiteral, .SubstitutionTemplate, .TemplateSpans, .TemplateMiddleList,
   .YieldExpression, .ArrowParameters, .ConciseBody, .ExpressionBody, .AsyncConciseBody,
   .Arguments, .ClassTail, .CoverParenthesizedExpressionAndArrowParameterList,
   .CoverCallExpressionAndAsyncArrowHead, .CoverAwaitExpressionAndAwaitUsingDeclarationHead,
   .ArrowFunction, .AsyncArrowFunction, .SuperCall, .ImportCall, .SuperProperty, .MetaProperty,
   .NewTarget, .ImportMeta, .ArrayLiteral, .ObjectLiteral, .FunctionExpression, .ClassExpression,
   .GeneratorExpression, .AsyncFunctionExpression, .AsyncGeneratorExpression]

private def itemRealCert (cx : Ctx) : Item → Bool
  | .sym (.t (.text _ _)) false | .butNot (.t (.text _ _)) _ => true
  | .sym (.nt k _) false | .butNot (.nt k _) _ =>
    (glData.alts cx .syntactic k).isEmpty || realCertList.contains k
  | _ => false

private def presentRealCount (cx : Ctx) : List Item → List Bool → Nat
  | [], _ => 0
  | .sym (.t (.text _ _)) false :: is, ms => 1 + presentRealCount cx is ms
  | .sym (.t (.text _ _)) true :: is, b :: ms => (if b then 1 else 0) + presentRealCount cx is ms
  | .sym (.t (.cp _)) true :: is, _ :: ms => presentRealCount cx is ms
  | .sym (.nt k _) false :: is, ms =>
    (if (glData.alts cx .syntactic k).isEmpty || realCertList.contains k then 1 else 0) + presentRealCount cx is ms
  | .sym (.nt k _) true :: is, b :: ms =>
    (if b && ((glData.alts cx .syntactic k).isEmpty || realCertList.contains k) then 1 else 0) + presentRealCount cx is ms
  | .butNot (.t (.text _ _)) _ :: is, ms => 1 + presentRealCount cx is ms
  | .butNot (.nt k _) _ :: is, ms =>
    (if (glData.alts cx .syntactic k).isEmpty || realCertList.contains k then 1 else 0) + presentRealCount cx is ms
  | _ :: is, ms => presentRealCount cx is ms

private theorem expr_and_realCert_check :
    ((realCertList.all fun m => !semiInsertNTs.contains m) &&
     (exprUnitNTs.all fun n => !semiInsertNTs.contains n) &&
     ((List.range 32).all fun i =>
       let cx := cxOfIdx i
       (realCertList.all fun m =>
         (glData.alts cx .syntactic m).isEmpty ||
         (glData.alts cx .syntactic m).all fun s => s.alt.rhs.any (itemRealCert cx)) &&
       (exprUnitNTs.all fun n =>
         (glData.alts cx .syntactic n).all fun s =>
           (masks ((s.alt.rhs.filter fun | .sym _ true => true | _ => false).length)).all fun m =>
             2 ≤ presentRealCount cx s.alt.rhs m ||
             (match s.alt.rhs with
              | [.sym (.t (.text _ _)) false] => true
              | _ => false) ||
             (match unitNt s.alt m with
              | some k => (glData.alts cx .syntactic k).isEmpty || exprUnitNTs.contains k
              | none => false)))) = true := by
  decide

/-! ## Slice `countP` additivity and `realCert` / `presentRealCount` lower bounds -/

private theorem slice_split {α : Type} (xs : List α) {i h j : Nat}
    (hih : i ≤ h) (hhj : h ≤ j) :
    slice xs i j = slice xs i h ++ slice xs h j := by
  unfold slice
  have h1 : j - i = (h - i) + (j - h) := by omega
  rw [h1, List.take_add, List.drop_drop, show i + (h - i) = h from by omega]

private theorem countP_slice_add {α : Type} (p : α → Bool) (xs : List α) {i h j : Nat}
    (hih : i ≤ h) (hhj : h ≤ j) :
    (slice xs i j).countP p = (slice xs i h).countP p + (slice xs h j).countP p := by
  rw [slice_split xs hih hhj, List.countP_append]

private theorem realCert_pos_count (hok : parseTablesOk = true) {cx : Ctx} {P : CodePrims} {toks : List Token} :
    ∀ (sz : Nat) {m : NT} {ps : List Param} {i j : Nat} {t : Tree},
      treeSize t ≤ sz →
      j ≤ toks.length →
      ((Ecma.Spec.gl.alts cx .syntactic m).isEmpty = true ∨ realCertList.contains m = true) →
      PosSynStep cx P toks m ps i j t →
      1 ≤ (slice toks i j).countP (fun tok => tok.virt.isNone) := by
  intro sz
  induction sz using Nat.strongRecOn with
  | ind sz ih =>
    intro m ps i j t hsz hj hcert hst
    cases hst with
    | @lex _ _ _ _ tok _ hget hleaf =>
      have hdrop : toks.drop i = tok :: toks.drop (i + 1) := by
        obtain ⟨hi, hv⟩ := List.getElem?_eq_some_iff.mp hget
        rw [List.drop_eq_getElem_cons hi, hv]
      have hsc : slice toks i (i + 1) = [tok] :=
        (slice_singleton_iff (by omega) hj).mpr ⟨rfl, hget, hdrop⟩
      rw [hsc, List.countP_cons, List.countP_nil, hleaf.1]
      simp
    | @node _ _ _ _ m0 kids0 id0 s hsMem _ _ hseq =>
      dsimp only [treeSize] at hsz
      rcases hcert with hem | hmemC
      · rw [List.isEmpty_iff] at hem; rw [hem] at hsMem; cases hsMem
      · obtain ⟨h12, hcxsOk⟩ := Bool.and_eq_true_iff.mp expr_and_realCert_check
        obtain ⟨hdisjR, _⟩ := Bool.and_eq_true_iff.mp h12
        have hmInR : m ∈ realCertList := by simpa using hmemC
        have hnotSemi : semiInsertNTs.contains m = false :=
          (Bool.not_eq_true' _) ▸ List.all_eq_true.mp hdisjR m hmInR
        have hci := List.all_eq_true.mp hcxsOk (cxIdx cx) (List.mem_range.mpr (cxIdx_lt cx))
        rw [cxOfIdx_cxIdx] at hci
        have hmOk := List.all_eq_true.mp (Bool.and_eq_true_iff.mp hci).1 m hmInR
        rw [← glData_eq] at hsMem
        have hnotEm : (glData.alts cx .syntactic m).isEmpty = false := by
          cases hL : glData.alts cx .syntactic m with
          | nil => rw [hL] at hsMem; cases hsMem
          | cons _ _ => rfl
        simp only [hnotEm, Bool.false_or] at hmOk
        have hany := List.any_eq_true.mp (List.all_eq_true.mp hmOk s hsMem)
        rw [glData_eq] at hsMem
        have hseqReal : ∀ (k : Nat) (is : List Item) (a : Nat) (mb : List Bool) (ts : List Tree),
            treeSize.treeListSize ts ≤ treeSize.treeListSize kids0 →
            (∃ it ∈ is, itemRealCert cx it = true) →
            PosSynSeq cx P toks s ps k is a j mb ts →
            1 ≤ (slice toks a j).countP (fun tok => tok.virt.isNone) := by
          intro k is
          induction is generalizing k with
          | nil => intro _ _ _ _ ⟨_, hm, _⟩ _; cases hm
          | cons it rest ihr =>
            intro a mb ts htsz ⟨it0, hit0Mem, hit0Ok⟩ hsS
            rcases List.mem_cons.mp hit0Mem with rfl | hrestMem
            · cases hsS with
              | absent _ => simp [itemRealCert] at hit0Ok
              | look _ _ | noLT _ _ | empty _ | onlyIf _ => cases hit0Ok
              | phrase hp _ => cases hp
              | @term _ _ _ x o _ _ h _ _ _ ht hr =>
                cases o with
                | true => cases x <;> cases hit0Ok
                | false =>
                  obtain ⟨tok, hsc, hvNone⟩ := term_is_real_of_not_semiInsertNT hok hsMem hnotSemi ht
                  have hah : a ≤ h := Nat.le_of_lt (slice_nonempty_lt (by rw [hsc]; exact List.cons_ne_nil _ _)).1
                  have hhj := posSynSeq_le hr
                  rw [countP_slice_add _ toks hah hhj, hsc, List.countP_cons, List.countP_nil, hvNone]
                  simp
              | @butNotT _ _ _ x _ _ _ h _ _ _ ht _ hr =>
                obtain ⟨tok, hsc, hvNone⟩ := term_is_real_of_not_semiInsertNT hok hsMem hnotSemi ht
                have hah : a ≤ h := Nat.le_of_lt (slice_nonempty_lt (by rw [hsc]; exact List.cons_ne_nil _ _)).1
                have hhj := posSynSeq_le hr
                rw [countP_slice_add _ toks hah hhj, hsc, List.countP_cons, List.countP_nil, hvNone]
                simp
              | @nt _ _ _ kNt _ o _ _ h _ _ t0 _ hs0 _ hr =>
                cases o with
                | true => cases hit0Ok
                | false =>
                  dsimp only [treeSize.treeListSize] at htsz
                  dsimp only [itemRealCert] at hit0Ok
                  rw [glData_eq] at hit0Ok
                  have hah := posSynStep_le hs0
                  have hhj := posSynSeq_le hr
                  have h1 := ih (treeSize t0) (by omega) (by omega) (Nat.le_trans hhj hj)
                    (Bool.or_eq_true_iff.mp hit0Ok) hs0
                  rw [countP_slice_add _ toks hah hhj]; omega
              | @butNotN _ _ _ kNt _ _ _ _ h _ _ t0 _ hs0 _ hr =>
                dsimp only [treeSize.treeListSize] at htsz
                dsimp only [itemRealCert] at hit0Ok
                rw [glData_eq] at hit0Ok
                have hah := posSynStep_le hs0
                have hhj := posSynSeq_le hr
                have h1 := ih (treeSize t0) (by omega) (by omega) (Nat.le_trans hhj hj)
                  (Bool.or_eq_true_iff.mp hit0Ok) hs0
                rw [countP_slice_add _ toks hah hhj]; omega
            · cases hsS with
              | absent hr | look _ hr | noLT _ hr | empty hr | onlyIf hr =>
                exact ihr (k + 1) a _ _ htsz ⟨it0, hrestMem, hit0Ok⟩ hr
              | phrase hp _ => cases hp
              | @term _ _ _ x _ _ _ h _ _ _ ht hr =>
                dsimp only [treeSize.treeListSize, treeSize] at htsz
                obtain ⟨tok, hsc, _⟩ := term_is_real_of_not_semiInsertNT hok hsMem hnotSemi ht
                have hah : a ≤ h := Nat.le_of_lt (slice_nonempty_lt (by rw [hsc]; exact List.cons_ne_nil _ _)).1
                have hhj := posSynSeq_le hr
                have hr1 := ihr (k + 1) h _ _ (by omega) ⟨it0, hrestMem, hit0Ok⟩ hr
                rw [countP_slice_add _ toks hah hhj]; omega
              | @butNotT _ _ _ x _ _ _ h _ _ _ ht _ hr =>
                dsimp only [treeSize.treeListSize, treeSize] at htsz
                obtain ⟨tok, hsc, _⟩ := term_is_real_of_not_semiInsertNT hok hsMem hnotSemi ht
                have hah : a ≤ h := Nat.le_of_lt (slice_nonempty_lt (by rw [hsc]; exact List.cons_ne_nil _ _)).1
                have hhj := posSynSeq_le hr
                have hr1 := ihr (k + 1) h _ _ (by omega) ⟨it0, hrestMem, hit0Ok⟩ hr
                rw [countP_slice_add _ toks hah hhj]; omega
              | @nt _ _ _ _ _ _ _ _ h _ _ _ _ hs0 _ hr | @butNotN _ _ _ _ _ _ _ _ h _ _ _ _ hs0 _ hr =>
                dsimp only [treeSize.treeListSize] at htsz
                have hah := posSynStep_le hs0
                have hhj := posSynSeq_le hr
                have hr1 := ihr (k + 1) h _ _ (by omega) ⟨it0, hrestMem, hit0Ok⟩ hr
                rw [countP_slice_add _ toks hah hhj]; omega
        exact hseqReal 0 s.alt.rhs i m0 kids0 (Nat.le_refl _) hany hseq

private theorem presentRealCount_absent (cx : Ctx) (sym0 : Sym) (rest : List Item) (m : List Bool) :
    presentRealCount cx (.sym sym0 true :: rest) (false :: m) = presentRealCount cx rest m := by
  cases sym0 with
  | t x => cases x <;> simp [presentRealCount]
  | nt _ _ => simp [presentRealCount]

private theorem presentRealCount_term (cx : Ctx) (str : String) (alt o : Bool) (rest : List Item) (m : List Bool) :
    presentRealCount cx (.sym (.t (.text str alt)) o :: rest) (if o then true :: m else m) =
      1 + presentRealCount cx rest m := by
  cases o <;> simp [presentRealCount]

private theorem presentRealCount_nt (cx : Ctx) (kNt : NT) (args : List Arg) (o : Bool) (rest : List Item) (m : List Bool) :
    presentRealCount cx (.sym (.nt kNt args) o :: rest) (if o then true :: m else m) =
      (if (glData.alts cx .syntactic kNt).isEmpty || realCertList.contains kNt then 1 else 0) +
        presentRealCount cx rest m := by
  cases o <;> simp [presentRealCount]

private theorem unitNt_go_absent (sym0 : Sym) (rest : List Item) (m : List Bool) :
    unitNt.go (.sym sym0 true :: rest) (false :: m) = unitNt.go rest m := by
  cases sym0 <;> rfl

private theorem unitNt_go_nt (mNt : NT) (args : List Arg) (o : Bool) (rest : List Item) (m : List Bool) :
    unitNt.go (.sym (.nt mNt args) o :: rest) (if o then true :: m else m) = some mNt :: unitNt.go rest m := by
  cases o <;> rfl

private theorem presentRealCount_le_countP (hok : parseTablesOk = true) {cx : Ctx} {P : CodePrims} {toks : List Token}
    {n : NT} {s : Src} (hsMem : s ∈ Ecma.Spec.gl.alts cx .syntactic n)
    (hnotSemi : semiInsertNTs.contains n = false) {ps : List Param} :
    ∀ (k : Nat) (is : List Item) (a b : Nat) (m : List Bool) (ts : List Tree),
      b ≤ toks.length →
      PosSynSeq cx P toks s ps k is a b m ts →
      presentRealCount cx is m ≤ (slice toks a b).countP (fun tok => tok.virt.isNone) := by
  intro k is
  induction is generalizing k with
  | nil => intro _ _ _ _ _ _; simp [presentRealCount]
  | cons it rest ih =>
    intro a b m ts hb hseq
    cases hseq with
    | absent hr =>
      rw [presentRealCount_absent]
      exact ih (k + 1) a b _ ts hb hr
    | phrase hp _ => cases hp
    | look _ hr | noLT _ hr | empty hr | onlyIf hr =>
      simpa [presentRealCount] using ih (k + 1) a b m ts hb hr
    | @term _ _ _ x o _ _ h _ m' _ ht hr =>
      obtain ⟨tok, hsc, hvNone⟩ := term_is_real_of_not_semiInsertNT hok hsMem hnotSemi ht
      have hah : a ≤ h := Nat.le_of_lt (slice_nonempty_lt (by rw [hsc]; exact List.cons_ne_nil _ _)).1
      have hhb := posSynSeq_le hr
      have hih := ih (k + 1) h b m' _ hb hr
      rw [countP_slice_add _ toks hah hhb, hsc, List.countP_cons, List.countP_nil, hvNone]
      cases x with
      | cp _ => cases ht
      | text str alt => rw [presentRealCount_term]; simp only [Option.isNone_none, ↓reduceIte]; omega
    | @butNotT _ _ _ x _ _ _ h _ _ _ ht _ hr =>
      obtain ⟨tok, hsc, hvNone⟩ := term_is_real_of_not_semiInsertNT hok hsMem hnotSemi ht
      have hah : a ≤ h := Nat.le_of_lt (slice_nonempty_lt (by rw [hsc]; exact List.cons_ne_nil _ _)).1
      have hhb := posSynSeq_le hr
      have hih := ih (k + 1) h b m _ hb hr
      rw [countP_slice_add _ toks hah hhb, hsc, List.countP_cons, List.countP_nil, hvNone]
      cases x with
      | cp _ => cases ht
      | text _ _ => dsimp only [presentRealCount]; simp only [Option.isNone_none, ↓reduceIte]; omega
    | @nt _ _ _ kNt _ o _ _ h _ m' t0 _ hs0 _ hr =>
      have hah := posSynStep_le hs0
      have hhb := posSynSeq_le hr
      have hih := ih (k + 1) h b m' _ hb hr
      rw [countP_slice_add _ toks hah hhb, presentRealCount_nt]
      cases hcOk : ((glData.alts cx .syntactic kNt).isEmpty || realCertList.contains kNt) with
      | true =>
        have h1 := realCert_pos_count hok (treeSize t0) (Nat.le_refl _) (Nat.le_trans hhb hb)
          (by rw [← glData_eq]; exact Bool.or_eq_true_iff.mp hcOk) hs0
        simp only [↓reduceIte]; omega
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte]; omega
    | @butNotN _ _ _ kNt _ _ _ _ h _ _ t0 _ hs0 _ hr =>
      have hah := posSynStep_le hs0
      have hhb := posSynSeq_le hr
      have hih := ih (k + 1) h b m _ hb hr
      rw [countP_slice_add _ toks hah hhb]
      dsimp only [presentRealCount]
      cases hcOk : ((glData.alts cx .syntactic kNt).isEmpty || realCertList.contains kNt) with
      | true =>
        have h1 := realCert_pos_count hok (treeSize t0) (Nat.le_refl _) (Nat.le_trans hhb hb)
          (by rw [← glData_eq]; exact Bool.or_eq_true_iff.mp hcOk) hs0
        simp only [↓reduceIte]; omega
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte]; omega

private theorem seq_of_unitNt_nil {cx : Ctx} {P : CodePrims} {toks : List Token} {s : Src} {ps : List Param} :
    ∀ (k : Nat) (is : List Item) (a b : Nat) (m : List Bool) (ts : List Tree),
      unitNt.go is m = [] →
      PosSynSeq cx P toks s ps k is a b m ts →
      a = b ∧ ts.filter (fun x => !x.isLeaf) = [] := by
  intro k is
  induction is generalizing k with
  | nil => intro _ _ _ _ _ hs; cases hs; exact ⟨rfl, rfl⟩
  | cons it rest ih =>
    intro a b m ts hu hs
    cases hs with
    | absent hr =>
      rw [unitNt_go_absent] at hu
      exact ih (k + 1) a b _ ts hu hr
    | @term _ _ _ _ o _ _ _ _ _ _ _ _ =>
      cases o <;> simp [unitNt.go] at hu
    | @nt _ _ _ _ _ o _ _ _ _ _ _ _ _ _ _ =>
      cases o <;> simp [unitNt.go] at hu
    | butNotT _ _ _ | butNotN _ _ _ => simp [unitNt.go] at hu
    | phrase hp _ => cases hp
    | look _ hr | noLT _ hr | empty hr | onlyIf hr =>
      dsimp only [unitNt.go] at hu
      exact ih (k + 1) a b m ts hu hr

private theorem seq_of_unitNt_some {cx : Ctx} {P : CodePrims} {toks : List Token} {s : Src} {ps : List Param}
    {k0 : NT} :
    ∀ (k : Nat) (is : List Item) (a b : Nat) (m : List Bool) (ts : List Tree),
      unitNt.go is m = [some k0] →
      PosSynSeq cx P toks s ps k is a b m ts →
      ∃ c psC, ts.filter (fun x => !x.isLeaf) = [c] ∧ c.span = (a, b) ∧ PosSynStep cx P toks k0 psC a b c := by
  intro k is
  induction is generalizing k with
  | nil => intro _ _ _ _ hu _; cases hu
  | cons it rest ih =>
    intro a b m ts hu hs
    cases hs with
    | absent hr =>
      rw [unitNt_go_absent] at hu
      exact ih (k + 1) a b _ ts hu hr
    | @term _ _ _ _ o _ _ _ _ _ _ _ _ =>
      cases o <;> simp [unitNt.go] at hu
    | butNotT _ _ _ => simp [unitNt.go] at hu
    | phrase hp _ => cases hp
    | look _ hr | noLT _ hr | empty hr | onlyIf hr =>
      dsimp only [unitNt.go] at hu
      exact ih (k + 1) a b m ts hu hr
    | @nt _ _ _ mNt argsNt o _ _ h _ m' t0 ts' hs0 _ hr =>
      rw [unitNt_go_nt] at hu
      injection hu with hmEq hrestNil
      injection hmEq with hmEq'
      subst hmEq'
      obtain ⟨rfl, htsNil⟩ := seq_of_unitNt_nil (k + 1) rest h b m' ts' hrestNil hr
      have ht0Sp : t0.span = (a, h) ∧ (!t0.isLeaf) = true := by
        cases hs0 with
        | node _ _ _ _ _ => exact ⟨rfl, rfl⟩
        | lex _ _ _ => exact ⟨rfl, rfl⟩
      rw [List.filter_cons, htsNil]
      simp only [ht0Sp.2, ↓reduceIte]
      exact ⟨t0, applyArgs ps argsNt, rfl, ht0Sp.1, hs0⟩
    | @butNotN _ _ _ mNt argsNt _ _ _ h _ _ t0 ts' hs0 _ hr =>
      dsimp only [unitNt.go] at hu
      injection hu with hmEq hrestNil
      injection hmEq with hmEq'
      subst hmEq'
      obtain ⟨rfl, htsNil⟩ := seq_of_unitNt_nil (k + 1) rest h b m ts' hrestNil hr
      have ht0Sp : t0.span = (a, h) ∧ (!t0.isLeaf) = true := by
        cases hs0 with
        | node _ _ _ _ _ => exact ⟨rfl, rfl⟩
        | lex _ _ _ => exact ⟨rfl, rfl⟩
      rw [List.filter_cons, htsNil]
      simp only [ht0Sp.2, ↓reduceIte]
      exact ⟨t0, applyArgs ps argsNt, rfl, ht0Sp.1, hs0⟩

private theorem exprUnit_oneReal_all_spans_eq (hok : parseTablesOk = true)
    {cx : Ctx} {P : CodePrims} {toks : List Token} :
    ∀ (t : Tree) {n : NT} {ps : List Param} {i j : Nat},
      j ≤ toks.length →
      ((Ecma.Spec.gl.alts cx .syntactic n).isEmpty = true ∨ exprUnitNTs.contains n = true) →
      (slice toks i j).countP (fun tok => tok.virt.isNone) ≤ 1 →
      PosSynStep cx P toks n ps i j t →
      t.span = (i, j) ∧ ∀ c ∈ (Tree.view fun _ _ => []).kids t,
        ∃ n' ps', ((Ecma.Spec.gl.alts cx .syntactic n').isEmpty = true ∨ exprUnitNTs.contains n' = true) ∧
          PosSynStep cx P toks n' ps' i j c := by
  intro t n ps i j hj hn hle1 hst
  cases hst with
  | lex _ _ _ => exact ⟨rfl, fun _ hc => nomatch hc⟩
  | @node _ _ _ _ m0 kids0 id0 s hsMem _ _ hseq =>
    refine ⟨rfl, ?_⟩
    rcases hn with hem | hnMem
    · rw [List.isEmpty_iff] at hem; rw [hem] at hsMem; cases hsMem
    · obtain ⟨h12, hcxsOk⟩ := Bool.and_eq_true_iff.mp expr_and_realCert_check
      obtain ⟨_, hdisjE⟩ := Bool.and_eq_true_iff.mp h12
      have hnInE : n ∈ exprUnitNTs := by simpa using hnMem
      have hnotSemi : semiInsertNTs.contains n = false :=
        (Bool.not_eq_true' _) ▸ List.all_eq_true.mp hdisjE n hnInE
      have hci := List.all_eq_true.mp hcxsOk (cxIdx cx) (List.mem_range.mpr (cxIdx_lt cx))
      rw [cxOfIdx_cxIdx] at hci
      have hmask := seq_masks_syn hseq
      rw [← glData_eq] at hsMem
      have hcase := List.all_eq_true.mp
        (List.all_eq_true.mp (List.all_eq_true.mp (Bool.and_eq_true_iff.mp hci).2 n hnInE) s hsMem) m0 hmask
      rw [glData_eq] at hsMem
      have hcntLe := presentRealCount_le_countP hok hsMem hnotSemi 0 s.alt.rhs i j m0 kids0 hj hseq
      have hnot2 : decide (2 ≤ presentRealCount cx s.alt.rhs m0) = false := decide_eq_false (by omega)
      rw [hnot2, Bool.false_or] at hcase
      rcases Bool.or_eq_true_iff.mp hcase with hsingleT | hunit
      · generalize hrhs : s.alt.rhs = rhs0 at hsingleT hseq
        cases rhs0 with
        | nil => cases hsingleT
        | cons it0 tl0 =>
          cases tl0 with
          | cons _ _ => simp at hsingleT
          | nil =>
            cases it0 with
            | sym sym0 o0 =>
              cases sym0 with
              | nt _ _ => simp at hsingleT
              | t x0 =>
                cases o0 with
                | true => simp at hsingleT
                | false =>
                  cases hseq with
                  | term _ hrNil =>
                    cases hrNil
                    intro c hc
                    simp [Tree.view, Tree.isLeaf] at hc
            | _ => simp at hsingleT
      · cases hu : unitNt s.alt m0 with
        | none => rw [hu] at hunit; cases hunit
        | some k0 =>
          rw [hu] at hunit
          unfold unitNt at hu
          have hgo : unitNt.go s.alt.rhs m0 = [some k0] := by
            cases hg : unitNt.go s.alt.rhs m0 with
            | nil => rw [hg] at hu; cases hu
            | cons x xs =>
              cases x with
              | none => rw [hg] at hu; cases xs <;> cases hu
              | some v =>
                cases xs with
                | cons _ _ => rw [hg] at hu; cases hu
                | nil => rw [hg] at hu; injection hu with hvEq; subst hvEq; rfl
          obtain ⟨c0, psC, hkidsEq, _, hstC⟩ := seq_of_unitNt_some 0 s.alt.rhs i j m0 kids0 hgo hseq
          intro c hc
          dsimp only [Tree.view] at hc
          rw [hkidsEq, List.mem_singleton] at hc
          subst hc
          rw [glData_eq] at hunit
          exact ⟨k0, psC, Bool.or_eq_true_iff.mp hunit, hstC⟩

/-! ## `Scans`, `tokensOf`, and `tokenSpan` properties -/

private theorem els_sorted_bounds :
    ∀ (L : List Element) (start : Nat),
      (∀ (m : Nat) e, L[m]? = some e → e.i = if m == 0 then start else (L[m - 1]?.map (·.j)).getD 0) →
      (∀ e ∈ L, e.i < e.j) →
      (∀ (m : Nat) e, L[m]? = some e → start ≤ e.i ∧ e.i < e.j) ∧
      (∀ (m1 m2 : Nat) e1 e2, m1 < m2 → L[m1]? = some e1 → L[m2]? = some e2 → e1.j ≤ e2.i) ∧
      (∀ (m : Nat) e last, L[m]? = some e → L.getLast? = some last → e.j ≤ last.j) := by
  intro L
  induction L with
  | nil =>
    intro _ _ _
    exact ⟨fun _ _ h => by simp at h, fun _ _ _ _ _ h => by simp at h, fun _ _ _ h _ => by simp at h⟩
  | cons hd tl ih =>
    intro start hadj hlt
    have hhdI : hd.i = start := hadj 0 hd rfl
    have hhdLt : hd.i < hd.j := hlt hd List.mem_cons_self
    have hadjTl : ∀ (m : Nat) e, tl[m]? = some e →
        e.i = if m == 0 then hd.j else (tl[m - 1]?.map (·.j)).getD 0 := by
      intro m e hm
      have h1 := hadj (m + 1) e (by simpa using hm)
      cases m with
      | zero => simpa using h1
      | succ m' => simpa using h1
    have ⟨hbTl, hordTl, hlastTl⟩ := ih hd.j hadjTl (fun e he => hlt e (List.mem_cons_of_mem _ he))
    refine ⟨?_, ?_, ?_⟩
    · intro m e hm
      cases m with
      | zero => simp only [List.getElem?_cons_zero, Option.some.injEq] at hm; subst hm; omega
      | succ m' =>
        have ⟨h1, h2⟩ := hbTl m' e (by simpa using hm)
        omega
    · intro m1 m2 e1 e2 hm12 he1 he2
      cases m2 with
      | zero => omega
      | succ m2' =>
        cases m1 with
        | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at he1; subst he1
          exact (hbTl m2' e2 (by simpa using he2)).1
        | succ m1' =>
          exact hordTl m1' m2' e1 e2 (by omega) (by simpa using he1) (by simpa using he2)
    · intro m e last hm hlast
      cases tl with
      | nil =>
        cases m with
        | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hm
          simp only [List.getLast?_singleton, Option.some.injEq] at hlast
          subst hm; subst hlast; exact Nat.le_refl _
        | succ m' => simp at hm
      | cons hd2 tl2 =>
        have hlast' : (hd2 :: tl2).getLast? = some last := by simpa using hlast
        cases m with
        | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hm; subst hm
          have h2 := hlastTl 0 hd2 last rfl hlast'
          have hhd2 := (hbTl 0 hd2 rfl)
          omega
        | succ m' =>
          exact hlastTl m' e last (by simpa using hm) hlast'

private theorem filter_strict_mono {α : Type} {R : α → α → Prop} (p : α → Bool) :
    ∀ (xs : List α),
      (∀ (m1 m2 : Nat) e1 e2, m1 < m2 → xs[m1]? = some e1 → xs[m2]? = some e2 → R e1 e2) →
      ∀ (k1 k2 : Nat) e1 e2, k1 < k2 → (xs.filter p)[k1]? = some e1 → (xs.filter p)[k2]? = some e2 → R e1 e2 := by
  intro xs
  induction xs with
  | nil => intro _ _ _ _ _ _ h _; simp at h
  | cons x xs ih0 =>
    intro hord
    have hmem_head : ∀ {k : Nat} {e : α}, (xs.filter p)[k]? = some e → R x e := by
      intro k e hk
      have heMem : e ∈ xs := (List.mem_filter.mp (List.mem_of_getElem? hk)).1
      obtain ⟨idx, hidxLt, rfl⟩ := List.getElem_of_mem heMem
      exact hord 0 (idx + 1) x xs[idx] (by omega) rfl (by simp [hidxLt])
    have ih := ih0 (fun m1 m2 e1 e2 hm he1 he2 =>
      hord (m1 + 1) (m2 + 1) e1 e2 (by omega) (by simpa using he1) (by simpa using he2))
    by_cases hpx : p x = true
    · simp only [List.filter_cons, hpx, ↓reduceIte]
      intro k1 k2 e1 e2 hk12 he1 he2
      cases k2 with
      | zero => omega
      | succ k2' =>
        cases k1 with
        | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at he1; subst he1
          exact hmem_head (by simpa using he2)
        | succ k1' =>
          exact ih k1' k2' e1 e2 (by omega) (by simpa using he1) (by simpa using he2)
    · simp only [List.filter_cons, hpx, Bool.false_eq_true, ↓reduceIte]
      exact ih

private theorem scans_token_elems {cx : Ctx} {P : CodePrims} {src : List Nat} {els : List Element}
    (hScans : Scans Ecma.Spec.gl cx P src els) :
    let es := els.filter Element.isToken
    (∀ e ∈ es, e.i < e.j ∧ e.j ≤ src.length) ∧
    (∀ (k1 k2 : Nat) e1 e2, k1 < k2 → es[k1]? = some e1 → es[k2]? = some e2 → e1.j ≤ e2.i) := by
  obtain ⟨hzip, hlastEq, hallElem⟩ := hScans
  have hadj : ∀ (m : Nat) e, els[m]? = some e →
      e.i = if m == 0 then 0 else (els[m - 1]?.map (·.j)).getD 0 := by
    intro m e hm
    have hmemZ : (e, m) ∈ els.zipIdx := by
      have hgen : ∀ (l : List Element) (k i : Nat) (x : Element),
          l[i]? = some x → (x, k + i) ∈ l.zipIdx k := by
        intro l; induction l with
        | nil => intro _ _ _ h; cases h
        | cons hd tl ihl =>
          intro k i x h
          cases i with
          | zero => simp only [List.getElem?_cons_zero, Option.some.injEq] at h; subst h; simp
          | succ i' =>
            have := ihl (k + 1) i' x (by simpa using h)
            rw [List.zipIdx_cons]
            refine List.mem_cons_of_mem _ ?_
            simpa [Nat.add_assoc, Nat.add_comm 1 i'] using this
      simpa using hgen els 0 m e hm
    exact beq_iff_eq.mp (List.all_eq_true.mp hzip (e, m) hmemZ)
  have ⟨_, hord, hlast⟩ := els_sorted_bounds els 0 hadj (fun e he => (hallElem e he).1)
  refine ⟨?_, filter_strict_mono Element.isToken els hord⟩
  intro e he
  have heEls := (List.mem_filter.mp he).1
  obtain ⟨idx, hidxLt, rfl⟩ := List.getElem_of_mem heEls
  have hltIJ := (hallElem els[idx] heEls).1
  cases hgl : els.getLast? with
  | none =>
    have hnil := List.getLast?_eq_none_iff.mp hgl
    rw [hnil] at hidxLt; simp at hidxLt
  | some last =>
    rw [hgl, Option.map_some, Option.getD_some] at hlastEq
    have hleLast := hlast idx els[idx] last (by simp [hidxLt]) hgl
    exact ⟨hltIJ, by omega⟩

private theorem zipIdx_filter_fst {α : Type} (p : α → Bool) :
    ∀ (xs : List α) (k : Nat),
      ((xs.zipIdx k).filter (fun x => p x.1)).map Prod.fst = xs.filter p
  | [], _ => rfl
  | x :: xs, k => by
    simp only [List.zipIdx_cons, List.filter_cons]
    cases p x <;> simp [zipIdx_filter_fst p xs (k + 1)]

private theorem tokensOf_length_and_get (src : List Nat) (els : List Element) :
    (tokensOf src els).length = (els.filter Element.isToken).length ∧
    ∀ (r : Nat) (tok : Token), (tokensOf src els)[r]? = some tok →
      ∃ el, (els.filter Element.isToken)[r]? = some el ∧ tok.text = slice src el.i el.j := by
  have hfst := zipIdx_filter_fst Element.isToken els 0
  unfold tokensOf
  refine ⟨by rw [List.length_map, ← List.length_map (f := Prod.fst), hfst], ?_⟩
  intro r tok hget
  rw [List.getElem?_map] at hget
  rcases opt_none_or_some ((els.zipIdx.filter fun x => x.1.isToken)[r]?) with hnone | ⟨⟨el, idx⟩, hel⟩
  · rw [hnone] at hget; cases hget
  · rw [hel, Option.map_some, Option.some.injEq] at hget
    have helFst : (els.filter Element.isToken)[r]? = some el := by
      rw [← hfst, List.getElem?_map, hel]; rfl
    exact ⟨el, helFst, by rw [← hget]⟩

private theorem filter_getElem?_of_getElem?_true {α : Type} (p : α → Bool) :
    ∀ (xs : List α) (k : Nat) (x : α),
      xs[k]? = some x → p x = true →
      (xs.take (k + 1)).countP p = (xs.take k).countP p + 1 ∧
      (xs.filter p)[(xs.take k).countP p]? = some x
  | [], _, _, h, _ => nomatch h
  | y :: ys, 0, x, h, hpx => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at h; subst h
    simp [List.take, hpx]
  | y :: ys, k + 1, x, h, hpx => by
    have ⟨hc, hg⟩ := filter_getElem?_of_getElem?_true p ys k x (by simpa using h) hpx
    by_cases hpy : p y = true
    · simp only [List.take_succ_cons, List.countP_cons, hpy, ↓reduceIte, List.filter_cons]
      refine ⟨by omega, ?_⟩
      rw [show (ys.take k).countP p + 1 = ((ys.take k).countP p) + 1 from rfl, List.getElem?_cons_succ]
      exact hg
    · simp only [List.take_succ_cons, List.countP_cons, hpy, Bool.false_eq_true, ↓reduceIte, Nat.add_zero, List.filter_cons]
      exact ⟨hc, hg⟩

private theorem length_filter_eq_countP {α : Type} (p : α → Bool) :
    ∀ xs : List α, (xs.filter p).length = xs.countP p
  | [] => rfl
  | x :: xs => by
    simp only [List.filter_cons, List.countP_cons]
    cases p x <;> simp [length_filter_eq_countP p xs]

private theorem take_countP_slice_add {α : Type} (p : α → Bool) (xs : List α) {a b : Nat}
    (hab : a ≤ b) (_hb : b ≤ xs.length) :
    (xs.take b).countP p = (xs.take a).countP p + (slice xs a b).countP p ∧
    (xs.take b).countP p ≤ (xs.filter p).length := by
  have h1 : xs.take b = xs.take a ++ slice xs a b := by
    unfold slice
    have hbEq : b = a + (b - a) := by omega
    conv => lhs; rw [hbEq]
    exact List.take_add
  have h2 : xs = xs.take b ++ xs.drop b := (List.take_append_drop b xs).symm
  refine ⟨by rw [h1, List.countP_append], ?_⟩
  rw [length_filter_eq_countP]
  conv => rhs; rw [h2, List.countP_append]
  omega

private theorem tokenSpan_ne_of_two_real {cx : Ctx} {P : CodePrims} {src : List Nat}
    {els : List Element} {toks : List Token}
    (hScans : Scans Ecma.Spec.gl cx P src els)
    (htoks : toks.filter (fun x => x.virt.isNone) = tokensOf src els)
    {i j k : Nat} {tok : Token}
    (hij : i ≤ j) (hj : j ≤ toks.length)
    (htwo : 2 ≤ (slice toks i j).countP (fun x => x.virt.isNone))
    (hk : toks[k]? = some tok) (hkv : tok.virt = none) :
    Ecma.Grammar.tokenSpan els toks k (k + 1) ≠ Ecma.Grammar.tokenSpan els toks i j := by
  have ⟨hesBounds, hesOrd⟩ := scans_token_elems hScans
  have ⟨hlenToks, _⟩ := tokensOf_length_and_get src els
  have hlenFilt : (toks.filter fun x => x.virt.isNone).length = (els.filter Element.isToken).length :=
    htoks ▸ hlenToks
  have ⟨haddIJ, hleB⟩ := take_countP_slice_add (fun x => x.virt.isNone) toks hij hj
  have hkvB : tok.virt.isNone = true := by simp [hkv]
  have ⟨hcK, hgetK⟩ := filter_getElem?_of_getElem?_true (fun x => x.virt.isNone) toks k tok hk hkvB
  have hab2 : (toks.take i).countP (fun x => x.virt.isNone) + 2 ≤
      (toks.take j).countP (fun x => x.virt.isNone) := by omega
  have hbEs : (toks.take j).countP (fun x => x.virt.isNone) ≤ (els.filter Element.isToken).length := by omega
  have hrLt : (toks.take k).countP (fun x => x.virt.isNone) < (els.filter Element.isToken).length := by
    have := (List.getElem?_eq_some_iff.mp hgetK).1
    omega
  let es := els.filter Element.isToken
  let a := (toks.take i).countP (fun x => x.virt.isNone)
  let b := (toks.take j).countP (fun x => x.virt.isNone)
  let r := (toks.take k).countP (fun x => x.virt.isNone)
  obtain ⟨ea, hea⟩ : ∃ ea, es[a]? = some ea := ⟨es[a]'(by dsimp only [es, a] at *; omega), by simp⟩
  obtain ⟨eb, heb⟩ : ∃ eb, es[b - 1]? = some eb := ⟨es[b - 1]'(by dsimp only [es, b] at *; omega), by simp⟩
  obtain ⟨er, her⟩ : ∃ er, es[r]? = some er := ⟨es[r]'hrLt, by simp⟩
  have hspK : Ecma.Grammar.tokenSpan els toks k (k + 1) = (er.i, er.j) := by
    unfold Ecma.Grammar.tokenSpan
    change (let start := (es[r]?.map (·.i)).getD _;
      if r < (toks.take (k + 1)).countP (fun x => x.virt.isNone) then
        (start, (es[(toks.take (k + 1)).countP (fun x => x.virt.isNone) - 1]?.map (·.j)).getD start)
      else (start, start)) = (er.i, er.j)
    rw [hcK]
    split
    · rw [Nat.add_sub_cancel, her]; rfl
    · dsimp only [r] at *; omega
  have hspIJ : Ecma.Grammar.tokenSpan els toks i j = (ea.i, eb.j) := by
    unfold Ecma.Grammar.tokenSpan
    change (let start := (es[a]?.map (·.i)).getD _;
      if a < b then (start, (es[b - 1]?.map (·.j)).getD start) else (start, start)) = (ea.i, eb.j)
    split
    · rw [hea, heb]; rfl
    · dsimp only [a, b] at *; omega
  rw [hspK, hspIJ]
  intro heq
  injection heq with hiEq hjEq
  have heaB := (hesBounds ea (List.mem_of_getElem? hea)).1
  have hebB := (hesBounds eb (List.mem_of_getElem? heb)).1
  have herB := (hesBounds er (List.mem_of_getElem? her)).1
  have habOrd := hesOrd a (b - 1) ea eb (by dsimp only [a, b] at *; omega) hea heb
  by_cases hra : r ≤ a
  · by_cases hrEq : r = a
    · rw [hrEq, hea] at her; injection her with herEq; subst herEq; omega
    · have hraOrd := hesOrd r a er ea (by omega) her hea
      omega
  · have harOrd := hesOrd a r ea er (by omega) hea her
    omega

/-! ## Relating `Model.NodeRel` + `PosSynStep` to `Strict.view` and `Tree.view` -/

private theorem source_toList_of_nodeRel {src : List Nat} {sp : Nat × Nat} {txt : Subarray Nat}
    (hslen : Engine.Model.MathVal.int (txt.toArray.map Engine.Impl.ofNat).size =
      Engine.Model.MathVal.int (slice src sp.1 sp.2).length)
    (hsget : ∀ (k : Nat),
      Engine.Impl.seqGet (txt.toArray.map Engine.Impl.ofNat) (Engine.Impl.ofNat k) =
        (slice src sp.1 sp.2)[k]?.map Engine.Impl.ofNat) :
    txt.toArray.toList = slice src sp.1 sp.2 := by
  injection hslen with hszI
  have hsz : txt.toArray.toList.length = (slice src sp.1 sp.2).length := by
    have h1 : (txt.toArray.map Engine.Impl.ofNat).size = txt.toArray.toList.length := by
      rw [Array.size_map, Array.length_toList]
    omega
  apply List.ext_getElem hsz
  intro k hk1 hk2
  have hg := hsget k
  rw [impl_seqGet_nat, Array.getElem?_map] at hg
  have h1 : txt.toArray[k]? = some txt.toArray.toList[k] := by
    rw [← Array.getElem?_toList, List.getElem?_eq_getElem hk1]
  have h2 : (slice src sp.1 sp.2)[k]? = some (slice src sp.1 sp.2)[k] := List.getElem?_eq_getElem hk2
  rw [h1, h2, Option.map_some, Option.map_some, Option.some.injEq] at hg
  change Engine.Model.MathVal.int (txt.toArray.toList[k] : Int) = Engine.Model.MathVal.int ((slice src sp.1 sp.2)[k] : Int) at hg
  injection hg with hiEq
  omega

private theorem lex_step_is_node {P : CodePrims} {cx : Ctx} {w : List Nat}
    {neg : NT → List Param → Nat → Nat → Prop} {n : NT} {ps : List Param} {a b : Nat} {lt : Tree}
    (h : Step (codeAlphabet P) neg w Ecma.Spec.gl cx .lexical n ps a b lt) :
    ∃ id kids, lt = .node n id ps a b kids := by
  cases h with
  | lex _ _ hl => cases hl
  | node _ _ _ _ _ => exact ⟨_, _, rfl⟩

private theorem nodeRel_inv_lex {M : Ecma.Model} {st : Nat} {src : List Nat} {sp : Nat → Nat → Nat × Nat}
    {nd : M.Node} {i : Nat} {lt : Tree} :
    Ecma.Model.NodeRel M st src sp nd (.lex i lt) →
    Ecma.Model.NodeRel M st src (fun a b => ((sp i (i + 1)).1 + a, (sp i (i + 1)).1 + b)) nd lt
  | .lex hl => hl

private theorem nodeRel_inv_node {M : Ecma.Model} {st : Nat} {src : List Nat} {sp : Nat → Nat → Nat × Nat}
    {nd : M.Node} {n : NT} {id : Nat} {ps : List Param} {i j : Nat} {kids : List Tree} :
    Ecma.Model.NodeRel M st src sp nd (.node n id ps i j kids) →
    M.nodeNt nd = n.ctorIdx ∧
    M.nodeProd nd = id ∧
    M.nodeSpan nd = sp i j ∧
    M.seqLen (M.nodeSource nd) = M.ofNat (slice src (sp i j).1 (sp i j).2).length ∧
    (∀ k : Nat, M.seqGet (M.nodeSource nd) (M.ofNat k) =
      (slice src (sp i j).1 (sp i j).2)[k]?.map M.ofNat) ∧
    M.seqLen (M.nodeKids nd) = M.ofNat (kids.filter fun x => !x.isLeaf).length ∧
    (∀ (idx : Nat) c_t c_nd,
      (kids.filter fun x => !x.isLeaf)[idx]? = some c_t →
      M.seqGet (M.nodeKids nd) (M.ofNat idx) = some c_nd →
      Ecma.Model.NodeRel M st src sp c_nd c_t)
  | .node hnt hprod _ _ hsp hslen hsget hklen _ hkids =>
    ⟨hnt, hprod, hsp, hslen, hsget, hklen, hkids⟩

private theorem nodeRel_syn_props (hok : parseTablesOk = true) {cx : Ctx} {P : CodePrims}
    {src : List Nat} {els : List Element} {toks : List Token} {st d : Nat}
    (hScans : Scans Ecma.Spec.gl cx P src els)
    (htoks : toks.filter (fun x => x.virt.isNone) = tokensOf src els)
    {n : NT} {ps : List Param} {i j : Nat} {nd : Engine.Model.Node} {t : Tree}
    (hj : j ≤ toks.length)
    (hst : PosSynStep cx P toks n ps i j t)
    (hrel : Ecma.Model.NodeRel Engine.Impl st src (Ecma.Grammar.tokenSpan els toks) nd t) :
    let text := Ecma.Grammar.tokenText src els toks
    Engine.builder.nt nd = n.ctorIdx ∧
    t.nt? = some n ∧
    (∀ k, (view Engine.builder d).isA nd k = (Tree.view text).isA t k) ∧
    Engine.builder.span nd = Ecma.Grammar.tokenSpan els toks t.span.1 t.span.2 ∧
    (∀ cs0, (view Engine.builder d).textIs nd cs0 = (Tree.view text).textIs t cs0) ∧
    (∀ k lt, t = .lex k lt → syn Engine.builder nd = false ∧ (view Engine.builder d).kids nd = [] ∧ (Tree.view text).kids t = []) ∧
    (∀ id ps0 a b kids, t = .node n id ps0 a b kids →
      syn Engine.builder nd = true ∧
      Engine.builder.prod nd = id ∧
      ((view Engine.builder d).kids nd).length = ((Tree.view text).kids t).length ∧
      ∀ (idx : Nat) c_nd c_t,
        ((view Engine.builder d).kids nd)[idx]? = some c_nd →
        ((Tree.view text).kids t)[idx]? = some c_t →
        ∃ n' ps' a' b', a' ≤ b' ∧ b' ≤ toks.length ∧
          PosSynStep cx P toks n' ps' a' b' c_t ∧
          Ecma.Model.NodeRel Engine.Impl st src (Ecma.Grammar.tokenSpan els toks) c_nd c_t) := by
  cases hst with
  | @lex _ _ _ lt tok halts hgetTok hleaf =>
    obtain ⟨hkv, K, hKL⟩ := hleaf
    have hstepL := hKL (max K 1) (Nat.le_max_left K 1)
    obtain ⟨k0, hk0⟩ : ∃ k0, max K 1 = k0 + 1 := ⟨max K 1 - 1, by omega⟩
    rw [hk0] at hstepL
    obtain ⟨idL, kidsL, hltEq⟩ := lex_step_is_node hstepL
    have hrelL := nodeRel_inv_lex (M := Engine.Impl) hrel
    rw [hltEq] at hrelL
    obtain ⟨hntL, _, hspL, hslenL, hsgetL, _, _⟩ := nodeRel_inv_node (M := Engine.Impl) hrelL
    rcases nd with ⟨st0, lo, hi, pid0, nt0, ps0, ks0, txt0⟩
    have hs0 := source_toList_of_nodeRel (txt := txt0) hslenL hsgetL
    dsimp only [Engine.Impl] at hntL hspL
    have ⟨hesBounds, _⟩ := scans_token_elems hScans
    have ⟨_, hgetTokOf⟩ := tokensOf_length_and_get src els
    have hkvB : tok.virt.isNone = true := by simp [hkv]
    have ⟨hcI, hfiltGet⟩ := filter_getElem?_of_getElem?_true (fun x => x.virt.isNone) toks i tok hgetTok hkvB
    rw [htoks] at hfiltGet
    obtain ⟨el, helGet, htokText⟩ := hgetTokOf _ tok hfiltGet
    have ⟨helLt, helLe⟩ := hesBounds el (List.mem_of_getElem? helGet)
    let r := (toks.take i).countP (fun x => x.virt.isNone)
    have hspI : Ecma.Grammar.tokenSpan els toks i (i + 1) = (el.i, el.j) := by
      unfold Ecma.Grammar.tokenSpan
      change (let start := ((els.filter Element.isToken)[r]?.map (·.i)).getD _;
        if r < (toks.take (i + 1)).countP (fun x => x.virt.isNone) then
          (start, ((els.filter Element.isToken)[(toks.take (i + 1)).countP (fun x => x.virt.isNone) - 1]?.map (·.j)).getD start)
        else (start, start)) = (el.i, el.j)
      rw [hcI]
      split
      · rw [Nat.add_sub_cancel, helGet]; rfl
      · dsimp only [r] at *; omega
    have htokLen : tok.text.length = el.j - el.i := by
      rw [htokText]; unfold slice
      rw [List.length_take_of_le (by rw [List.length_drop]; omega)]
    have hspEq : (lo, hi) = (el.i, el.j) := by
      rw [hspI, htokLen] at hspL
      exact hspL.trans (Prod.ext (Nat.add_zero _) (by omega))
    have htxtList : txt0.toArray.toList = slice src el.i el.j := by
      rwa [hspI, htokLen, Nat.add_zero, show el.i + (el.j - el.i) = el.j from by omega] at hs0
    have hsynF : syn Engine.builder (.mk st0 lo hi pid0 nt0 ps0 ks0 txt0) = false := by
      unfold syn; dsimp only [Engine.builder]
      rw [hntL, hasRule_syntactic_eq hok cx n, halts]; rfl
    have hntLex : (Tree.lex i lt).nt? = some n := by rw [hltEq]; rfl
    refine ⟨hntL, hntLex, ?_, ?_, ?_, ?_, fun _ _ _ _ _ h => by cases h⟩
    · intro k
      dsimp only [view, Tree.view, Engine.builder]
      rw [hntL, hntLex]
      apply Bool.eq_iff_iff.mpr
      simp only [beq_iff_eq, Option.some.injEq]
      exact ⟨nt_ctorIdx_inj, fun h => h ▸ rfl⟩
    · dsimp only [Engine.builder, Tree.span]; rw [hspI]; exact hspEq
    · intro cs0
      dsimp only [view, Tree.view, Tree.span, Ecma.Grammar.tokenText, Engine.builder]
      rw [htxtList, hspI]
    · intro _ _ _
      exact ⟨hsynF, by simp [view, hsynF], rfl⟩
  | @node _ _ _ _ m0 kids0 id0 s hsMem _ hpid hseq =>
    obtain ⟨hnt, hprod, hsp, hslen, hsget, hklen, hkids⟩ := nodeRel_inv_node (M := Engine.Impl) hrel
    rcases nd with ⟨st0, lo, hi, pid0, nt0, ps0, ks0, txt0⟩
    have htxtList : txt0.toArray.toList = slice src (Ecma.Grammar.tokenSpan els toks i j).1 (Ecma.Grammar.tokenSpan els toks i j).2 :=
      source_toList_of_nodeRel (txt := txt0) hslen hsget
    dsimp only [Engine.Impl, Engine.Model.kidsOf] at hnt hprod hsp hklen hkids
    have hsynT : syn Engine.builder (.mk st0 lo hi pid0 nt0 ps0 ks0 txt0) = true := by
      unfold syn; dsimp only [Engine.builder]
      rw [hnt, hasRule_syntactic_eq hok cx n]
      cases hL : Ecma.Spec.gl.alts cx .syntactic n with
      | nil => rw [hL] at hsMem; cases hsMem
      | cons _ _ => rfl
    have hchildSteps := posSynSeq_child_step hj hseq
    refine ⟨hnt, rfl, ?_, hsp, ?_, (fun _ _ h => by cases h), ?_⟩
    · intro k
      dsimp only [view, Tree.view, Tree.nt?, Engine.builder]
      rw [hnt]
      apply Bool.eq_iff_iff.mpr
      simp only [beq_iff_eq, Option.some.injEq]
      exact ⟨nt_ctorIdx_inj, fun h => h ▸ rfl⟩
    · intro cs0
      dsimp only [view, Tree.view, Tree.span, Ecma.Grammar.tokenText, Engine.builder]
      rw [htxtList]
    · intro id' ps0' a' b' kids' heq
      injection heq with _ hidEq _ haEq hbEq hkidsEq
      subst hidEq; subst haEq; subst hbEq; subst hkidsEq
      have hkListEq : (ks0.toList.filterMap Prod.snd) = (ks0.filterMap Prod.snd).toList :=
        (Array.toList_filterMap).symm
      injection hklen with hszInt
      have hlenEq : (ks0.toList.filterMap Prod.snd).length = (kids0.filter fun x => !x.isLeaf).length := by
        rw [hkListEq, Array.length_toList]; omega
      refine ⟨hsynT, hprod, ?_, ?_⟩
      · dsimp only [view, Tree.view]
        rw [hsynT]
        dsimp only [Engine.builder]
        exact hlenEq
      · intro idx c_nd c_t hcNd hcT
        dsimp only [view, Tree.view] at hcNd hcT
        rw [hsynT] at hcNd
        dsimp only [Engine.builder] at hcNd
        rw [hkListEq, Array.getElem?_toList] at hcNd
        have hseqGet : Engine.Impl.seqGet (ks0.filterMap Prod.snd) (Engine.Impl.ofNat idx) = some c_nd := by
          rw [impl_seqGet_nat]; exact hcNd
        have hrelC := hkids idx c_t c_nd hcT hseqGet
        obtain ⟨n', ps', a0, b0, _, hab0, _, hb0L, hstC⟩ := hchildSteps c_t (List.mem_of_getElem? hcT)
        exact ⟨n', ps', a0, b0, hab0, hb0L, hstC, hrelC⟩

/-! ## `oneNode`, `directive`, `prologueScan`, `bodyOf`, `strictCode`, and `sloppyOk` equivalence -/

private theorem oneNode_of_const_spans (hok : parseTablesOk = true) {cx : Ctx} {P : CodePrims}
    {src : List Nat} {els : List Element} {toks : List Token} {st d : Nat}
    (hScans : Scans Ecma.Spec.gl cx P src els)
    (htoks : toks.filter (fun x => x.virt.isNone) = tokensOf src els)
    {i j : Nat} (hj : j ≤ toks.length)
    (hle1 : (slice toks i j).countP (fun x => x.virt.isNone) ≤ 1) :
    ∀ (d0 : Nat) {n : NT} {ps : List Param} {nd : Engine.Model.Node} {t : Tree},
      ((Ecma.Spec.gl.alts cx .syntactic n).isEmpty = true ∨ exprUnitNTs.contains n = true) →
      PosSynStep cx P toks n ps i j t →
      Ecma.Model.NodeRel Engine.Impl st src (Ecma.Grammar.tokenSpan els toks) nd t →
      oneNode (view Engine.builder d) .StringLiteral (Ecma.Grammar.tokenSpan els toks i j) d0 nd =
        oneNode (Tree.view (Ecma.Grammar.tokenText src els toks)) .StringLiteral (i, j) d0 t
  | 0, _, _, _, _, _, _, _ => rfl
  | d0 + 1, n, ps, nd, t, hn, hst, hrel => by
    have ⟨_, _, hisA, hspNd, _, hlex, hnode⟩ := nodeRel_syn_props (d := d) hok hScans htoks hj hst hrel
    have ⟨hspT, hunitKids⟩ := exprUnit_oneReal_all_spans_eq hok t hj hn hle1 hst
    unfold oneNode
    have hv1Sp : ((view Engine.builder d).span nd == Ecma.Grammar.tokenSpan els toks i j) = true := by
      dsimp only [view]; rw [hspNd, hspT]; exact BEq.rfl
    have hv2Sp : ((Tree.view (Ecma.Grammar.tokenText src els toks)).span t == (i, j)) = true := by
      dsimp only [Tree.view]; rw [hspT]; exact BEq.rfl
    rw [hv1Sp, hv2Sp, Bool.true_and, Bool.true_and, hisA .StringLiteral]
    congr 1
    cases t with
    | leaf _ _ => cases hst
    | lex k lt =>
      obtain ⟨_, hkids1, hkids2⟩ := hlex k lt rfl
      rw [hkids1, hkids2]; rfl
    | node nt id0 ps0 a0 b0 kids0 =>
      have hnEq : nt = n := by cases hst; rfl
      subst nt
      obtain ⟨_, _, hlenK, hkidsRel⟩ := hnode id0 ps0 a0 b0 kids0 rfl
      apply Bool.eq_iff_iff.mpr
      simp only [List.any_eq_true]
      constructor
      · rintro ⟨c_nd, hcNdMem, hone1⟩
        obtain ⟨idx, hidxLt, rfl⟩ := List.getElem_of_mem hcNdMem
        have hidxLt2 : idx < ((Tree.view (Ecma.Grammar.tokenText src els toks)).kids (.node n id0 ps0 a0 b0 kids0)).length :=
          hlenK ▸ hidxLt
        let c_t := ((Tree.view (Ecma.Grammar.tokenText src els toks)).kids (.node n id0 ps0 a0 b0 kids0))[idx]'hidxLt2
        obtain ⟨_, _, _, _, _, _, _, hrelC⟩ := hkidsRel idx _ c_t (List.getElem?_eq_getElem hidxLt) (List.getElem?_eq_getElem hidxLt2)
        obtain ⟨nC, psC, hnC, hstC⟩ := hunitKids c_t (List.getElem_mem hidxLt2)
        have heq := oneNode_of_const_spans (d := d) hok hScans htoks hj hle1 d0 hnC hstC hrelC
        exact ⟨c_t, List.getElem_mem hidxLt2, heq ▸ hone1⟩
      · rintro ⟨c_t, hcTMem, hone2⟩
        obtain ⟨idx, hidxLt2, rfl⟩ := List.getElem_of_mem hcTMem
        have hidxLt1 : idx < ((view Engine.builder d).kids nd).length := hlenK.symm ▸ hidxLt2
        let c_nd := ((view Engine.builder d).kids nd)[idx]'hidxLt1
        obtain ⟨_, _, _, _, _, _, _, hrelC⟩ := hkidsRel idx c_nd _ (List.getElem?_eq_getElem hidxLt1) (List.getElem?_eq_getElem hidxLt2)
        obtain ⟨nC, psC, hnC, hstC⟩ := hunitKids _ (List.getElem_mem hidxLt2)
        have heq := oneNode_of_const_spans (d := d) hok hScans htoks hj hle1 d0 hnC hstC hrelC
        exact ⟨c_nd, List.getElem_mem hidxLt1, heq.symm ▸ hone2⟩

private theorem oneNode_false_of_two_real (hok : parseTablesOk = true) {cx : Ctx} {P : CodePrims}
    {src : List Nat} {els : List Element} {toks : List Token} {st d : Nat}
    (hScans : Scans Ecma.Spec.gl cx P src els)
    (htoks : toks.filter (fun x => x.virt.isNone) = tokensOf src els)
    {i j : Nat} (hij : i ≤ j) (hj : j ≤ toks.length)
    (htwo : 2 ≤ (slice toks i j).countP (fun x => x.virt.isNone)) :
    ∀ (d0 : Nat) {n : NT} {ps : List Param} {a b : Nat} {nd : Engine.Model.Node} {t : Tree},
      b ≤ toks.length →
      PosSynStep cx P toks n ps a b t →
      Ecma.Model.NodeRel Engine.Impl st src (Ecma.Grammar.tokenSpan els toks) nd t →
      oneNode (view Engine.builder d) .StringLiteral (Ecma.Grammar.tokenSpan els toks i j) d0 nd = false ∧
      oneNode (Tree.view (Ecma.Grammar.tokenText src els toks)) .StringLiteral (i, j) d0 t = false
  | 0, _, _, _, _, _, _, _, _, _ => ⟨rfl, rfl⟩
  | d0 + 1, n, ps, a, b, nd, t, hb, hst, hrel => by
    have ⟨_, hntT, hisA, hspNd, _, hlex, hnode⟩ := nodeRel_syn_props (d := d) hok hScans htoks hb hst hrel
    have ⟨hrSynStr, _, _, _, _, _, _, _, _⟩ := fast_invariants hok cx
    have hnotStrNode : ∀ {m : NT} {s : Src}, s ∈ Ecma.Spec.gl.alts cx .syntactic m → m ≠ .StringLiteral := by
      intro m s hs heq
      subst heq
      have hne : Ecma.Spec.gl.alts cx .syntactic .StringLiteral ≠ [] := fun hnil => by rw [hnil] at hs; cases hs
      have hmemR := syn_nonempty_in_rulesOf hok hne
      have hr := ruleNt_of_rulesOf hok hmemR
      rw [hrSynStr] at hr; cases hr
    cases hst with
    | @lex _ _ _ lt tok halts hgetTok hleaf =>
      unfold oneNode
      obtain ⟨_, hkids1, hkids2⟩ := hlex a lt rfl
      simp only [hkids1, hkids2, List.any_nil, Bool.or_false]
      constructor
      · by_cases hisStr : (view Engine.builder d).isA nd .StringLiteral = true
        · have hspNe := tokenSpan_ne_of_two_real hScans htoks hij hj htwo hgetTok hleaf.1
          dsimp only [view, Tree.span] at hspNd ⊢
          rw [hspNd]
          simp [beq_eq_false_iff_ne.mpr hspNe]
        · simp [hisStr]
      · by_cases hspEq : ((Tree.view (Ecma.Grammar.tokenText src els toks)).span (.lex a lt) == (i, j)) = true
        · dsimp only [Tree.view, Tree.span] at hspEq
          rw [beq_iff_eq] at hspEq
          injection hspEq with hiEq hjEq
          subst hiEq; subst hjEq
          have hdrop : toks.drop a = tok :: toks.drop (a + 1) := by
            obtain ⟨ha, hv⟩ := List.getElem?_eq_some_iff.mp hgetTok
            rw [List.drop_eq_getElem_cons ha, hv]
          have hsc : slice toks a (a + 1) = [tok] := (slice_singleton_iff (by omega) hj).mpr ⟨rfl, hgetTok, hdrop⟩
          rw [hsc, List.countP_cons, List.countP_nil] at htwo
          split at htwo <;> omega
        · simp [hspEq]
    | @node _ _ _ _ m0 kids0 id0 s hsMem _ _ _ =>
      have hnNeStr : n ≠ .StringLiteral := hnotStrNode hsMem
      have hisAF2 : (Tree.view (Ecma.Grammar.tokenText src els toks)).isA (.node n id0 ps a b kids0) .StringLiteral = false := by
        dsimp only [Tree.view, Tree.nt?]
        exact beq_eq_false_iff_ne.mpr (fun h => hnNeStr (Option.some.inj h))
      have hisAF1 : (view Engine.builder d).isA nd .StringLiteral = false := by rw [hisA]; exact hisAF2
      obtain ⟨_, _, hlenK, hkidsRel⟩ := hnode id0 ps a b kids0 rfl
      unfold oneNode
      rw [hisAF1, hisAF2, Bool.false_or, Bool.false_or]
      have hk1F : ((view Engine.builder d).kids nd).any
          (oneNode (view Engine.builder d) .StringLiteral (Ecma.Grammar.tokenSpan els toks i j) d0) = false := by
        rw [List.any_eq_false]
        intro c_nd hcNdMem
        obtain ⟨idx, hidxLt1, rfl⟩ := List.getElem_of_mem hcNdMem
        have hidxLt2 : idx < ((Tree.view (Ecma.Grammar.tokenText src els toks)).kids (.node n id0 ps a b kids0)).length :=
          hlenK ▸ hidxLt1
        let c_t := ((Tree.view (Ecma.Grammar.tokenText src els toks)).kids (.node n id0 ps a b kids0))[idx]'hidxLt2
        obtain ⟨_, _, _, _, _, hbC, hstC, hrelC⟩ :=
          hkidsRel idx _ c_t (List.getElem?_eq_getElem hidxLt1) (List.getElem?_eq_getElem hidxLt2)
        exact Bool.eq_false_iff.mp (oneNode_false_of_two_real (d := d) hok hScans htoks hij hj htwo d0 hbC hstC hrelC).1
      have hk2F : ((Tree.view (Ecma.Grammar.tokenText src els toks)).kids (.node n id0 ps a b kids0)).any
          (oneNode (Tree.view (Ecma.Grammar.tokenText src els toks)) .StringLiteral (i, j) d0) = false := by
        rw [List.any_eq_false]
        intro c_t hcTMem
        obtain ⟨idx, hidxLt2, rfl⟩ := List.getElem_of_mem hcTMem
        have hidxLt1 : idx < ((view Engine.builder d).kids nd).length := hlenK.symm ▸ hidxLt2
        let c_nd := ((view Engine.builder d).kids nd)[idx]'hidxLt1
        obtain ⟨_, _, _, _, _, hbC, hstC, hrelC⟩ :=
          hkidsRel idx c_nd _ (List.getElem?_eq_getElem hidxLt1) (List.getElem?_eq_getElem hidxLt2)
        exact Bool.eq_false_iff.mp (oneNode_false_of_two_real (d := d) hok hScans htoks hij hj htwo d0 hbC hstC hrelC).2
      rw [hk1F, hk2F, Bool.and_false, Bool.and_false]
      exact ⟨rfl, rfl⟩

private theorem oneNode_expression_eq (hok : parseTablesOk = true) {cx : Ctx} {P : CodePrims}
    {src : List Nat} {els : List Element} {toks : List Token} {st d : Nat}
    (hScans : Scans Ecma.Spec.gl cx P src els)
    (htoks : toks.filter (fun x => x.virt.isNone) = tokensOf src els)
    (d0 : Nat) {ps : List Param} {i j : Nat} {nd_e : Engine.Model.Node} {e : Tree}
    (hj : j ≤ toks.length)
    (hst : PosSynStep cx P toks .Expression ps i j e)
    (hrel : Ecma.Model.NodeRel Engine.Impl st src (Ecma.Grammar.tokenSpan els toks) nd_e e) :
    oneNode (view Engine.builder d) .StringLiteral ((view Engine.builder d).span nd_e) d0 nd_e =
      oneNode (Tree.view (Ecma.Grammar.tokenText src els toks)) .StringLiteral e.span d0 e := by
  have ⟨_, _, _, hspNd, _, _, _⟩ := nodeRel_syn_props (d := d) hok hScans htoks hj hst hrel
  have heSp : e.span = (i, j) := by cases hst <;> rfl
  have hspV : (view Engine.builder d).span nd_e = Ecma.Grammar.tokenSpan els toks i j := by
    dsimp only [view]; rw [hspNd, heSp]
  rw [hspV, heSp]
  by_cases hle1 : (slice toks i j).countP (fun x => x.virt.isNone) ≤ 1
  · exact oneNode_of_const_spans hok hScans htoks hj hle1 d0 (Or.inr (by decide)) hst hrel
  · have hij := posSynStep_le hst
    have ⟨hf1, hf2⟩ := oneNode_false_of_two_real (d := d) hok hScans htoks hij hj (by omega) d0 hj hst hrel
    rw [hf1, hf2]

private theorem singleton_kids_inv {α β : Type} {xs : List α} {ys : List β}
    (hlen : xs.length = ys.length) :
    (xs = [] ∧ ys = []) ∨
    (∃ x y, xs = [x] ∧ ys = [y] ∧ xs[0]? = some x ∧ ys[0]? = some y) ∨
    (2 ≤ xs.length ∧ 2 ≤ ys.length) := by
  cases xs with
  | nil =>
    cases ys with
    | nil => exact Or.inl ⟨rfl, rfl⟩
    | cons _ _ => simp at hlen
  | cons x xs' =>
    cases ys with
    | nil => simp at hlen
    | cons y ys' =>
      cases xs' with
      | nil =>
        cases ys' with
        | nil => exact Or.inr (Or.inl ⟨x, y, rfl, rfl, rfl, rfl⟩)
        | cons _ _ => simp at hlen
      | cons _ _ =>
        cases ys' with
        | nil => simp at hlen
        | cons _ _ => exact Or.inr (Or.inr ⟨by simp, by simp⟩)

private theorem directive_sim_eq (hok : parseTablesOk = true) {cx : Ctx} {P : CodePrims}
    {src : List Nat} {els : List Element} {toks : List Token} {st d : Nat}
    (hScans : Scans Ecma.Spec.gl cx P src els)
    (htoks : toks.filter (fun x => x.virt.isNone) = tokensOf src els)
    (d0 : Nat) {n : NT} {ps : List Param} {i j : Nat} {nd_item : Engine.Model.Node} {item : Tree}
    (hj : j ≤ toks.length)
    (hst : PosSynStep cx P toks n ps i j item)
    (hrel : Ecma.Model.NodeRel Engine.Impl st src (Ecma.Grammar.tokenSpan els toks) nd_item item) :
    directive (view Engine.builder d) d0 nd_item =
      directive (Tree.view (Ecma.Grammar.tokenText src els toks)) d0 item := by
  let V1 := view Engine.builder d
  let V2 := Tree.view (Ecma.Grammar.tokenText src els toks)
  have stepKids : ∀ {n0 ps0 a0 b0 nd0 t0}, b0 ≤ toks.length →
      PosSynStep cx P toks n0 ps0 a0 b0 t0 →
      Ecma.Model.NodeRel Engine.Impl st src (Ecma.Grammar.tokenSpan els toks) nd0 t0 →
      (V1.kids nd0 = [] ∧ V2.kids t0 = []) ∨
      (∃ c_nd c_t n1 ps1 a1 b1, V1.kids nd0 = [c_nd] ∧ V2.kids t0 = [c_t] ∧
        b1 ≤ toks.length ∧ PosSynStep cx P toks n1 ps1 a1 b1 c_t ∧
        Ecma.Model.NodeRel Engine.Impl st src (Ecma.Grammar.tokenSpan els toks) c_nd c_t) ∨
      (2 ≤ (V1.kids nd0).length ∧ 2 ≤ (V2.kids t0).length) := by
    intro n0 ps0 a0 b0 nd0 t0 hb0 hst0 hrel0
    have ⟨_, _, _, _, _, hlex0, hnode0⟩ := nodeRel_syn_props (d := d) hok hScans htoks hb0 hst0 hrel0
    cases t0 with
    | leaf _ _ => cases hst0
    | lex k0 lt0 =>
      obtain ⟨_, hk1, hk2⟩ := hlex0 k0 lt0 rfl
      exact Or.inl ⟨hk1, hk2⟩
    | node nt0 id0 ps0' i0 j0 kids0 =>
      have hnEq : nt0 = n0 := by cases hst0; rfl
      subst nt0
      obtain ⟨_, _, hlen0, hkids0⟩ := hnode0 id0 ps0' i0 j0 kids0 rfl
      rcases singleton_kids_inv hlen0 with ⟨h1, h2⟩ | ⟨x, y, hx, hy, hg1, hg2⟩ | h2ge
      · exact Or.inl ⟨h1, h2⟩
      · obtain ⟨n1, ps1, a1, b1, _, hb1, hst1, hrel1⟩ := hkids0 0 x y hg1 hg2
        exact Or.inr (Or.inl ⟨x, y, n1, ps1, a1, b1, hx, hy, hb1, hst1, hrel1⟩)
      · exact Or.inr (Or.inr h2ge)
  unfold directive
  rcases stepKids hj hst hrel with ⟨h1, h2⟩ | ⟨s_nd, s_t, nS, psS, aS, bS, hk1, hk2, hbS, hstS, hrelS⟩ | ⟨hg1, hg2⟩
  · dsimp only [V1, V2] at h1 h2; rw [h1, h2]
  · dsimp only [V1, V2] at hk1 hk2; rw [hk1, hk2]
    have ⟨_, _, hisAS, _, _, _, _⟩ := nodeRel_syn_props (d := d) hok hScans htoks hbS hstS hrelS
    dsimp only
    rw [hisAS .Statement]
    cases hSt : (Tree.view (Ecma.Grammar.tokenText src els toks)).isA s_t .Statement with
    | false => rfl
    | true =>
      simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      rcases stepKids hbS hstS hrelS with ⟨h1, h2⟩ | ⟨es_nd, es_t, nE, psE, aE, bE, hek1, hek2, hbE, hstE, hrelE⟩ | ⟨hgE1, hgE2⟩
      · dsimp only [V1, V2] at h1 h2; rw [h1, h2]
      · dsimp only [V1, V2] at hek1 hek2; rw [hek1, hek2]
        have ⟨_, _, hisAE, _, _, _, _⟩ := nodeRel_syn_props (d := d) hok hScans htoks hbE hstE hrelE
        dsimp only
        rw [hisAE .ExpressionStatement]
        cases hEs : (Tree.view (Ecma.Grammar.tokenText src els toks)).isA es_t .ExpressionStatement with
        | false => rfl
        | true =>
          simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
          rcases stepKids hbE hstE hrelE with ⟨h1, h2⟩ | ⟨e_nd, e_t, nX, psX, aX, bX, hxk1, hxk2, hbX, hstX, hrelX⟩ | ⟨hgX1, hgX2⟩
          · dsimp only [V1, V2] at h1 h2; rw [h1, h2]
          · dsimp only [V1, V2] at hxk1 hxk2; rw [hxk1, hxk2]
            have ⟨_, hntX, hisAX, _, htxtX, _, _⟩ := nodeRel_syn_props (d := d) hok hScans htoks hbX hstX hrelX
            dsimp only
            rw [hisAX .Expression]
            cases hEx : (Tree.view (Ecma.Grammar.tokenText src els toks)).isA e_t .Expression with
            | false => rfl
            | true =>
              have hnXEq : nX = .Expression := by
                dsimp only [Tree.view] at hEx
                rw [hntX, beq_iff_eq, Option.some.injEq] at hEx
                exact hEx
              subst hnXEq
              have honeEq := oneNode_expression_eq (d := d) hok hScans htoks d0 hbX hstX hrelX
              have huseEq : useStrictTexts.any ((view Engine.builder d).textIs e_nd) =
                  useStrictTexts.any ((Tree.view (Ecma.Grammar.tokenText src els toks)).textIs e_t) :=
                list_any_congr (fun cs0 _ => htxtX cs0)
              have honeEq' : oneNode (view Engine.builder d) .StringLiteral ((view Engine.builder d).span e_nd) d0 e_nd =
                  oneNode (Tree.view (Ecma.Grammar.tokenText src els toks)) .StringLiteral
                    ((Tree.view (Ecma.Grammar.tokenText src els toks)).span e_t) d0 e_t := honeEq
              simp only [Bool.true_and, honeEq', huseEq]
          · dsimp only [V1, V2] at hgX1 hgX2
            cases hxk1 : (view Engine.builder d).kids es_nd with
            | nil => rw [hxk1] at hgX1; simp at hgX1
            | cons _ tl1 =>
              cases tl1 with
              | nil => rw [hxk1] at hgX1; simp at hgX1
              | cons _ _ =>
                cases hxk2 : (Tree.view (Ecma.Grammar.tokenText src els toks)).kids es_t with
                | nil => rfl
                | cons _ tl2 =>
                  cases tl2 with
                  | nil => rw [hxk2] at hgX2; simp at hgX2
                  | cons _ _ => rfl
      · dsimp only [V1, V2] at hgE1 hgE2
        cases hek1 : (view Engine.builder d).kids s_nd with
        | nil => rw [hek1] at hgE1; simp at hgE1
        | cons _ tl1 =>
          cases tl1 with
          | nil => rw [hek1] at hgE1; simp at hgE1
          | cons _ _ =>
            cases hek2 : (Tree.view (Ecma.Grammar.tokenText src els toks)).kids s_t with
            | nil => rfl
            | cons _ tl2 =>
              cases tl2 with
              | nil => rw [hek2] at hgE2; simp at hgE2
              | cons _ _ => rfl
  · dsimp only [V1, V2] at hg1 hg2
    cases hk1 : (view Engine.builder d).kids nd_item with
    | nil => rw [hk1] at hg1; simp at hg1
    | cons _ tl1 =>
      cases tl1 with
      | nil => rw [hk1] at hg1; simp at hg1
      | cons _ _ =>
        cases hk2 : (Tree.view (Ecma.Grammar.tokenText src els toks)).kids item with
        | nil => rfl
        | cons _ tl2 =>
          cases tl2 with
          | nil => rw [hk2] at hg2; simp at hg2
          | cons _ _ => rfl

private theorem findSome_zip_eq {α β γ : Type} {xs : List α} {ys : List β}
    {f : α → Option γ} {g : β → Option γ}
    (hlen : xs.length = ys.length)
    (heq : ∀ (idx : Nat) x y, xs[idx]? = some x → ys[idx]? = some y → f x = g y) :
    xs.findSome? f = ys.findSome? g := by
  induction xs generalizing ys with
  | nil =>
    cases ys with
    | nil => rfl
    | cons _ _ => simp at hlen
  | cons x xs ih =>
    cases ys with
    | nil => simp at hlen
    | cons y ys =>
      simp only [List.findSome?_cons, heq 0 x y rfl rfl]
      cases g y with
      | some _ => rfl
      | none =>
        exact ih (by simp at hlen; omega) (fun idx a b ha hb => heq (idx + 1) a b (by simpa using ha) (by simpa using hb))

private theorem prologueScan_sim_eq (hok : parseTablesOk = true) {cx : Ctx} {P : CodePrims}
    {src : List Nat} {els : List Element} {toks : List Token} {st d : Nat}
    (hScans : Scans Ecma.Spec.gl cx P src els)
    (htoks : toks.filter (fun x => x.virt.isNone) = tokensOf src els) :
    ∀ (d0 : Nat) {n : NT} {ps : List Param} {i j : Nat} {nd : Engine.Model.Node} {t : Tree},
      j ≤ toks.length →
      PosSynStep cx P toks n ps i j t →
      Ecma.Model.NodeRel Engine.Impl st src (Ecma.Grammar.tokenSpan els toks) nd t →
      prologueScan (view Engine.builder d) d0 nd =
        prologueScan (Tree.view (Ecma.Grammar.tokenText src els toks)) d0 t
  | 0, _, _, _, _, _, _, _, _, _ => rfl
  | d0 + 1, n, ps, i, j, nd, t, hj, hst, hrel => by
    have ⟨_, _, hisA, _, _, hlex, hnode⟩ := nodeRel_syn_props (d := d) hok hScans htoks hj hst hrel
    unfold prologueScan
    rw [hisA .StatementListItem]
    cases hSli : (Tree.view (Ecma.Grammar.tokenText src els toks)).isA t .StatementListItem with
    | true =>
      simp only [↓reduceIte]
      rw [directive_sim_eq (d := d) hok hScans htoks d0 hj hst hrel]
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      cases t with
      | leaf _ _ => cases hst
      | lex k0 lt0 =>
        obtain ⟨_, hk1, hk2⟩ := hlex k0 lt0 rfl
        rw [hk1, hk2]; rfl
      | node nt id0 ps0 a0 b0 kids0 =>
        have hnEq : nt = n := by cases hst; rfl
        subst nt
        obtain ⟨_, _, hlenK, hkidsRel⟩ := hnode id0 ps0 a0 b0 kids0 rfl
        exact findSome_zip_eq hlenK fun idx c_nd c_t hcNd hcT => by
          obtain ⟨_, _, _, _, _, hbC, hstC, hrelC⟩ := hkidsRel idx c_nd c_t hcNd hcT
          exact prologueScan_sim_eq hok hScans htoks d0 hbC hstC hrelC

private theorem prologueStrict_sim_eq (hok : parseTablesOk = true) {cx : Ctx} {P : CodePrims}
    {src : List Nat} {els : List Element} {toks : List Token} {st d : Nat}
    (hScans : Scans Ecma.Spec.gl cx P src els)
    (htoks : toks.filter (fun x => x.virt.isNone) = tokensOf src els)
    {n : NT} {ps : List Param} {i j : Nat} {nd : Engine.Model.Node} {t : Tree}
    (hj : j ≤ toks.length)
    (hd : synHeight t ≤ d)
    (hst : PosSynStep cx P toks n ps i j t)
    (hrel : Ecma.Model.NodeRel Engine.Impl st src (Ecma.Grammar.tokenSpan els toks) nd t) :
    prologueStrict (view Engine.builder d) nd =
      prologueStrict (Tree.view (Ecma.Grammar.tokenText src els toks)) t := by
  unfold prologueStrict
  have h1 : (view Engine.builder d).height nd = d := rfl
  have h2 : (Tree.view (Ecma.Grammar.tokenText src els toks)).height t = t.height := rfl
  rw [h1, h2, prologueScan_sim_eq (d := d) hok hScans htoks d hj hst hrel]
  rw [prologueScan_tree_stab _ t hd (synHeight_le_height t)]

private theorem bodyOf_sim (hok : parseTablesOk = true) {cx : Ctx} {P : CodePrims}
    {src : List Nat} {els : List Element} {toks : List Token} {st d : Nat}
    (hScans : Scans Ecma.Spec.gl cx P src els)
    (htoks : toks.filter (fun x => x.virt.isNone) = tokensOf src els) :
    ∀ (d0 : Nat) {n : NT} {ps : List Param} {i j : Nat} {nd : Engine.Model.Node} {t : Tree},
      j ≤ toks.length →
      PosSynStep cx P toks n ps i j t →
      Ecma.Model.NodeRel Engine.Impl st src (Ecma.Grammar.tokenSpan els toks) nd t →
      (bodyOf (view Engine.builder d) d0 nd = none ∧
       bodyOf (Tree.view (Ecma.Grammar.tokenText src els toks)) d0 t = none) ∨
      (∃ b_nd b_t nB psB aB bB,
        bodyOf (view Engine.builder d) d0 nd = some b_nd ∧
        bodyOf (Tree.view (Ecma.Grammar.tokenText src els toks)) d0 t = some b_t ∧
        bB ≤ toks.length ∧
        PosSynStep cx P toks nB psB aB bB b_t ∧
        Ecma.Model.NodeRel Engine.Impl st src (Ecma.Grammar.tokenSpan els toks) b_nd b_t)
  | 0, _, _, _, _, _, _, _, _, _ => Or.inl ⟨rfl, rfl⟩
  | d0 + 1, n, ps, i, j, nd, t, hj, hst, hrel => by
    have ⟨_, _, hisA, _, _, hlex, hnode⟩ := nodeRel_syn_props (d := d) hok hScans htoks hj hst hrel
    unfold bodyOf
    rw [hisA .FunctionBody]
    cases hFb : (Tree.view (Ecma.Grammar.tokenText src els toks)).isA t .FunctionBody with
    | true =>
      simp only [↓reduceIte]
      exact Or.inr ⟨nd, t, n, ps, i, j, rfl, rfl, hj, hst, hrel⟩
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      cases t with
      | leaf _ _ => cases hst
      | lex k0 lt0 =>
        obtain ⟨_, hk1, hk2⟩ := hlex k0 lt0 rfl
        rw [hk1, hk2]; exact Or.inl ⟨rfl, rfl⟩
      | node nt id0 ps0 a0 b0 kids0 =>
        have hnEq : nt = n := by cases hst; rfl
        subst nt
        obtain ⟨_, _, hlenK, hkidsRel⟩ := hnode id0 ps0 a0 b0 kids0 rfl
        let ks1 := (view Engine.builder d).kids nd
        let ks2 := (Tree.view (Ecma.Grammar.tokenText src els toks)).kids (.node n id0 ps0 a0 b0 kids0)
        have hlen12 : ks1.length = ks2.length := hlenK
        have hzipBody : ∀ (m : Nat),
            m ≤ ks1.length →
            ((ks1.drop m).findSome? (fun k => if (view Engine.builder d).isIn bodyPath k then bodyOf (view Engine.builder d) d0 k else none) = none ∧
             (ks2.drop m).findSome? (fun k => if (Tree.view (Ecma.Grammar.tokenText src els toks)).isIn bodyPath k then bodyOf (Tree.view (Ecma.Grammar.tokenText src els toks)) d0 k else none) = none) ∨
            (∃ b_nd b_t nB psB aB bB,
              (ks1.drop m).findSome? (fun k => if (view Engine.builder d).isIn bodyPath k then bodyOf (view Engine.builder d) d0 k else none) = some b_nd ∧
              (ks2.drop m).findSome? (fun k => if (Tree.view (Ecma.Grammar.tokenText src els toks)).isIn bodyPath k then bodyOf (Tree.view (Ecma.Grammar.tokenText src els toks)) d0 k else none) = some b_t ∧
              bB ≤ toks.length ∧
              PosSynStep cx P toks nB psB aB bB b_t ∧
              Ecma.Model.NodeRel Engine.Impl st src (Ecma.Grammar.tokenSpan els toks) b_nd b_t) := by
          intro m hm
          induction hrem : ks1.length - m generalizing m with
          | zero =>
            have hm1 : ks1.length ≤ m := by omega
            have hm2 : ks2.length ≤ m := by omega
            rw [List.drop_of_length_le hm1, List.drop_of_length_le hm2]
            exact Or.inl ⟨rfl, rfl⟩
          | succ rem ih =>
            have hmLt1 : m < ks1.length := by omega
            have hmLt2 : m < ks2.length := by omega
            rw [List.drop_eq_getElem_cons hmLt1, List.drop_eq_getElem_cons hmLt2]
            simp only [List.findSome?_cons]
            obtain ⟨nC, psC, aC, bC, _, hbC, hstC, hrelC⟩ :=
              hkidsRel m ks1[m] ks2[m] (List.getElem?_eq_getElem hmLt1) (List.getElem?_eq_getElem hmLt2)
            have ⟨_, _, hisAC, _, _, _, _⟩ := nodeRel_syn_props (d := d) hok hScans htoks hbC hstC hrelC
            have hisInEq : (view Engine.builder d).isIn bodyPath ks1[m] =
                (Tree.view (Ecma.Grammar.tokenText src els toks)).isIn bodyPath ks2[m] :=
              list_any_congr (fun u _ => hisAC u)
            rw [hisInEq]
            by_cases hIn : (Tree.view (Ecma.Grammar.tokenText src els toks)).isIn bodyPath ks2[m] = true
            · simp only [hIn, ↓reduceIte]
              rcases bodyOf_sim hok hScans htoks d0 hbC hstC hrelC with ⟨hn1, hn2⟩ | ⟨b_nd, b_t, nB, psB, aB, bB, hs1, hs2, hbB, hstB, hrelB⟩
              · rw [hn1, hn2]; exact ih (m + 1) (by omega) (by omega)
              · rw [hs1, hs2]; exact Or.inr ⟨b_nd, b_t, nB, psB, aB, bB, rfl, rfl, hbB, hstB, hrelB⟩
            · simp only [hIn, Bool.false_eq_true, ↓reduceIte]
              exact ih (m + 1) (by omega) (by omega)
        simpa using hzipBody 0 (Nat.zero_le _)

private theorem bodyStrict_sim_eq (hok : parseTablesOk = true) {cx : Ctx} {P : CodePrims}
    {src : List Nat} {els : List Element} {toks : List Token} {st d : Nat}
    (hScans : Scans Ecma.Spec.gl cx P src els)
    (htoks : toks.filter (fun x => x.virt.isNone) = tokensOf src els)
    {n : NT} {ps : List Param} {i j : Nat} {nd : Engine.Model.Node} {t : Tree}
    (hj : j ≤ toks.length)
    (hd : synHeight t ≤ d)
    (hst : PosSynStep cx P toks n ps i j t)
    (hrel : Ecma.Model.NodeRel Engine.Impl st src (Ecma.Grammar.tokenSpan els toks) nd t) :
    bodyStrict (view Engine.builder d) nd =
      bodyStrict (Tree.view (Ecma.Grammar.tokenText src els toks)) t := by
  unfold bodyStrict
  have h1 : (view Engine.builder d).height nd = d := rfl
  have h2 : (Tree.view (Ecma.Grammar.tokenText src els toks)).height t = t.height := rfl
  rw [h1, h2]
  have ⟨hstab, hleB⟩ := bodyOf_tree_stab_and_le (Ecma.Grammar.tokenText src els toks) t hd (synHeight_le_height t)
  rw [← hstab]
  rcases bodyOf_sim (d := d) hok hScans htoks d hj hst hrel with ⟨hn1, hn2⟩ | ⟨b_nd, b_t, nB, psB, aB, bB, hs1, hs2, hbB, hstB, hrelB⟩
  · rw [hn1, hn2]; rfl
  · rw [hs1, hs2]
    simp only [Option.any_some]
    exact prologueStrict_sim_eq hok hScans htoks hbB (Nat.le_trans (hleB b_t hs2) hd) hstB hrelB

/-- Pairwise relation over two lists of equal length. -/
inductive PairRel {α β : Type} (R : α → β → Prop) : List α → List β → Prop where
  | nil : PairRel R [] []
  | cons {x : α} {y : β} {xs : List α} {ys : List β} : R x y → PairRel R xs ys → PairRel R (x :: xs) (y :: ys)

private theorem pairRel_append {α β : Type} {R : α → β → Prop} {xs1 xs2 : List α} {ys1 ys2 : List β}
    (h1 : PairRel R xs1 ys1) (h2 : PairRel R xs2 ys2) : PairRel R (xs1 ++ xs2) (ys1 ++ ys2) := by
  induction h1 with
  | nil => exact h2
  | cons hxy _ ih => exact .cons hxy ih

private theorem pairRel_reverse {α β : Type} {R : α → β → Prop} {xs : List α} {ys : List β}
    (h : PairRel R xs ys) : PairRel R xs.reverse ys.reverse := by
  induction h with
  | nil => exact .nil
  | cons hxy _ ih =>
    rw [List.reverse_cons, List.reverse_cons]
    exact pairRel_append ih (.cons hxy .nil)

/-- Node-pair invariant along an ancestor path, with `synHeight ≤ d`. -/
def PathRel (cx : Ctx) (P : CodePrims) (src : List Nat) (els : List Element) (toks : List Token)
    (st d : Nat) (nd : Engine.Model.Node) (t : Tree) : Prop :=
  synHeight t ≤ d ∧
  ∃ n ps a b, b ≤ toks.length ∧
    PosSynStep cx P toks n ps a b t ∧
    Ecma.Model.NodeRel Engine.Impl st src (Ecma.Grammar.tokenSpan els toks) nd t

private theorem takeWhile_any_zip {α β : Type} {p1 : α → Bool} {p2 : β → Bool}
    {q1 : α → Bool} {q2 : β → Bool} {xs : List α} {ys : List β}
    (hr : PairRel (fun x y => p1 x = p2 y ∧ q1 x = q2 y) xs ys) :
    (xs.takeWhile p1).any q1 = (ys.takeWhile p2).any q2 := by
  induction hr with
  | nil => rfl
  | @cons x y xs ys hxy _ ih =>
    simp only [List.takeWhile_cons, hxy.1]
    cases p2 y with
    | false => rfl
    | true => simp [List.any_cons, hxy.2, ih]

private theorem pathRel_to_takeWhile (hok : parseTablesOk = true) {cx : Ctx} {P : CodePrims}
    {src : List Nat} {els : List Element} {toks : List Token} {st d : Nat}
    (hScans : Scans Ecma.Spec.gl cx P src els)
    (htoks : toks.filter (fun x => x.virt.isNone) = tokensOf src els)
    {xs : List Engine.Model.Node} {ys : List Tree}
    (hr : PairRel (PathRel cx P src els toks st d) xs ys) :
    PairRel (fun x y =>
      ((!(view Engine.builder d).isIn (functionForms ++ classForms) x) =
       (!(Tree.view (Ecma.Grammar.tokenText src els toks)).isIn (functionForms ++ classForms) y)) ∧
      ((view Engine.builder d).isA x .ClassElementName =
       (Tree.view (Ecma.Grammar.tokenText src els toks)).isA y .ClassElementName)) xs ys := by
  induction hr with
  | nil => exact .nil
  | cons hxy _ ih =>
    obtain ⟨_, nX, psX, aX, bX, hbX, hstX, hrelX⟩ := hxy
    have ⟨_, _, hisAX, _, _, _, _⟩ := nodeRel_syn_props (d := d) hok hScans htoks hbX hstX hrelX
    refine .cons ⟨?_, hisAX .ClassElementName⟩ ih
    congr 1
    exact list_any_congr (fun u _ => hisAX u)

private theorem strictDown_sim_eq (hok : parseTablesOk = true) {cx : Ctx} {P : CodePrims}
    {src : List Nat} {els : List Element} {toks : List Token} {st d : Nat}
    (hScans : Scans Ecma.Spec.gl cx P src els)
    (htoks : toks.filter (fun x => x.virt.isNone) = tokensOf src els) :
    ∀ {nds : List Engine.Model.Node} {ts : List Tree} (s : Bool),
      PairRel (PathRel cx P src els toks st d) nds ts →
      strictDown (view Engine.builder d) s nds =
        strictDown (Tree.view (Ecma.Grammar.tokenText src els toks)) s ts := by
  intro nds ts s hrelL
  induction hrelL generalizing s with
  | nil => rfl
  | @cons f_nd f_t rest_nd rest_t hf hrest ih =>
    obtain ⟨hdF, nF, psF, aF, bF, hbF, hstF, hrelF⟩ := hf
    have ⟨_, _, hisAF, _, _, _, _⟩ := nodeRel_syn_props (d := d) hok hScans htoks hbF hstF hrelF
    have hisInEq : ∀ ns, (view Engine.builder d).isIn ns f_nd =
        (Tree.view (Ecma.Grammar.tokenText src els toks)).isIn ns f_t :=
      fun ns => list_any_congr (fun u _ => hisAF u)
    cases hrest with
    | nil =>
      unfold strictDown
      rw [hisInEq classForms]
    | @cons g_nd g_t tl_nd tl_t hg htl =>
      unfold strictDown
      rw [hisInEq classForms]
      cases hCls : (Tree.view (Ecma.Grammar.tokenText src els toks)).isIn classForms f_t with
      | true => simp only [↓reduceIte]
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte]
        rw [hisInEq functionForms]
        cases hFn : (Tree.view (Ecma.Grammar.tokenText src els toks)).isIn functionForms f_t with
        | false => simp only [Bool.false_eq_true, ↓reduceIte]; exact ih s
        | true =>
          simp only [↓reduceIte]
          have htwEq : (((g_nd :: tl_nd).takeWhile fun x => !(view Engine.builder d).isIn (functionForms ++ classForms) x).any
              fun x => (view Engine.builder d).isA x .ClassElementName) =
            (((g_t :: tl_t).takeWhile fun x => !(Tree.view (Ecma.Grammar.tokenText src els toks)).isIn (functionForms ++ classForms) x).any
              fun x => (Tree.view (Ecma.Grammar.tokenText src els toks)).isA x .ClassElementName) :=
            takeWhile_any_zip (pathRel_to_takeWhile hok hScans htoks (.cons hg htl))
          rw [hisAF .MethodDefinition, htwEq]
          cases hMeth : ((Tree.view (Ecma.Grammar.tokenText src els toks)).isA f_t .MethodDefinition &&
              ((g_t :: tl_t).takeWhile fun x => !(Tree.view (Ecma.Grammar.tokenText src els toks)).isIn (functionForms ++ classForms) x).any
                (fun x => (Tree.view (Ecma.Grammar.tokenText src els toks)).isA x .ClassElementName)) with
          | true =>
            simp only [↓reduceIte]
            exact ih s
          | false =>
            simp only [Bool.false_eq_true, ↓reduceIte, bodyStrict_sim_eq hok hScans htoks hbF hdF hstF hrelF]
            exact ih _

theorem strictCode_sim_eq (hok : parseTablesOk = true) {cx : Ctx} {P : CodePrims}
    {src : List Nat} {els : List Element} {toks : List Token} {st d : Nat}
    (hScans : Scans Ecma.Spec.gl cx P src els)
    (htoks : toks.filter (fun x => x.virt.isNone) = tokensOf src els)
    {up_nd : List Engine.Model.Node} {up_t : List Tree}
    {nd : Engine.Model.Node} {t : Tree}
    (hup : PairRel (PathRel cx P src els toks st d) up_nd up_t)
    (ht : PathRel cx P src els toks st d nd t) :
    strictCode (view Engine.builder d) up_nd nd =
      strictCode (Tree.view (Ecma.Grammar.tokenText src els toks)) up_t t := by
  unfold strictCode
  have hpath := pairRel_append (pairRel_reverse hup) (.cons ht .nil)
  generalize up_nd.reverse ++ [nd] = l1 at hpath ⊢
  generalize up_t.reverse ++ [t] = l2 at hpath ⊢
  cases hpath with
  | nil => rfl
  | @cons root_nd root_t path_nd path_t hroot hrest =>
    have ⟨hdR, nR, psR, aR, bR, hbR, hstR, hrelR⟩ := hroot
    have ⟨_, _, hisAR, _, _, _, _⟩ := nodeRel_syn_props (d := d) hok hScans htoks hbR hstR hrelR
    have hisInR : (view Engine.builder d).isIn bodyGoals root_nd =
        (Tree.view (Ecma.Grammar.tokenText src els toks)).isIn bodyGoals root_t :=
      list_any_congr (fun u _ => hisAR u)
    have htopEq :
        (if (view Engine.builder d).isA root_nd .Module then true
         else if (view Engine.builder d).isA root_nd .Script then prologueStrict (view Engine.builder d) root_nd
         else (view Engine.builder d).isIn bodyGoals root_nd && bodyStrict (view Engine.builder d) root_nd) =
        (if (Tree.view (Ecma.Grammar.tokenText src els toks)).isA root_t .Module then true
         else if (Tree.view (Ecma.Grammar.tokenText src els toks)).isA root_t .Script then
           prologueStrict (Tree.view (Ecma.Grammar.tokenText src els toks)) root_t
         else (Tree.view (Ecma.Grammar.tokenText src els toks)).isIn bodyGoals root_t &&
           bodyStrict (Tree.view (Ecma.Grammar.tokenText src els toks)) root_t) := by
      rw [hisAR .Module, hisAR .Script, hisInR,
        prologueStrict_sim_eq hok hScans htoks hbR hdR hstR hrelR,
        bodyStrict_sim_eq hok hScans htoks hbR hdR hstR hrelR]
    dsimp only
    rw [htopEq]
    exact strictDown_sim_eq hok hScans htoks _ (.cons hroot hrest)

/-! ## `sloppyOk` soundness and completeness -/

private theorem foldlM_sloppyOk_false_init {d : Nat} {strict : Bool} {f : Nat}
    {up : List Engine.Model.Node} :
    ∀ ks : List Engine.Model.Node,
      ks.foldlM (init := false) (fun ok k => if ok then sloppyOk Engine.builder d strict f up k else some false) =
        some false
  | [] => rfl
  | _ :: ks => foldlM_sloppyOk_false_init ks

private theorem foldlM_sloppyOk_inv {d : Nat} {strict : Bool} {f : Nat}
    {up : List Engine.Model.Node} :
    ∀ (ks : List Engine.Model.Node) {res : Bool},
      ks.foldlM (init := true) (fun ok k => if ok then sloppyOk Engine.builder d strict f up k else some false) =
        some res →
      (res = true → ∀ k ∈ ks, sloppyOk Engine.builder d strict f up k = some true) ∧
      (res = false → ∃ k ∈ ks, sloppyOk Engine.builder d strict f up k = some false)
  | [], res, h => by
    dsimp only [List.foldlM, pure] at h
    injection h with hres
    subst hres
    exact ⟨(fun _ _ hm => nomatch hm), (fun hf => by cases hf)⟩
  | k :: ks, res, h => by
    simp only [List.foldlM_cons, ↓reduceIte] at h
    rcases opt_none_or_some (sloppyOk Engine.builder d strict f up k) with hnone | ⟨bk, hbk⟩
    · rw [hnone] at h; cases h
    · rw [hbk] at h
      dsimp only [Bind.bind, Option.bind] at h
      cases bk with
      | false =>
        rw [foldlM_sloppyOk_false_init ks] at h
        injection h with hres
        subst hres
        exact ⟨(fun ht => by cases ht), fun _ => ⟨k, List.mem_cons_self, hbk⟩⟩
      | true =>
        have ⟨ht, hf⟩ := foldlM_sloppyOk_inv ks h
        exact ⟨fun hr x hx => by
                 rcases List.mem_cons.mp hx with rfl | hmem
                 · exact hbk
                 · exact ht hr x hmem,
               fun hr => by
                 obtain ⟨x, hx, hsx⟩ := hf hr
                 exact ⟨x, List.mem_cons_of_mem _ hx, hsx⟩⟩

theorem sloppyOk_true_synHeight (hok : parseTablesOk = true) {cx : Ctx} {P : CodePrims}
    {src : List Nat} {els : List Element} {toks : List Token} {st d : Nat} {strict : Bool}
    (hScans : Scans Ecma.Spec.gl cx P src els)
    (htoks : toks.filter (fun x => x.virt.isNone) = tokensOf src els) :
    ∀ (f : Nat) {up_nd : List Engine.Model.Node} {n : NT} {ps : List Param} {i j : Nat}
      {nd : Engine.Model.Node} {t : Tree},
      j ≤ toks.length →
      PosSynStep cx P toks n ps i j t →
      Ecma.Model.NodeRel Engine.Impl st src (Ecma.Grammar.tokenSpan els toks) nd t →
      sloppyOk Engine.builder d strict f up_nd nd = some true →
      synHeight t ≤ f
  | 0, _, _, _, _, _, _, _, _, _, _, h => by cases h
  | f + 1, up_nd, n, ps, i, j, nd, t, hj, hst, hrel, hsl => by
    have ⟨_, _, _, _, _, hlex, hnode⟩ := nodeRel_syn_props (d := d) hok hScans htoks hj hst hrel
    cases t with
    | leaf _ _ => cases hst
    | lex _ _ => simp [synHeight]
    | node nt id0 ps0 a0 b0 kids0 =>
      have hnEq : nt = n := by cases hst; rfl
      subst nt
      obtain ⟨hsynT, _, hlenK, hkidsRel⟩ := hnode id0 ps0 a0 b0 kids0 rfl
      unfold sloppyOk at hsl
      rw [hsynT] at hsl
      simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hsl
      by_cases hcond : (sloppy (Engine.builder.prod nd) &&
          (strict || strictCode (view Engine.builder d) up_nd nd)) = true
      · simp [hcond] at hsl
      · simp only [hcond, Bool.false_eq_true, ↓reduceIte] at hsl
        have hallTrue := (foldlM_sloppyOk_inv _ hsl).1 rfl
        rw [synHeight]
        apply Nat.succ_le_succ
        apply synHeightKids_le_of_all
        intro c_t hcT
        have hcTMem : c_t ∈ (Tree.view (Ecma.Grammar.tokenText src els toks)).kids (.node n id0 ps0 a0 b0 kids0) := hcT
        obtain ⟨idx, hidxLt2, rfl⟩ := List.getElem_of_mem hcTMem
        have hidxLt1 : idx < ((view Engine.builder d).kids nd).length := hlenK.symm ▸ hidxLt2
        let c_nd := ((view Engine.builder d).kids nd)[idx]'hidxLt1
        obtain ⟨_, _, _, _, _, hbC, hstC, hrelC⟩ :=
          hkidsRel idx c_nd _ (List.getElem?_eq_getElem hidxLt1) (List.getElem?_eq_getElem hidxLt2)
        have hcSl := hallTrue c_nd (List.getElem_mem hidxLt1)
        exact sloppyOk_true_synHeight hok hScans htoks f hbC hstC hrelC hcSl

private theorem sloppyOk_spec_gen (hok : parseTablesOk = true) {cx : Ctx} {P : CodePrims}
    {src : List Nat} {els : List Element} {toks : List Token} {st d : Nat} {strict : Bool}
    (hScans : Scans Ecma.Spec.gl cx P src els)
    (htoks : toks.filter (fun x => x.virt.isNone) = tokensOf src els) :
    let G : Ecma.GrammarCtx := { gl := Ecma.Spec.gl, cx := cx, P := P, strict := strict }
    ∀ (f : Nat) {up_nd : List Engine.Model.Node} {up_t : List Tree}
      {nd : Engine.Model.Node} {t : Tree} {res : Bool},
      PairRel (PathRel cx P src els toks st d) up_nd up_t →
      PathRel cx P src els toks st d nd t →
      sloppyOk Engine.builder d strict f up_nd nd = some res →
      (res = true → NonStrictOk Ecma.Spec.gl (G.StrictIn src els toks) up_t t) ∧
      (res = false → ¬ NonStrictOk Ecma.Spec.gl (G.StrictIn src els toks) up_t t) := by
  intro G f
  induction f with
  | zero => intro _ _ _ _ _ _ _ h; cases h
  | succ f ih =>
    intro up_nd up_t nd t res hup hpt hsl
    obtain ⟨hdT, n, ps, i, j, hj, hst, hrel⟩ := hpt
    have ⟨_, _, _, _, _, hlex, hnode⟩ := nodeRel_syn_props (d := d) hok hScans htoks hj hst hrel
    cases t with
    | leaf _ _ => cases hst
    | lex k lt =>
      obtain ⟨hsynF, _, _⟩ := hlex k lt rfl
      unfold sloppyOk at hsl
      rw [hsynF] at hsl
      simp only [Bool.not_false, ↓reduceIte, Option.some.injEq] at hsl
      subst hsl
      exact ⟨fun _ => trivial, fun hf => by cases hf⟩
    | node nt id0 ps0 a0 b0 kids0 =>
      have hnEq : nt = n := by cases hst; rfl
      subst nt
      obtain ⟨hsynT, hprodEq, hlenK, hkidsRel⟩ := hnode id0 ps0 a0 b0 kids0 rfl
      unfold sloppyOk at hsl
      rw [hsynT, hprodEq] at hsl
      simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hsl
      have hscEq := strictCode_sim_eq hok hScans htoks hup ⟨hdT, n, ps, i, j, hj, hst, hrel⟩
      have hslopIff : sloppy id0 = true ↔ id0 ∈ Ecma.Spec.gl.sloppyIds := isSloppy_iff hok id0
      have hstrictIff : (strict || strictCode (view Engine.builder d) up_nd nd) = true ↔
          G.StrictIn src els toks up_t (.node n id0 ps0 a0 b0 kids0) := by
        rw [hscEq, Bool.or_eq_true]
        rfl
      by_cases hbad : (sloppy id0 && (strict || strictCode (view Engine.builder d) up_nd nd)) = true
      · simp only [hbad, ↓reduceIte, Option.some.injEq] at hsl
        subst hsl
        simp only [Bool.and_eq_true] at hbad
        refine ⟨(fun ht => by cases ht), ?_⟩
        intro _ hns
        unfold NonStrictOk at hns
        exact hns.1 (hslopIff.mp hbad.1) (hstrictIff.mp hbad.2)
      · simp only [hbad, Bool.false_eq_true, ↓reduceIte] at hsl
        have hrootOk : id0 ∈ Ecma.Spec.gl.sloppyIds →
            ¬ G.StrictIn src els toks up_t (.node n id0 ps0 a0 b0 kids0) := by
          intro hidMem hstrIn
          exact hbad (Bool.and_eq_true_iff.mpr ⟨hslopIff.mpr hidMem, hstrictIff.mpr hstrIn⟩)
        have ⟨htAll, hfEx⟩ := foldlM_sloppyOk_inv _ hsl
        refine ⟨fun hr => ?_, fun hr => ?_⟩
        · unfold NonStrictOk
          refine ⟨hrootOk, (nonStrictOk_all_iff _).mpr ?_⟩
          intro c_t hcT
          cases hl : c_t.isLeaf with
          | true => cases c_t <;> simp [Tree.isLeaf, NonStrictOk] at hl ⊢
          | false =>
            have hcTFilt : c_t ∈ (Tree.view (Ecma.Grammar.tokenText src els toks)).kids (.node n id0 ps0 a0 b0 kids0) :=
              List.mem_filter.mpr ⟨hcT, by simp [hl]⟩
            obtain ⟨idx, hidxLt2, rfl⟩ := List.getElem_of_mem hcTFilt
            have hidxLt1 : idx < ((view Engine.builder d).kids nd).length := hlenK.symm ▸ hidxLt2
            let c_nd := ((view Engine.builder d).kids nd)[idx]'hidxLt1
            obtain ⟨nC, psC, aC, bC, _, hbC, hstC, hrelC⟩ :=
              hkidsRel idx c_nd _ (List.getElem?_eq_getElem hidxLt1) (List.getElem?_eq_getElem hidxLt2)
            have hdC : synHeight _ ≤ d := Nat.le_of_lt (Nat.lt_of_lt_of_le (synHeight_child_lt (List.getElem_mem hidxLt2)) hdT)
            have hcSl := htAll hr c_nd (List.getElem_mem hidxLt1)
            exact (ih (.cons ⟨hdT, n, ps, i, j, hj, hst, hrel⟩ hup) ⟨hdC, nC, psC, aC, bC, hbC, hstC, hrelC⟩ hcSl).1 rfl
        · obtain ⟨c_nd, hcNdMem, hcSlF⟩ := hfEx hr
          obtain ⟨idx, hidxLt1, rfl⟩ := List.getElem_of_mem hcNdMem
          have hidxLt2 : idx < ((Tree.view (Ecma.Grammar.tokenText src els toks)).kids (.node n id0 ps0 a0 b0 kids0)).length :=
            hlenK ▸ hidxLt1
          let c_t := ((Tree.view (Ecma.Grammar.tokenText src els toks)).kids (.node n id0 ps0 a0 b0 kids0))[idx]'hidxLt2
          obtain ⟨nC, psC, aC, bC, _, hbC, hstC, hrelC⟩ :=
            hkidsRel idx _ c_t (List.getElem?_eq_getElem hidxLt1) (List.getElem?_eq_getElem hidxLt2)
          have hdC : synHeight c_t ≤ d := Nat.le_of_lt (Nat.lt_of_lt_of_le (synHeight_child_lt (List.getElem_mem hidxLt2)) hdT)
          have hnotC := (ih (.cons ⟨hdT, n, ps, i, j, hj, hst, hrel⟩ hup) ⟨hdC, nC, psC, aC, bC, hbC, hstC, hrelC⟩ hcSlF).2 rfl
          rintro ⟨_, hallKids⟩
          have hcTInKids : c_t ∈ kids0 := (List.mem_filter.mp (List.getElem_mem hidxLt2)).1
          exact hnotC ((nonStrictOk_all_iff _).mp hallKids c_t hcTInKids)

theorem sloppyOk_true_sound (hok : parseTablesOk = true) {cx : Ctx} {P : CodePrims}
    {src : List Nat} {els : List Element} {toks : List Token} {st d : Nat} {strict : Bool}
    (hScans : Scans Ecma.Spec.gl cx P src els)
    (htoks : toks.filter (fun x => x.virt.isNone) = tokensOf src els)
    {n : NT} {ps : List Param} {i j : Nat} {nd : Engine.Model.Node} {t : Tree}
    (hj : j ≤ toks.length)
    (hst : PosSynStep cx P toks n ps i j t)
    (hrel : Ecma.Model.NodeRel Engine.Impl st src (Ecma.Grammar.tokenSpan els toks) nd t)
    (hsl : sloppyOk Engine.builder d strict d [] nd = some true) :
    NonStrictOk Ecma.Spec.gl
      (({ gl := Ecma.Spec.gl, cx := cx, P := P, strict := strict } : Ecma.GrammarCtx).StrictIn src els toks) [] t := by
  have hd : synHeight t ≤ d := sloppyOk_true_synHeight hok hScans htoks d hj hst hrel hsl
  exact (sloppyOk_spec_gen hok hScans htoks d .nil ⟨hd, n, ps, i, j, hj, hst, hrel⟩ hsl).1 rfl

theorem sloppyOk_false_sound (hok : parseTablesOk = true) {cx : Ctx} {P : CodePrims}
    {src : List Nat} {els : List Element} {toks : List Token} {st d : Nat} {strict : Bool}
    (hScans : Scans Ecma.Spec.gl cx P src els)
    (htoks : toks.filter (fun x => x.virt.isNone) = tokensOf src els)
    {n : NT} {ps : List Param} {i j : Nat} {nd : Engine.Model.Node} {t : Tree}
    (hj : j ≤ toks.length)
    (hd : synHeight t ≤ d)
    (hst : PosSynStep cx P toks n ps i j t)
    (hrel : Ecma.Model.NodeRel Engine.Impl st src (Ecma.Grammar.tokenSpan els toks) nd t)
    (hsl : sloppyOk Engine.builder d strict d [] nd = some false) :
    ¬ NonStrictOk Ecma.Spec.gl
      (({ gl := Ecma.Spec.gl, cx := cx, P := P, strict := strict } : Ecma.GrammarCtx).StrictIn src els toks) [] t :=
  (sloppyOk_spec_gen hok hScans htoks d .nil ⟨hd, n, ps, i, j, hj, hst, hrel⟩ hsl).2 rfl

end Engine.Parse.Strict
