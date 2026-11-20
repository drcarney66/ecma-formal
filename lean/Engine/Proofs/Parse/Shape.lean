module

public import Engine.Proofs.Nodes
public import Engine.Proofs.Host.ModelLemmas
public import Engine.Proofs.Host.ParseLemmas
public import Ecma.Spec.Program

@[expose] public section

/-!
# A parsed node's occurrences are its production's: `Model.NodeLaws` at the engine's model

`Engine.parse` gives a Parse Node only where `shapeOk` passes: at every node of the tree, the children are the
occurrences of the node's production under the readings in effect, with their presences. The occurrences it
checks against (`Parse.occsBy`) are `Grammar.occsAt`'s of the specification's GL (`occsBy_eq`), and a node whose
slots pass has `nodeChild` answer by them (`child_of_nodeOk`); the check is of every node of the tree
(`shapeOk_within`) and holds of the restamped tree (`shapeOk_restamp`). So `child_parse` holds of every parse,
with no fact about the parser's search or builder.
-/

namespace Engine.Impl
open Ecma Ecma.Prims.Nodes Engine.Model
open Ecma.Grammar (NT Prod RuleReading occsOf fillOccs occsAt prodsOf)

/-- The engine's Parse Nodes. -/
local notation "Node" => Engine.Model.Node

/-- The engine's grammar context: the specification's GL under the engine's readings. A parse's context, the code
point classes and strictness from outside are whatever they are: `Model.NodeLaws` reads the GL and the readings
only. -/
def grammarCtx (cx : Ecma.Grammar.Ctx) (P : Ecma.Grammar.CodePrims) (strict : Bool) : GrammarCtx :=
  ⟨Ecma.Spec.gl, Engine.readings, cx, P, strict⟩

/-! The tables are `occsAt`. -/

theorem occs_table (A : Array (Option Prod)) (L₂ : List Prod) (p : Nat) :
    (if p < (A.map fun o => (o.map Engine.Parse.occsOfProd).getD []).size then
        (A.map fun o => (o.map Engine.Parse.occsOfProd).getD [])[p]?.getD []
      else (L₂.toArray.map Engine.Parse.occsOfProd)[p - (A.map fun o => (o.map Engine.Parse.occsOfProd).getD []).size]?.getD []) =
      (((A.toList ++ L₂.map some)[p]?).join.bind fun p => p.altOf.map fun a => occsOf a.rhs p.mask).getD [] := by
  have hp : ∀ o : Option Prod, (o.bind fun p => p.altOf.map fun a => occsOf a.rhs p.mask).getD [] =
      (o.map Engine.Parse.occsOfProd).getD [] := fun o => by cases o <;> rfl
  rw [hp]
  simp only [Array.size_map, Array.getElem?_map, List.getElem?_toArray, List.getElem?_append,
    Array.length_toList, Array.getElem?_toList, List.getElem?_map]
  split
  · cases A[p]? with
    | none => rfl
    | some o => cases o <;> rfl
  · cases L₂[p - A.size]? <;> rfl

/-- The occurrences the check reads are the specification's. -/
theorem occsBy_eq (rd : List RuleReading) (p : Nat) :
    Engine.Parse.occsBy (Engine.Parse.readingOccs rd) p = occsAt Ecma.Spec.gl rd p := by
  have hg : Engine.Parse.glOccs.get = Engine.Parse.prods.map fun o => (o.map Engine.Parse.occsOfProd).getD [] := rfl
  have hr : Engine.Parse.readingOccs rd =
      (prodsOf (rd.map fun x : RuleReading => (x.grammar, [x.rule]))).toArray.map Engine.Parse.occsOfProd := rfl
  have hl : Ecma.Spec.gl.byId = Engine.Parse.prods := rfl
  unfold Engine.Parse.occsBy occsAt Ecma.Grammar.prodAt
  rw [hg, hr, hl]
  exact occs_table _ _ p

/-! A node whose slots pass. -/

theorem fill_absent {N : Type} (n : NT) (os : List (NT × Bool)) (ks : List N) :
    fillOccs ((n, false) :: os) ks = (n.ctorIdx, none) :: fillOccs os ks := by cases ks <;> rfl

/-- Slots that pass are the occurrences, each with its child. -/
theorem slotsOk_fill (kids : Array (NtId × Option Node)) : ∀ (os : List (NT × Bool)) (i : Nat),
    slotsOk kids os i = true →
      fillOccs os ((kids.toList.drop i).filterMap Prod.snd) = (kids.toList.drop i).map fun c => (slotNt c, c.2)
  | [], i, h => by
    have : i = kids.size := by simpa [slotsOk] using h
    subst this
    simp [fillOccs]
  | (n, b) :: os, i, h => by
    rw [slotsOk] at h
    cases hk : kids[i]? with
    | none => rw [hk] at h; cases h
    | some x =>
      rw [hk] at h
      obtain ⟨hi, rfl⟩ := Array.getElem?_eq_some_iff.mp hk
      have hd : kids.toList.drop i = kids[i] :: kids.toList.drop (i + 1) := by
        rw [List.drop_eq_getElem_cons (by simpa using hi)]; simp
      rw [hd]
      rcases hx : kids[i] with ⟨t, _ | ⟨_, _, _, _, m, _, _, _⟩⟩
      · rw [hx] at h
        simp only [Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq] at h
        obtain ⟨⟨rfl, rfl⟩, h⟩ := h
        simp only [List.filterMap_cons, List.map_cons, slotNt, fill_absent, slotsOk_fill kids os (i + 1) h]
      · rw [hx] at h
        simp only [Bool.and_eq_true, beq_iff_eq] at h
        obtain ⟨⟨⟨rfl, rfl⟩, rfl⟩, h⟩ := h
        simp only [List.filterMap_cons, List.map_cons, slotNt, fillOccs, slotsOk_fill kids os (i + 1) h]

/-- A node's own slots pass. -/
def nodeOk (occs : Nat → List (NT × Bool)) : Node → Bool
  | .mk _ _ _ p _ _ kids _ => slotsOk kids (occs p) 0

/-- At a node whose slots pass, `nodeChild` answers by its production's occurrences. -/
theorem child_of_nodeOk {rd : List RuleReading} {d : Node}
    (h : nodeOk (Engine.Parse.occsBy (Engine.Parse.readingOccs rd)) d = true) (nt : NtId) (k : Nat) :
    Impl.nodeChild d nt k = (((fillOccs (occsAt Ecma.Spec.gl rd (Impl.nodeProd d))
      (seqList (M := Impl) (Impl.nodeKids d))).filter (·.1 == nt)).map (·.2))[k]? := by
  obtain ⟨_, _, _, p, _, _, kids, _⟩ := d
  rw [seqList_eq, ← occsBy_eq]
  have hf := slotsOk_fill kids _ 0 h
  simp only [List.drop_zero] at hf
  show ((kids.filter fun c => slotNt c == nt).map Prod.snd)[k]? =
    (((fillOccs (Engine.Parse.occsBy _ p) (kids.filterMap Prod.snd).toList).filter _).map _)[k]?
  rw [Array.toList_filterMap, hf, ← Array.getElem?_toList]
  simp [List.filter_map, Function.comp_def]

/-! The check is of every node. -/

/-- The check passes at a node: its slots pass, and the check passes at its children. -/
theorem shapeOk_iff (occs : Nat → List (NT × Bool)) (n : Node) :
    shapeOk occs n = true ↔ nodeOk occs n = true ∧ ∀ c ∈ (kidsOf n).toList, shapeOk occs c = true := by
  obtain ⟨_, _, _, p, _, _, kids, _⟩ := n
  have h2 : (kids.attach.all fun a => a.val.2.attach.all fun x => shapeOk occs x.val) =
      kids.all fun c => c.2.all (shapeOk occs) := by
    rw [Array.all_subtype (g := fun c => c.2.all (shapeOk occs)) (fun x h => Option.all_attach fun _ _ => rfl)
      (by simp), Array.unattach_attach]
  rw [shapeOk]
  show (slotsOk kids (occs p) 0 && kids.attach.all fun a => a.val.2.attach.all fun x => shapeOk occs x.val) = true ↔ _
  rw [h2, Bool.and_eq_true, Array.all_eq_true_iff_forall_mem]
  refine and_congr Iff.rfl ⟨fun h c hc => ?_, fun h x hx => ?_⟩
  · obtain ⟨t, ht⟩ : ∃ t, (t, some c) ∈ kids := by simpa [kidsOf] using hc
    exact h _ ht
  · obtain ⟨t, _ | c⟩ := x
    · rfl
    · exact h c (by simpa [kidsOf] using ⟨t, hx⟩)

/-- A descendant is a child or a child's descendant. -/
theorem mem_descendants (n d : Node) : d ∈ seqList (M := Impl) (Impl.nodeDescendants n) ↔
    ∃ c ∈ (kidsOf n).toList, d = c ∨ d ∈ seqList (M := Impl) (Impl.nodeDescendants c) := by
  rw [descendants_eq, List.mem_flatMap, nodeKids_eq, seqList_eq]
  simp only [List.mem_cons]

/-- The check passes at every node below one it passes at. -/
theorem shapeOk_below (occs : Nat → List (NT × Bool)) : ∀ (f : Nat) (n : Node), n.height ≤ f → shapeOk occs n = true →
    ∀ d ∈ seqList (M := Impl) (Impl.nodeDescendants n), shapeOk occs d = true
  | 0, n, hf, _, _, _ => by obtain ⟨g, hg⟩ := height_pos n; omega
  | f + 1, n, hf, h, d, hd => by
    obtain ⟨c, hc, hdc⟩ := (mem_descendants n d).1 hd
    have hcs := ((shapeOk_iff occs n).1 h).2 c hc
    rcases hdc with rfl | hdc
    · exact hcs
    · exact shapeOk_below occs f c (by have := height_kid hc; omega) hcs d hdc

/-! The check holds of the restamped tree. -/

theorem slotsOk_restamp (k : Nat) (kids : Array (NtId × Option Node)) : ∀ (os : List (NT × Bool)) (i : Nat),
    slotsOk (kids.map fun c => (c.1, c.2.map (restamp k))) os i = slotsOk kids os i
  | [], i => by simp [slotsOk]
  | (n, b) :: os, i => by
    rw [slotsOk, slotsOk, Array.getElem?_map]
    cases kids[i]? with
    | none => rfl
    | some x =>
      obtain ⟨t, _ | ⟨_, _, _, _, m, _, _, _⟩⟩ := x
      · simp [slotsOk_restamp k kids os (i + 1)]
      · simp [restamp_mk, slotsOk_restamp k kids os (i + 1)]

theorem shapeOk_restamp (occs : Nat → List (NT × Bool)) (k : Nat) : ∀ (f : Nat) (n : Node), n.height ≤ f →
    shapeOk occs n = true → shapeOk occs (restamp k n) = true
  | 0, n, hf, _ => by obtain ⟨g, hg⟩ := height_pos n; omega
  | f + 1, n, hf, h => by
    rw [shapeOk_iff] at h ⊢
    refine ⟨?_, fun c hc => ?_⟩
    · obtain ⟨_, _, _, p, _, _, kids, _⟩ := n
      rw [restamp_mk]
      show slotsOk _ (occs p) 0 = true
      rw [slotsOk_restamp]
      exact h.1
    · rw [← nodeKids_eq, nodeKids_restamp, nodeKids_eq] at hc
      obtain ⟨c', hc', rfl⟩ : ∃ c' ∈ (kidsOf n).toList, restamp k c' = c := by simpa using hc
      exact shapeOk_restamp occs k f c' (by have := height_kid hc'; omega) (h.2 c' hc')

/-! A parse passes the check. -/

/-- A Parse Node the checked outcome gives passes the check. -/
theorem outcome_shaped {stamp : Nat} {src : Array MathVal} {goal : NtId} {args : List (ParamId × Bool)}
    {rd : List RuleReading} {cx : Ecma.Grammar.Ctx} {strict lit : Bool} {n : Node}
    (h : outcome stamp src goal args rd cx strict lit = .ok n) : shaped rd n = true := by
  unfold outcome at h
  split at h
  · cases h
  split at h
  · split at h
    · cases h
    generalize Engine.Parse.parse builder rd cx strict stamp _ goal args lit = o at h
    cases o with
    | ok m =>
      simp only [checked] at h
      split at h
      · cases h; assumption
      · cases h
    | noParse => cases h
    | stop => cases h
  · cases h

/-- A Parse Node `parse` gives passes the check, under the readings in effect. -/
theorem parse_shaped {sel : ErratumId → Reading} {pc : ParseCx} {st : Nat} {src : Array MathVal} {goal : NtId}
    {args : List (ParamId × Bool)} {n : Node} (h : Engine.parse sel pc st src goal args = some (some n)) :
    shaped (rulesUnder readings sel) n = true := by
  cases hg : (goal == Ecma.Grammar.NT.StringNumericLiteral.ctorIdx || goal == Ecma.Grammar.NT.StringIntegerLiteral.ctorIdx)
  · obtain ⟨m, ho, rfl⟩ := parse_some hg h
    exact shapeOk_restamp _ _ _ _ (Nat.le_refl _) (outcome_shaped ho)
  · unfold Engine.parse at h
    simp only [hg, ↓reduceIte] at h
    split at h
    · split at h
      · cases h; assumption
      · cases h
    · next hne => exact absurd h (hne n)

/-- §5.1.2 "the |X| of" at the engine's model: at every node of a parse, the `k`-th written occurrence of `nt` in the
node's production. -/
theorem child_parse (sel : ErratumId → Reading) (pc : ParseCx) (st : Nat) (src : List Nat) (goal : NtId)
    (args : List (ParamId × Bool)) (n d : Impl.Node) (nt : NtId) (k : Nat)
    (h : Impl.parse sel pc st (Impl.seqOfNats src) goal args = some (some n))
    (hd : d = n ∨ d ∈ seqList (M := Impl) (Impl.nodeDescendants n)) :
    Impl.nodeChild d nt k = (((fillOccs (occsAt Ecma.Spec.gl (rulesUnder Engine.readings sel) (Impl.nodeProd d))
      (seqList (M := Impl) (Impl.nodeKids d))).filter (·.1 == nt)).map (·.2))[k]? := by
  have hs : shaped (rulesUnder readings sel) n = true := parse_shaped h
  have hds : shaped (rulesUnder readings sel) d = true := by
    rcases hd with rfl | hd
    · exact hs
    · exact shapeOk_below _ _ n (Nat.le_refl _) hs d hd
  exact child_of_nodeOk ((shapeOk_iff _ d).1 hds).1 nt k

theorem guard_bind_some {α : Type} {b : Bool} {f : Unit → Option α} {x : α}
    (h : (guard (b = true) >>= f) = some x) : b = true ∧ f () = some x := by
  cases b
  · exact nomatch h
  · exact ⟨rfl, by simpa [guard] using h⟩

/-- A covered node `cover` gives passes the check, under the readings in effect. -/
theorem cover_shaped {sel : ErratumId → Reading} {pc : ParseCx} {st : Nat} {c : Node} {goal : NtId}
    {args : List (ParamId × Bool)} {n : Node} (h : Engine.Model.Relabel.relabel sel pc st c goal args = some n) :
    shaped (rulesUnder readings sel) n = true := by
  obtain ⟨_, lo, hi, p, nt, _, kids, t⟩ := c
  unfold Engine.Model.Relabel.relabel at h
  obtain ⟨-, h⟩ := guard_bind_some h
  obtain ⟨p', -, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨-, h⟩ := guard_bind_some h
  obtain ⟨-, h⟩ := guard_bind_some h
  obtain ⟨hs, h⟩ := guard_bind_some h
  cases h
  exact hs

/-- §5.1.5 "the |X| of" at the engine's model, in a covered node the model gives. -/
theorem child_cover (sel : ErratumId → Reading) (pc : ParseCx) (st : Nat) (c : Impl.Node) (goal : NtId)
    (args : List (ParamId × Bool)) (n d : Impl.Node) (nt : NtId) (k : Nat)
    (h : Impl.cover sel pc st c goal args = some n)
    (hd : d = n ∨ d ∈ seqList (M := Impl) (Impl.nodeDescendants n)) :
    Impl.nodeChild d nt k = (((fillOccs (occsAt Ecma.Spec.gl (rulesUnder Engine.readings sel) (Impl.nodeProd d))
      (seqList (M := Impl) (Impl.nodeKids d))).filter (·.1 == nt)).map (·.2))[k]? := by
  have hs : shaped (rulesUnder readings sel) n = true := cover_shaped h
  have hds : shaped (rulesUnder readings sel) d = true := by
    rcases hd with rfl | hd
    · exact hs
    · exact shapeOk_below _ _ n (Nat.le_refl _) hs d hd
  exact child_of_nodeOk ((shapeOk_iff _ d).1 hds).1 nt k

/-- The engine's Parse Node accessors meet their laws. -/
theorem nodeLaws (cx : Ecma.Grammar.Ctx) (P : Ecma.Grammar.CodePrims) (strict : Bool) :
    Model.NodeLaws Impl (grammarCtx cx P strict) :=
  nodeLaws_of (grammarCtx cx P strict) child_parse child_cover

end Engine.Impl
