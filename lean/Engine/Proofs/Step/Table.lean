module

public import Engine.Proofs.Step.Kinds
public import Engine.Proofs.Step.ListUpdate

@[expose] public section

/-!
# The table's rows, by kind

Which rows of `Engine.Accel.Table.fastTable` answer at each kind of key, and with them the obligations of
`Engine.Machine.Sound` at the engine's set-up (`Engine.Machine.ctx`): `ctx_prim`, the primitives'.
-/

namespace Engine.Machine

open Ecma Ecma.Machine Engine.Accel Engine.Accel.Rows Engine.Accel.Table

theorem prim_at {k q : PrimId} {xs : List (Val F)} {x : Run F (Val F)}
    (h : (if k = q then ListUpdate.prim k xs else none) = some x) : ListUpdate.prim q xs = some x := by
  split at h
  · subst_vars; exact h
  · cases h

/-- The table's rows at a primitive are the List updates in place. -/
theorem fastTable_prim {Fc : Facts} {rd : ErratumId → Reading} {q : PrimId}
    {xs : List (Val F)} {x : Run F (Val F)} (h : (fastTable Fc rd).prim q xs = some x) :
    ListUpdate.prim q xs = some x := by
  simp only [Table.prim, fastTable, exactRows, sdoRows, primRows, loopRow, algRow,
    List.findSome?_cons, List.findSome?_nil, List.map, Row.prim, List.cons_append, List.nil_append] at h
  repeat' split at h
  all_goals first
    | (cases h; exact prim_at ‹_›)
    | cases h

/-- The primitives' obligation at the engine's set-up, at every configuration. -/
theorem ctx_prim (Q : Prog') (H : Host F) (rd : ErratumId → Reading) (chk : Bool) (c : Cfg F)
    (q : PrimId) (xs : List (Val F)) (r : Run F (Val F)) (hc : c.ctl = .invoke (.prim q xs))
    (h : (ctx Q H rd chk).A.prim q xs = some r) :
    Sim (ctx Q H rd chk).X c (leafV c r) := by
  rw [listUpdate_step _ c q xs r hc (fastTable_prim (Fc := facts Q.P) (rd := rd) h)]
  exact Sim.step _ _

/-! ## The algorithms' rows -/

/-- What an algorithm's row owes: the algorithm is the program's, and from a configuration whose transition
enters its frame, the entry's outcome is the specification's. -/
def AlgRow (X : Ctx F) (a : AlgId) (e : List (Val F) → Option (Run F (Option (Val F)))) : Prop :=
  ∃ g, X.P.alg a = some g ∧ ∀ (c : Cfg F) (vs : List (Val F)) (r : Run F (Option (Val F))) (nd : Option F.Node),
    e vs = some r → step X c = enterAlg X c g nd (g.args vs) g.header.rc true true →
    Sim X c (bindR c r fun o c => match o with
      | some v => c.to (.val v)
      | none => step X c)

/-- A row's obligation at algorithms: `AlgRow` of an algorithm's row, nothing of another. -/
def RowAlgOk (X : Ctx F) : Row F → Prop
  | ⟨.alg a, e, _⟩ => AlgRow X a e
  | _ => True

theorem sameAlg_eq {a b : AlgId} (h : sameAlg a b = true) : a = b := by
  obtain ⟨a1, a2⟩ := a
  obtain ⟨b1, b2⟩ := b
  simp [sameAlg] at h
  simp [h.1, h.2]

/-- The row that answers at an algorithm. -/
theorem Table.alg_some {tab : Table F} {a : AlgId} {vs : List (Val F)} {r : Run F (Option (Val F))} {X : Ctx F}
    (hok : ∀ row ∈ tab, RowAlgOk X row) (h : tab.alg a vs = some r) : ∃ e, AlgRow X a e ∧ e vs = some r := by
  obtain ⟨row, hrow, hx⟩ := List.exists_of_findSome?_eq_some h
  have := hok row hrow
  obtain ⟨k, e, m⟩ := row
  cases k <;> simp only [Row.alg] at hx <;> try cases hx
  split at hx
  · rename_i hs
    cases sameAlg_eq hs
    exact ⟨e, this, hx⟩
  · cases hx

/-- The algorithms' obligations of `Sound`, from the rows'. -/
theorem alg_of_rows {tab : Table F} {X : Ctx F} (hok : ∀ row ∈ tab, RowAlgOk X row) (c : Cfg F) (a : AlgId)
    (vs : List (Val F)) (r : Run F (Option (Val F))) (hc : c.ctl = .invoke (.alg a vs))
    (h : tab.alg a vs = some r) :
    Sim X c (bindR c r fun o c => match o with
      | some v => c.to (.val v)
      | none => step X c) := by
  obtain ⟨e, ⟨g, hg, hrow⟩, he⟩ := Table.alg_some hok h
  refine hrow c vs r none he ?_
  simp only [step, hc, invoke, algEnter, hg]

theorem phrase_of_rows {tab : Table F} {X : Ctx F} (hok : ∀ row ∈ tab, RowAlgOk X row) (c : Cfg F) (p : PhraseId)
    (n : F.Node) (a : AlgId) (vs : List (Val F)) (r : Run F (Option (Val F)))
    (hc : c.ctl = .invoke (.phrase p (some n) vs)) (hp : X.P.phrase p = .alg a) (h : tab.alg a vs = some r) :
    Sim X c (bindR c r fun o c => match o with
      | some v => c.to (.val v)
      | none => step X c) := by
  obtain ⟨e, ⟨g, hg, hrow⟩, he⟩ := Table.alg_some hok h
  refine hrow c vs r (some n) he ?_
  simp only [step, hc, invoke, hp, hg]

end Engine.Machine
