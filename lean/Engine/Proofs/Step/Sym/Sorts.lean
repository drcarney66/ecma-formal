module

public import Engine.Proofs.Step.Sym.Basic

@[expose] public section

/-!
# Symbolic execution: the program's algorithms and sorts

`rfl` does not compute the engine's program's tables (hash maps over the whole specification), so the
transitions that consult them are lemmas over pins and over the generated declarations:

* `spec_P`: the specification's context's program is the engine's; `algCode_pin`: a pinned algorithm's code.
* `step_alg`: the transition at a call of an algorithm, from its two pins (`pin_prog_alg`, `pin_alg`): its
  frame, at its code.
* `sortDef_eq`: the program's sort definitions are the generated declarations' (a sort's definition is then
  `rw [sortDef_eq]; rfl` under `set_option maxRecDepth 8000`). `step_sort_alg`: the test of a sort whose test
  is an algorithm, of a mathematical value, is that algorithm's call. `step_sort_int`: the test of the sort of
  the integers. `subSort_leaf`: no sort lies below a sort that no declaration names as a super sort (by
  `decide +kernel` over the declarations), which makes a Record sort's test a comparison of the cell's sort.
-/

namespace Engine.Machine

open Ecma Ecma.Machine

/-- The specification's context's program is the engine's. -/
theorem spec_P (H : Host F) (chk : Bool) : (Ctx.spec Engine.P' H chk).P = Engine.P := rfl

/-- A pinned algorithm's code in the specification's context. -/
theorem algCode_pin (H : Host F) (chk : Bool) (a : AlgId) (code : Code)
    (hc : Engine.P'.alg a = some code) : (Ctx.spec Engine.P' H chk).algCode a = code := by
  show (Engine.P'.alg a).getD _ = _
  rw [hc]; rfl

/-- The machine's transition at a call of an algorithm of the program: its frame, at its code. -/
theorem step_alg (H : Host F) (chk : Bool) (s : State F) (fr : List (Frame F))
    (a : AlgId) (vs : List (Val F)) (g : Alg) (code : Code) (hg : Engine.P.alg a = some g)
    (hc : Engine.P'.alg g.id = some code) :
    step (Ctx.spec Engine.P' H chk) ⟨s, fr, .invoke (.alg a vs)⟩ =
      .inl ⟨s, algFrame g none (g.args vs) g.header.rc true true :: fr, .code code⟩ := by
  have hcode : (Ctx.spec Engine.P' H chk).algCode g.id = code := algCode_pin H chk g.id code hc
  simp only [step, invoke, algEnter, spec_P, hg, enterAlg, hcode]
  rfl

/-! ## Sorts -/

/-- The engine's program's sort definitions are the generated declarations'. -/
theorem sortDef_eq (k : SortId) : Engine.P.sortDef k = (Gen.sortDefs[k]?).join := by
  unfold Engine.P
  dsimp only [Prog.memo, Src.expanded, Src.prog, Src.index]
  rfl

/-- The machine's transition at the test of a sort whose test is an algorithm, of a mathematical value. -/
theorem step_sort_alg (H : Host F) (chk : Bool) (s : State F) (fr : List (Frame F))
    (k : SortId) (m : Model.MathVal) (d : SortDef) (a : AlgId)
    (hd : Engine.P.sortDef k = some d) (ht : d.test = .alg a) (hr : d.record = false) :
    step (Ctx.spec Engine.P' H chk) ⟨s, fr, .invoke (.sort k (.math m))⟩ =
      .inl ⟨s, ((⟨s, fr, .invoke (.sort k (.math m))⟩ : Cfg F).push (.args (.leaf .toBool) [] [])).frames,
        .invoke (.alg a [.math m])⟩ := by
  simp only [step, invoke, spec_P, hd, ht, hr, Bool.false_eq_true, ↓reduceIte]
  cases fr <;> rfl

set_option maxRecDepth 8000 in
/-- The sort of the integers has no definition. -/
theorem sortDef_9 : Engine.P.sortDef 9 = none := by
  rw [sortDef_eq]; rfl

/-- The machine's transition at the test of the sort of the integers, of one. -/
theorem step_sort_int (H : Host F) (chk : Bool) (s : State F) (fr : List (Frame F))
    (u : Int) :
    step (Ctx.spec Engine.P' H chk) ⟨s, fr, .invoke (.sort 9 (.math (.int u)))⟩ = .inl ⟨s, fr, .val (.bool true)⟩ := by
  simp only [step, invoke, spec_P, sortDef_9, sortTest]
  rfl

/-- No sort lies below a sort that no declaration names as a super sort. -/
theorem subSort_leaf (t : SortId)
    (hn : Gen.sortDefs.toList.all (fun o => !((o.map SortDef.super).getD []).contains t) = true) (f : Nat)
    (k : SortId) : subSort Engine.P f k t = (k == t) := by
  induction f generalizing k with
  | zero => rfl
  | succ f ih =>
    have ha : (((Engine.P.sortDef k).map (·.super)).getD []).any (subSort Engine.P f · t) = false := by
      rw [sortDef_eq, List.any_eq_false]
      intro x hx
      rw [ih]
      intro hxt
      have hxt : x = t := by simpa using hxt
      rw [hxt] at hx
      rcases hk : Gen.sortDefs[k]? with _ | o
      · simp [hk] at hx
      · obtain ⟨hlt, heq⟩ := Array.getElem?_eq_some_iff.mp hk
        have hm : o ∈ Gen.sortDefs.toList := Array.mem_toList_iff.mpr (heq ▸ Array.getElem_mem hlt)
        have := List.all_eq_true.mp hn o hm
        simp [hk] at hx
        simp [hx] at this
    simp only [subSort, ha, Bool.or_false]

end Engine.Machine
