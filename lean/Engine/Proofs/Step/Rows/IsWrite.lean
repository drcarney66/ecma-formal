module

public import Engine.Proofs.Step.Sym
public import Engine.Proofs.Step.Table

@[expose] public section

/-!
# The row of sort-WriteSharedMemory-event

`isWrite_algRow`: the engine's shortcut at "whether a value is a WriteSharedMemory event"
(`Engine.Accel.isWriteEntry`) is the machine's steps of the algorithm's code. The code's sort test is the
machine's transition at `.invoke (.sort Known.sWriteSharedMemory v)`: the sort's definition in the engine's program is the generated
declarations' (`sortDef_eq`), a Record sort with no test (`sortDef_write`) and no sort below it
(`subSort_write`, by `subSort_leaf`), so the test is the engine's `isWrite` (`sortTest_write`, `step_sort_write`).
-/

namespace Engine.Machine

open Ecma Ecma.Machine

/-! ## The sort WriteSharedMemory in the engine's program -/

set_option maxRecDepth 8000 in
/-- WriteSharedMemory: a Record sort with no test. -/
theorem sortDef_write : Engine.P.sortDef Known.sWriteSharedMemory = some { super := [Known.sSharedDataBlockEvent], test := .none, record := true } := by
  rw [sortDef_eq]
  rfl

theorem noSuper_write : Gen.sortDefs.toList.all (fun o => !((o.map SortDef.super).getD []).contains Known.sWriteSharedMemory) = true := by
  decide +kernel

/-- No sort lies below WriteSharedMemory. -/
theorem subSort_write (f : Nat) (k : SortId) : subSort Engine.P f k Known.sWriteSharedMemory = (k == Known.sWriteSharedMemory) :=
  subSort_leaf Known.sWriteSharedMemory noSuper_write f k

open Engine.Accel in
/-- The sort test at WriteSharedMemory is the engine's `isWrite`. -/
theorem sortTest_write (H : Host F) (call : AlgId → List (Val F) → Run F (Val F)) (v : Val F) :
    (do return .bool (← sortTest Engine.P H call Known.sWriteSharedMemory v) : Run F (Val F)) = isWrite v := by
  funext s
  simp only [sortTest, sortDef_write]
  cases v with
  | ref a =>
    simp only [isWrite, bind, Run.bind, readCell, pure]
    generalize s.heap.get a = o
    rcases o with _ | c
    · simp [Run.Res.bind]
    · cases c <;> simp [Run.Res.bind, subSort_write, sWrite, Run.pure]
  | _ => rfl

open Engine.Accel in
/-- The machine's transition at the sort test of WriteSharedMemory. -/
theorem step_sort_write (H : Host F) (chk : Bool) (s : State F) (fr : List (Frame F))
    (v : Val F) :
    step (Ctx.spec Engine.P' H chk) ⟨s, fr, .invoke (.sort Known.sWriteSharedMemory v)⟩ = leafV ⟨s, fr, .invoke (.sort Known.sWriteSharedMemory v)⟩ (isWrite v) := by
  simp only [step, invoke, spec_P, sortDef_write]
  rw [sortTest_write]

open Engine.Accel in
theorem isWrite_used (v : Val F) : isWrite v.used = isWrite v := by
  cases v <;> rfl

open Engine.Accel in
/-- `isWrite` answers a Bool in the same state, or stops with a sort error. -/
theorem isWrite_cases (v : Val F) (s : State F) :
    (∃ b, isWrite v s = .ok (.bool b) s) ∨ isWrite v s = .stop .sortError := by
  unfold isWrite
  repeat' split
  all_goals first | exact .inl ⟨_, rfl⟩ | exact .inr rfl

/-! ## The machine's steps -/

/-- The frame's continuations under the sort test: the alternatives, the type test's binding, its negation's
leaf, the conjunction, the subject's binding, the branch, the steps after it. -/
def isWriteKonts (w : Val F) : List (Kont F) :=
  [.junct false [], .bind w.used, .args (.leaf (.isTy false false)) [] [], .junct true [], .bind w,
    .args (.br [.ret (.const (.val .true))] []) [] [], .seq [.site [2], .ret (.const (.val .false))]]

/-- The algorithm's steps to its sort test, at a bound argument. -/
theorem isWrite_pre (X : Ctx F) (s : State F) (fs : List (Frame F)) (a : AlgId) (nd : Option F.Node) (w : Val F)
    (hw : w ≠ .unbound) :
    Steps X ⟨s, ⟨a, nd, #[w], .steps false true true, [], [], none⟩ :: fs, .code isWriteCode⟩
      ⟨s, ⟨a, nd, #[w], .steps false true true, [1], isWriteKonts w, none⟩ :: fs, .invoke (.sort Known.sWriteSharedMemory w.used)⟩ := by
  iterate 3 mstep
  refine Steps.next (step_var _ _ _ _ _ w rfl hw) ?_
  iterate 12 mstep
  exact .refl _

/-- The algorithm's steps from its sort test's answer: it returns the answer. -/
theorem isWrite_post (X : Ctx F) (s : State F) (fs : List (Frame F)) (a : AlgId) (nd : Option F.Node) (w : Val F)
    (b : Bool) :
    Steps X ⟨s, ⟨a, nd, #[w], .steps false true true, [1], isWriteKonts w, none⟩ :: fs, .val (.bool b)⟩
      ⟨s, fs, .val (.bool b)⟩ := by
  cases b
  · iterate 13 mstep
    exact .refl _
  · iterate 10 mstep
    exact .refl _

open Engine.Accel in
/-- sort-WriteSharedMemory-event's steps where `isWrite` answers: its answer, in the same state. -/
theorem isWrite_steps (H : Host F) (chk : Bool) (s : State F) (fs : List (Frame F))
    (a : AlgId) (nd : Option F.Node) (w : Val F) (b : Bool) (hw : w ≠ .unbound) (h : isWrite w s = .ok (.bool b) s) :
    Steps (Ctx.spec Engine.P' H chk)
      ⟨s, ⟨a, nd, #[w], .steps false true true, [], [], none⟩ :: fs, .code isWriteCode⟩ ⟨s, fs, .val (.bool b)⟩ := by
  refine Steps.trans (isWrite_pre _ s fs a nd w hw) (Steps.next ?_ (isWrite_post _ s fs a nd w b))
  rw [step_sort_write, isWrite_used]
  simp only [leafV, bindR, h]
  rfl

open Engine.Accel in
/-- sort-WriteSharedMemory-event's run where `isWrite` stops: the same stop. -/
theorem isWrite_stops (H : Host F) (chk : Bool) (s : State F) (fs : List (Frame F))
    (a : AlgId) (nd : Option F.Node) (w : Val F) (e : Stop) (hw : w ≠ .unbound) (h : isWrite w s = .stop e) :
    Runs (Ctx.spec Engine.P' H chk)
      ⟨s, ⟨a, nd, #[w], .steps false true true, [], [], none⟩ :: fs, .code isWriteCode⟩
      (.stop e) := by
  refine ⟨_, isWrite_pre _ s fs a nd w hw, ?_⟩
  show step _ _ = _
  rw [step_sort_write, isWrite_used]
  simp only [leafV, bindR, h]

/-! ## The row -/

open Engine.Accel in
/-- The engine's shortcut at sort-WriteSharedMemory-event is the specification's steps, from a configuration whose
transition enters the algorithm's frame. -/
theorem isWrite_row (H : Host F) (chk : Bool) [PinsHold] (c : Cfg F) (vs : List (Val F))
    (r : Run F (Option (Val F))) (nd : Option F.Node) (he : isWriteEntry vs = some r)
    (hstep : step (Ctx.spec Engine.P' H chk) c =
      enterAlg (Ctx.spec Engine.P' H chk) c isWriteAlg nd (isWriteAlg.args vs) isWriteAlg.header.rc true true) :
    Sim (Ctx.spec Engine.P' H chk) c (bindR c r fun o c => match o with
      | some v => c.to (.val v)
      | none => step (Ctx.spec Engine.P' H chk) c) := by
  unfold isWriteEntry at he
  split at he
  · cases he
  · rename_i v hv
    have hv : v ≠ .unbound := fun h => hv (by rw [h])
    cases he
    obtain ⟨st, fs, ctl⟩ := c
    have hcode : (Ctx.spec Engine.P' H chk).algCode isWriteAlg.id = isWriteCode := by
      show (Engine.P'.alg ⟨Known.cSortWriteSharedMemoryEvent, 0⟩).getD _ = _
      rw [isWriteCode_pin]; rfl
    rcases isWrite_cases v st with ⟨b, h⟩ | h
    · simp only [bindR, always, h, Run.Res.bind]
      show Steps _ _ _
      refine Steps.next hstep ?_
      rw [hcode]
      exact isWrite_steps H chk st fs _ nd v.used b (used_bound hv) (by rw [isWrite_used]; exact h)
    · simp only [bindR, always, h, Run.Res.bind]
      refine .inr ?_
      obtain ⟨c', hs, he⟩ := isWrite_stops H chk st fs isWriteAlg.id nd v.used .sortError (used_bound hv)
        (by rw [isWrite_used]; exact h)
      refine ⟨c', Steps.next hstep ?_, he⟩
      rw [hcode]
      exact hs
  · cases he

open Engine.Accel in
/-- sort-WriteSharedMemory-event's row. -/
theorem isWrite_algRow (H : Host F) (chk : Bool) [PinsHold] :
    AlgRow (Ctx.spec Engine.P' H chk) ⟨Known.cSortWriteSharedMemoryEvent, 0⟩ isWriteEntry :=
  ⟨isWriteAlg, isWriteAlg_pin, fun c vs r nd he hstep => isWrite_row H chk c vs r nd he hstep⟩

end Engine.Machine
