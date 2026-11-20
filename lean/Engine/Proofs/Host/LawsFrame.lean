module

public import Engine.Proofs.Host.Laws

@[expose] public section

/-!
# The frame laws of a host step that only reads and allocates

`KeepsR`: a step keeps every cell and the rest of the state; such a step keeps the agent and every object to
its invariants (`StepKeeps`, which `invariantsKept` and `agentFixed` read), and the base's choice strategies
are such steps.
-/

namespace Ecma

section Frame
variable {M : Model}

/-- A result whose state, if it has one (an answer or an escape), has `P`. -/
def Res.EndsIn {α : Type} (P : State M → Prop) : Res M α → Prop
  | .ok _ s' => P s'
  | .esc _ s' => P s'
  | _ => True

/-- Allocating keeps every cell of the heap. -/
def AllocKeeps (M : Model) : Prop :=
  ∀ (h : M.Heap (Cell M)) v a c, M.heapGet h a = some c → M.heapGet (M.heapAlloc h v).2 a = some c

/-- `s'` is `s` but for a heap that keeps each of `s`'s cells. -/
def Keeps (s s' : State M) : Prop :=
  s' = { s with heap := s'.heap } ∧ ∀ a c, M.heapGet s.heap a = some c → M.heapGet s'.heap a = some c

theorem Keeps.refl (s : State M) : Keeps s s := ⟨rfl, fun _ _ h => h⟩

theorem Keeps.trans {s₁ s₂ s₃ : State M} (h₁ : Keeps s₁ s₂) (h₂ : Keeps s₂ s₃) : Keeps s₁ s₃ := by
  obtain ⟨e₁, g₁⟩ := h₁
  obtain ⟨e₂, g₂⟩ := h₂
  refine ⟨?_, fun a c h => g₂ a c (g₁ a c h)⟩
  rw [e₂, e₁]

/-- Every answer or escape of `m` keeps the heap's cells, and the rest of the state. -/
def KeepsR {α : Type} (m : Run M α) : Prop := ∀ s, (m s).EndsIn (Keeps s)

theorem KeepsR.pure {α : Type} (a : α) : KeepsR (Run.pure a : Run M α) := fun s => Keeps.refl s

theorem KeepsR.pure' {α : Type} (a : α) : KeepsR (Pure.pure a : Run M α) := KeepsR.pure a

theorem KeepsR.stop {α : Type} (r : Stop) : KeepsR (Run.stop r : Run M α) := fun _ => trivial

theorem KeepsR.get : KeepsR (Run.get : Run M (State M)) := fun s => Keeps.refl s

/-- A read of the state: its answer at the state as it was. -/
theorem KeepsR.ok {α : Type} {m : Run M α} (h : ∀ s, ∃ a, m s = .ok a s) : KeepsR m := fun s => by
  obtain ⟨a, e⟩ := h s; rw [e]; exact Keeps.refl s

theorem KeepsR.bind {α β : Type} {m : Run M α} {f : α → Run M β} (hm : KeepsR m) (hf : ∀ a, KeepsR (f a)) :
    KeepsR (m >>= f) := fun s => by
  change (Run.Res.bind (m s) f).EndsIn _
  have h := hm s
  cases e : m s with
  | ok a s₁ =>
    rw [e] at h
    have h2 := hf a s₁
    change (f a s₁).EndsIn _
    cases e2 : f a s₁ <;> rw [e2] at h2 <;> first | trivial | exact h.trans h2
  | esc c s₁ => rw [e] at h; exact h
  | stop => trivial

theorem KeepsR.ite {α : Type} {c : Prop} [Decidable c] {t e : Run M α} (ht : KeepsR t) (he : KeepsR e) :
    KeepsR (if c then t else e) := by
  by_cases h : c
  · rw [if_pos h]; exact ht
  · rw [if_neg h]; exact he

theorem KeepsR.readCell (a : M.Addr) : KeepsR (Ecma.readCell a : Run M (Cell M)) := fun s => by
  unfold Ecma.readCell; split
  · exact Keeps.refl s
  · trivial

theorem KeepsR.alloc (hA : AllocKeeps M) (c : Cell M) : KeepsR (Ecma.alloc c : Run M M.Addr) := fun _ =>
  ⟨rfl, fun _ _ h => hA _ _ _ _ h⟩

theorem KeepsR.listOf (hA : AllocKeeps M) (vs : List (Val M)) : KeepsR (Ecma.listOf vs : Run M (Val M)) :=
  KeepsR.bind (KeepsR.alloc hA _) fun _ => KeepsR.pure' _

/-- An answer of `Run.boundary m` is an answer or an escape of `m`. -/
theorem KeepsR.boundary {m : Run M (Val M)} (hm : KeepsR m) {s : State M} {r : Val M} {s' : State M}
    (h : Run.boundary m s = .ok r s') : Keeps s s' := by
  have hk := hm s
  change Run.Res.boundary (m s) = _ at h
  cases e : m s <;> rw [e] at h hk <;> cases h <;> exact hk

/-- The host steps' `do` blocks: values, stops, reads of the state and cells, allocations. -/
macro "keeps_tac" : tactic => `(tactic| repeat' (first
  | exact KeepsR.pure _ | exact KeepsR.pure' _ | exact KeepsR.stop _ | exact KeepsR.get
  | exact KeepsR.readCell _ | exact KeepsR.listOf ‹_› _ | exact KeepsR.alloc ‹_› _
  | exact Keeps.refl _ | trivial
  | refine KeepsR.bind ?_ fun _ => ?_
  | split
  | exact KeepsR.ok fun _ => ⟨_, rfl⟩))

theorem attrsAt_keeps {s s' : State M} (hk : ∀ a c, M.heapGet s.heap a = some c → M.heapGet s'.heap a = some c)
    {ps : M.Props (Val M)} {k : M.Str ⊕ M.Sym} {fs : M.Rec (Val M)} (h : attrsAt s ps k = some fs) :
    attrsAt s' ps k = some fs := by
  unfold attrsAt at h ⊢
  split at h
  · rename_i p _
    split at h
    · rename_i hc; cases h; rw [hk _ _ hc]
    · cases h
  · cases h

theorem attrsKept_refl (fs : M.Rec (Val M)) : attrsKept fs fs := ⟨fun _ _ _ => rfl, .inl rfl, fun _ => rfl⟩

theorem objKept_keeps {s s' : State M}
    (hk : ∀ a c, M.heapGet s.heap a = some c → M.heapGet s'.heap a = some c) (sl : M.Rec (Val M))
    (ps : M.Props (Val M)) : objKept s s' sl ps sl ps :=
  ⟨.inl rfl, fun _ => ⟨rfl, fun _ h => h⟩, fun _ fs h _ => ⟨fs, attrsAt_keeps hk h, attrsKept_refl fs⟩⟩

/-- `attrsAt_keeps` where the Record cells alone are kept. -/
theorem attrsAt_keepsRec {s s' : State M}
    (hk : ∀ a t fs, M.heapGet s.heap a = some (.record t fs) → M.heapGet s'.heap a = some (.record t fs))
    {ps : M.Props (Val M)} {k : M.Str ⊕ M.Sym} {fs : M.Rec (Val M)} (h : attrsAt s ps k = some fs) :
    attrsAt s' ps k = some fs := by
  unfold attrsAt at h ⊢
  split at h
  · rename_i p _
    split at h
    · rename_i hc; cases h; rw [hk _ _ _ hc]
    · cases h
  · cases h

/-- `objKept_keeps` where the Record cells alone are kept. -/
theorem objKept_keepsRec {s s' : State M}
    (hk : ∀ a t fs, M.heapGet s.heap a = some (.record t fs) → M.heapGet s'.heap a = some (.record t fs))
    (sl : M.Rec (Val M)) (ps : M.Props (Val M)) : objKept s s' sl ps sl ps :=
  ⟨.inl rfl, fun _ => ⟨rfl, fun _ h => h⟩, fun _ fs h _ => ⟨fs, attrsAt_keepsRec hk h, attrsKept_refl fs⟩⟩

/-- A host whose job callback choices are the defaults (~empty~, and ~unused~ around the call) meets
`callJobCallback` and `jobCallbackDefault`. -/
theorem jobCallback_laws {H : Host M}
    (hd : ∀ vs, H.choice Known.pHostJobCallbackData vs = Run.pure (.enum Known.eEmpty))
    (hp : ∀ vs, H.choice Known.pHostPrepareCallJobCallback vs = Run.pure (.enum Known.eUnused))
    (hc : ∀ vs, H.choice Known.pHostCleanupCallJobCallback vs = Run.pure (.enum Known.eUnused)) :
    (∀ q vs s r s', (q = Known.pHostPrepareCallJobCallback ∨ q = Known.pHostCleanupCallJobCallback) →
      Run.boundary (H.choice q vs) s = .ok r s' → r = .enum Known.eUnused) ∧
    (∀ q vs s r s', H.choice Known.pWebBrowser [.choice 1, .absent] s = .ok (.bool false) s →
      q ∈ [Known.pHostJobCallbackData, Known.pHostPrepareCallJobCallback, Known.pHostCleanupCallJobCallback] →
      Run.boundary (H.choice q vs) s = .ok r s' →
      s' = s ∧ r = .enum (if q = Known.pHostJobCallbackData then Known.eEmpty else Known.eUnused)) := by
  have hq : ∀ q, q ∈ [Known.pHostJobCallbackData, Known.pHostPrepareCallJobCallback, Known.pHostCleanupCallJobCallback] →
      ∀ vs s r s', Run.boundary (H.choice q vs) s = .ok r s' →
      s' = s ∧ r = .enum (if q = Known.pHostJobCallbackData then Known.eEmpty else Known.eUnused) := by
    intro q hq vs s r s' h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · rw [hd] at h; cases h; exact ⟨rfl, rfl⟩
    · rw [hp] at h; cases h; exact ⟨rfl, rfl⟩
    · rw [hc] at h; cases h; exact ⟨rfl, rfl⟩
  refine ⟨fun q vs s r s' hq' h => ?_, fun q vs s r s' _ h1 h => hq q h1 vs s r s' h⟩
  rcases hq' with rfl | rfl
  · exact (hq _ (by simp) vs s r s' h).2
  · exact (hq _ (by simp) vs s r s' h).2

/-- Collecting nothing leaves the state as it is. -/
theorem Collected.nil (s : State M) : Collected s [] s := by
  refine ⟨fun _ h => absurd h List.not_mem_nil, rfl, fun a => ⟨rfl, fun c hc => ⟨c, hc, ?_⟩⟩⟩
  have hr : ∀ k gs (fs : M.Rec (Val M)), Rec.Emptied [] k gs fs fs := fun _ _ _ =>
    .inr ⟨by simp, rfl⟩
  cases c with
  | object sl ps => exact ⟨rfl, hr _ _ _⟩
  | record k fs =>
    refine ⟨rfl, ?_⟩
    by_cases hw : weakMapEntry s a
    · exact .inl ⟨hw, hr _ _ _⟩
    · exact .inr ⟨hw, hr _ _ _⟩
  | list ys o => exact ⟨rfl, fun _ => rfl, rfl, fun _ v h => .inr ⟨List.not_mem_nil, h⟩⟩
  | _ => rfl

/-- The default collection (`Host.collect`, none) keeps `Collected`. -/
theorem Collected.of_pure {s : State M} {xs s'} (h : (pure [] : Run M (List (Val M))) s = .ok xs s') :
    Collected s xs s' := by
  cases h; exact Collected.nil s

/-- `s'` keeps `s`'s agent and each of its Record cells. -/
def RecKeeps (s s' : State M) : Prop :=
  s'.agent = s.agent ∧
    ∀ q k fs, M.heapGet s.heap q = some (.record k fs) → M.heapGet s'.heap q = some (.record k fs)

/-- Every object of `s` is one of `s'` and keeps to the invariants of the essential internal methods. -/
def ObjsKept (s s' : State M) : Prop :=
  ∀ a sl ps, M.heapGet s.heap a = some (.object sl ps) →
    ∃ sl' ps', M.heapGet s'.heap a = some (.object sl' ps') ∧ objKept s s' sl ps sl' ps'

/-- A host step keeps the agent and its Record cells, and every object keeps to the invariants. -/
def StepKeeps (s s' : State M) : Prop := RecKeeps s s' ∧ ObjsKept s s'

theorem Keeps.recKeeps {s s' : State M} (h : Keeps s s') : RecKeeps s s' :=
  ⟨by rw [h.1], fun q _ _ hq => h.2 q _ hq⟩

theorem Keeps.objsKept {s s' : State M} (h : Keeps s s') : ObjsKept s s' :=
  fun a sl ps ha => ⟨sl, ps, h.2 a _ ha, objKept_keeps h.2 sl ps⟩

theorem Keeps.stepKeeps {s s' : State M} (h : Keeps s s') : StepKeeps s s' := ⟨h.recKeeps, h.objsKept⟩

/-- A step that keeps the agent, every Record cell and every object cell keeps every object to the invariants. -/
theorem RecKeeps.stepKeeps {s s' : State M} (h : RecKeeps s s')
    (ho : ∀ a sl ps, M.heapGet s.heap a = some (.object sl ps) → M.heapGet s'.heap a = some (.object sl ps)) :
    StepKeeps s s' :=
  ⟨h, fun a sl ps ha => ⟨sl, ps, ho a sl ps ha, objKept_keepsRec h.2 sl ps⟩⟩

/-- A step that keeps the agent and every Record cell keeps the Agent Record (`agentKept`). -/
theorem RecKeeps.agentKept {s s' : State M} (h : RecKeeps s s') : agentKept s s' :=
  ⟨h.1, fun a k fs _ ha => ⟨fs, h.2 a k fs ha, fun _ _ => rfl⟩⟩

/-- A host each of whose kinds of step is `StepKeeps` has every step `StepKeeps`. -/
theorem Host.stepKeeps_of {H : Host M}
    (hook : ∀ c xs s r s', H.answers c xs s r s' → StepKeeps s s')
    (choice : ∀ q vs s r s', Run.boundary (H.choice q vs) s = .ok r s' → StepKeeps s s')
    (next : ∀ s k s', H.nextJob s = .ok k s' → StepKeeps s s')
    (clears : ∀ s b s', H.clearsKept s = .ok b s' → StepKeeps s s')
    (prep : ∀ k s s', H.prepareJob k s = .ok () s' → StepKeeps s s')
    (clean : ∀ k s s', H.cleanupJob k s = .ok () s' → StepKeeps s s')
    (first : ∀ s a s', H.first s = .ok a s' → StepKeeps s s')
    (idle : ∀ s a s', H.idle s = .ok a s' → StepKeeps s s')
    (idleEnd : ∀ v s b s', H.idleEnd v s = .ok b s' → StepKeeps s s') :
    ∀ s s', H.Step s s' → StepKeeps s s' := by
  rintro s s' (⟨c, xs, r, h⟩ | ⟨q, vs, r, h⟩ | ⟨k, h⟩ | ⟨b, h⟩ | ⟨k, h⟩ | ⟨k, h⟩ | ⟨a, h⟩ | ⟨a, h⟩ | ⟨v, b, h⟩)
  · exact hook c xs s r s' h
  · exact choice q vs s r s' h
  · exact next s k s' h
  · exact clears s b s' h
  · exact prep k s s' h
  · exact clean k s s' h
  · exact first s a s' h
  · exact idle s a s' h
  · exact idleEnd v s b s' h

end Frame

section FrameHelpers
variable {M : Model} (hA : AllocKeeps M)
include hA

omit hA in
theorem readClock_keeps (read : List (HostCall M) → M.Num) : KeepsR (readClock read) := fun s => by
  unfold readClock; exact Keeps.refl s

omit hA in
theorem suspendUntil_keeps (vs : List (Val M)) : KeepsR (suspendUntil vs) := by
  unfold suspendUntil; keeps_tac

omit hA in
theorem agentWoken_keeps : KeepsR (agentWoken (M := M)) := fun s => Keeps.refl s

omit hA in
theorem agentTimeout_keeps (xs : State M → List (Val M)) : KeepsR (agentTimeout xs) := fun s => by
  unfold agentTimeout; split
  · exact Keeps.refl s
  · split
    · exact Keeps.refl s
    · trivial

omit hA in
theorem selectNext_keeps (isAgent : State M → Val M → Bool) (xs : State M → List (Val M)) (vs : List (Val M)) :
    KeepsR (selectNext isAgent xs vs) := by
  fun_cases selectNext isAgent xs vs
  · intro s; dsimp only; split <;> exact Keeps.refl s
  · exact KeepsR.stop _

theorem scWrites_keeps (isWrite : State M → Val M → Bool) (vs : List (Val M)) : KeepsR (scWrites isWrite vs) := by
  intro s; unfold scWrites; split
  · dsimp only; split
    · split
      · exact KeepsR.listOf hA _ s
      · trivial
    · trivial
  · trivial

theorem actRecord_keeps (a : ForInAct M) : KeepsR (actRecord a) := by
  unfold actRecord; keeps_tac

theorem forInChoiceBy_keeps (hist : State M → Val M → Option (List (ForInEntry M))) (vs : List (Val M)) :
    KeepsR (forInChoiceBy hist vs) := by
  fun_cases forInChoiceBy hist vs
  · intro s; dsimp only; split
    · exact actRecord_keeps hA _ s
    · trivial
  · exact KeepsR.stop _

theorem documentOrder_keeps (vs : List (Val M)) : KeepsR (documentOrder vs) := by
  fun_cases documentOrder vs
  · intro s; dsimp only; split
    · exact KeepsR.listOf hA _ s
    · trivial
  · exact KeepsR.stop _

theorem caseAsDefault_keeps (f : M.Seq M.Math → M.Seq M.Math) (vs : List (Val M)) :
    KeepsR (caseAsDefault f vs) := by
  fun_cases caseAsDefault f vs
  · intro s; dsimp only; split
    · split
      · exact KeepsR.listOf hA _ s
      · trivial
    · trivial
  · exact KeepsR.stop _

omit hA in
theorem compareBy_keeps (g : M.Seq M.Math → List Nat) (vs : List (Val M)) : KeepsR (compareBy g vs) := by
  unfold compareBy; keeps_tac

omit hA in
theorem dateAsDefault_keeps (vs : List (Val M)) : KeepsR (dateAsDefault vs) := by
  fun_cases dateAsDefault vs
  · exact KeepsR.ok fun _ => ⟨_, rfl⟩
  · exact KeepsR.stop _

theorem sortDone_keeps (σ : List Nat) : KeepsR (sortDone (M := M) σ) := by
  unfold sortDone; keeps_tac

omit hA in
/-- NativeFunctionSource's answer keeps the state. -/
theorem nativeAnswer_keeps (g : State M → Option (List Nat)) : KeepsR (fun s => nativeAnswer (M := M) (g s) s) := by
  intro s
  show (nativeAnswer (g s) s).EndsIn (Keeps s)
  cases h : nativeNameOf (g s) <;> simp only [nativeAnswer, h, Run.pure, Run.stop]
  · trivial
  · exact Keeps.refl s

theorem sortStepBy_keeps (ix : M.Math → Option Nat) (vs : List (Val M)) : KeepsR (sortStepBy ix vs) := by
  fun_cases sortStepBy ix vs
  · rename_i a _
    cases a with
    | inl p => obtain ⟨j, k, b⟩ := p; exact KeepsR.listOf hA _
    | inr σ => exact sortDone_keeps hA σ
  · exact KeepsR.stop _
  · exact KeepsR.stop _

omit hA in
theorem numberFor_keeps (vs : List (Val M)) : KeepsR (Prims.Numbers.numberFor vs) := by
  unfold Prims.Numbers.numberFor; keeps_tac

end FrameHelpers

/-- info: 'Ecma.Host.stepKeeps_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Host.stepKeeps_of

end Ecma
