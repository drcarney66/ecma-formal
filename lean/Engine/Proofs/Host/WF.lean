module

public import Engine.Proofs.Host.GlobalProps
public import Engine.Proofs.Host.MemoryImpl
public import Engine.Proofs.Laws
public import Engine.Proofs.Host.EscapeLaw
public import Engine.Proofs.Host.OptsOMap

@[expose] public section

/-!
# The Impl host meets the host laws, over Ecma.Data

`wf`: the Impl host at Ecma.Data's names (`JSSpec.Host`) satisfies the host laws (`Host.WF`), its
frame laws by `KeepsR` and `JobKeeps`.
-/

namespace Engine.SpecHost

open Ecma Engine

/-! Frames: the Impl host's steps keep every cell and the rest of the state (`KeepsR`); a job's
preparation and cleanup change only the heap's new cells, the stack and the suspended context. -/

/-- Impl's integers from naturals are exact. -/
theorem fastIntFacts : MemoryModel.IntFacts Impl := MemoryModel.Model.Laws.intFacts Engine.Impl.laws

theorem fast_pairChoice_keeps (vs : List (Val Impl)) : KeepsR (Engine.Host.pairChoice vs) := by
  unfold Engine.Host.pairChoice; keeps_tac

theorem fast_nanEncoding_keeps (vs : List (Val Impl)) : KeepsR (Engine.Host.nanEncoding vs) := by
  unfold Engine.Host.nanEncoding; keeps_tac

theorem fast_escapeChoice_keeps (vs : List (Val Impl)) : KeepsR (Engine.Host.escapeChoice vs) := by
  unfold Engine.Host.escapeChoice; keeps_tac

theorem fast_parseDate_keeps (vs : List (Val Impl)) : KeepsR (Engine.Host.parseDate vs) := by
  unfold Engine.Host.parseDate; keeps_tac

theorem fast_nativeChoice_keeps (vs : List (Val Impl)) : KeepsR (Engine.Host.nativeChoice vs) := by
  fun_cases Engine.Host.nativeChoice vs
  · exact nativeAnswer_keeps _
  · exact KeepsR.stop _

/-- `listInFast` is `listIn`. -/
theorem listInFast_eq (s : State Impl) (v : Val Impl) : Engine.Host.listInFast s v = listIn s v := by
  cases v <;> try rfl
  rename_i a
  simp only [Engine.Host.listInFast, listIn]
  split
  · rename_i xs o h
    rw [h]; exact congrArg some (Engine.Impl.seqList_eq xs).symm
  · rename_i h
    split
    · rename_i xs o h'; exact absurd h' (h xs o)
    · rfl

/-- ForInStep's history read in one pass is `forInHist`. -/
theorem forInHistFast_eq : Engine.Host.forInHistFast = forInHist (M := Impl) := by
  have hl : Engine.Host.listInFast = listIn (M := Impl) := funext fun s => funext (listInFast_eq s)
  funext s h
  unfold Engine.Host.forInHistFast forInHist entryIn
  rw [hl]

theorem keepsR_dite {α : Type} {c : Prop} [Decidable c] {t e : Run Impl α} (ht : c → KeepsR t)
    (he : KeepsR e) : KeepsR (if c then t else e) := by
  by_cases h : c
  · rw [if_pos h]; exact ht h
  · rw [if_neg h]; exact he

/-- Every choice but HostGlobalProperties keeps every cell and the rest of the state. -/
theorem fast_choice_keeps (q : PrimId) (vs : List (Val Impl)) (hq : q ≠ Known.pHostGlobalProperties) :
    KeepsR (Engine.Host.choice names q vs) := by
  have hA := fast_allocKeeps
  unfold Engine.Host.choice
  repeat' (first
    | refine keepsR_dite (fun _ => ?_) ?_
    | exact KeepsR.pure _ | exact KeepsR.stop _
    | exact absurd (beq_iff_eq.mp ‹(q == Known.pHostGlobalProperties) = true›) hq
    | exact numberFor_keeps _ | exact fast_nanEncoding_keeps _
    | exact fast_pairChoice_keeps _ | exact fast_escapeChoice_keeps _ | exact fast_nativeChoice_keeps _
    | exact readClock_keeps _ | exact fast_parseDate_keeps _ | exact suspendUntil_keeps _
    | exact selectNext_keeps _ _ _ | exact agentWoken_keeps | exact agentTimeout_keeps _ | exact scWrites_keeps hA _ _
    | exact forInChoiceBy_keeps hA _ _ | exact documentOrder_keeps hA _ | exact caseAsDefault_keeps hA _ _
    | exact compareBy_keeps _ _ | exact dateAsDefault_keeps _ | exact sortStepBy_keeps hA _ _
    | exact KeepsR.listOf hA _
    | unfold Engine.Host.approxPower | unfold Engine.Host.bigIntTooLarge | unfold Engine.Host.stringTooLarge
    | split)

theorem nextJob_keeps : KeepsR nextJob := fun s => by
  simp only [nextJob, Engine.Host.nextJob]
  split <;> exact Keeps.refl s

/-- The agents' job prims but AgentPrepareJob and AgentCleanupJob keep every cell and the rest of the
state where `next` and `ch` do. -/
theorem agentJobs_keeps (c : Cells) {next : Run Impl (Option Nat)}
    {ch : PrimId → List (Val Impl) → Run Impl (Val Impl)} {q : PrimId} {vs : List (Val Impl)}
    (hn : KeepsR next) (hch : KeepsR (ch q vs)) (h1 : q ≠ Known.pAgentPrepareJob) (h2 : q ≠ Known.pAgentCleanupJob) :
    KeepsR (Engine.Host.agentJobs names c next ch q vs) := by
  unfold Engine.Host.agentJobs
  rw [beq_false_of_ne h1, beq_false_of_ne h2]
  simp only [Bool.false_eq_true, ↓reduceIte]
  refine KeepsR.ite ?_ hch
  split
  · exact KeepsR.bind hn fun o => by cases o <;> exact KeepsR.pure' _
  · exact KeepsR.stop _

/-- Every choice of the host but HostGlobalProperties, AgentPrepareJob and AgentCleanupJob keeps every
cell and the rest of the state. -/
theorem host_choice_keeps (c : Cells) (q : PrimId) (vs : List (Val Impl)) (hq : q ≠ Known.pHostGlobalProperties)
    (h1 : q ≠ Known.pAgentPrepareJob) (h2 : q ≠ Known.pAgentCleanupJob) : KeepsR ((host c).choice q vs) :=
  agentJobs_keeps c nextJob_keeps (fast_choice_keeps q vs hq) h1 h2

/-- The host-defined operations keep every cell and the rest of the state. -/
theorem fast_hooks_keeps (N : Engine.Host.Names) : ∀ p ∈ Engine.Host.hooks N, ∀ c vs, KeepsR (p.2 c vs) := by
  have hA := fast_allocKeeps
  intro p hp c vs
  simp only [Engine.Host.hooks, List.mem_cons, List.not_mem_nil, or_false] at hp
  repeat' rcases hp with rfl | hp
  all_goals (dsimp only; try unfold Engine.Host.normalEnum); try keeps_tac
  all_goals (unfold Engine.Host.enumNamed; split <;> keeps_tac)

/-- A host-defined operation of the data keeps every cell and the rest of the state. -/
theorem hook_keeps {c : Cells} {k : ClauseId} {sec : String} (hk : secOf k = some sec) (vs : List (Val Impl)) :
    KeepsR ((host c).hook k vs) := by
  rw [hook_of hk]
  cases h : hooks.lookup sec with
  | none => exact KeepsR.stop _
  | some g => exact fast_hooks_keeps names (sec, g) (lookup_some_mem h) c vs

/-- `s'` is `s` but for its heap, which keeps each of `s`'s cells, its stack and its suspended context;
its roots are bound where `s`'s are. -/
def JobKeeps (s s' : State Impl) : Prop :=
  s' = { s with heap := s'.heap, stack := s'.stack, suspended := s'.suspended } ∧
    ∀ a c, Impl.heapGet s.heap a = some c → Impl.heapGet s'.heap a = some c

theorem JobKeeps.refl (s : State Impl) : JobKeeps s s := ⟨rfl, fun _ _ h => h⟩

theorem JobKeeps.trans {s₁ s₂ s₃ : State Impl} (h₁ : JobKeeps s₁ s₂) (h₂ : JobKeeps s₂ s₃) : JobKeeps s₁ s₃ := by
  obtain ⟨e₁, g₁⟩ := h₁
  obtain ⟨e₂, g₂⟩ := h₂
  refine ⟨?_, fun a c h => g₂ a c (g₁ a c h)⟩
  rw [e₂, e₁]

theorem JobKeeps.of_keeps {s s' : State Impl} (h : Keeps s s') : JobKeeps s s' := by
  obtain ⟨e, g⟩ := h
  refine ⟨?_, g⟩
  rw [e]

/-- A step that keeps every cell keeps the agent, every Record cell and every object. -/
theorem JobKeeps.stepKeeps {s s' : State Impl} (h : JobKeeps s s') : StepKeeps s s' :=
  ⟨⟨by rw [h.1], fun q _ _ hq => h.2 q _ hq⟩, fun a sl ps ha => ⟨sl, ps, h.2 a _ ha, objKept_keeps h.2 sl ps⟩⟩

theorem pushCtx_jobKeeps {realm sm : Val Impl} {s s' : State Impl} (h : pushCtx realm sm s = .ok () s') :
    JobKeeps s s' := by
  unfold pushCtx Engine.Host.pushCtx at h
  split at h
  · split at h
    · simp only [Res.ok.injEq] at h
      obtain ⟨-, rfl⟩ := h
      exact ⟨rfl, fun _ _ hb => heapGet_alloc hb⟩
    · cases h
  · cases h

theorem readList_keeps (a : Impl.Addr) : KeepsR (Engine.Host.readList a) := by
  unfold Engine.Host.readList; keeps_tac

/-- Every answer or escape of `m` is `JobKeeps` of the state it starts from. -/
def JobKeepsR {α : Type} (m : Run Impl α) : Prop := ∀ s, (m s).EndsIn (JobKeeps s)

theorem JobKeepsR.of_keepsR {α : Type} {m : Run Impl α} (h : KeepsR m) : JobKeepsR m := fun s => by
  have hk := h s
  cases e : m s <;> rw [e] at hk <;> first | trivial | exact JobKeeps.of_keeps hk

theorem JobKeepsR.bind {α β : Type} {m : Run Impl α} {f : α → Run Impl β} (hm : JobKeepsR m)
    (hf : ∀ a, JobKeepsR (f a)) : JobKeepsR (m >>= f) := fun s => by
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

theorem JobKeepsR.ok_of {α : Type} {m : Run Impl α} (hm : JobKeepsR m) {s : State Impl} {a : α}
    {s' : State Impl} (h : m s = .ok a s') : JobKeeps s s' := by
  have hk := hm s
  rw [h] at hk
  exact hk

theorem JobKeepsR.boundary {m : Run Impl (Val Impl)} (hm : JobKeepsR m) {s : State Impl} {r : Val Impl}
    {s' : State Impl} (h : Run.boundary m s = .ok r s') : JobKeeps s s' := by
  have hk := hm s
  change Run.Res.boundary (m s) = _ at h
  cases e : m s <;> rw [e] at h hk <;> cases h <;> exact hk

theorem pushCtx_jobKeepsR (realm sm : Val Impl) : JobKeepsR (pushCtx realm sm) := fun s => by
  cases e : pushCtx realm sm s with
  | ok u t => exact pushCtx_jobKeeps e
  | esc v t =>
    unfold pushCtx Engine.Host.pushCtx at e
    split at e
    · split at e <;> cases e
    · cases e
  | stop => trivial

theorem prepareJobOn_jobKeepsR (c : Cells) (base k : Nat) : JobKeepsR (Engine.Host.prepareJobOn names c base k) :=
    fun s => by
  unfold Engine.Host.prepareJobOn
  split
  · split
    · try dsimp only
      split
      · exact (JobKeepsR.bind (JobKeepsR.of_keepsR (readList_keeps c.realm)) fun xs => by
          try dsimp only
          split
          · exact JobKeepsR.of_keepsR (KeepsR.pure _)
          · exact pushCtx_jobKeepsR _ _) s
      · exact pushCtx_jobKeepsR _ _ s
    · trivial
  · trivial

theorem prepareJob_jobKeeps {c : Cells} {k : Nat} {s s' : State Impl} (h : prepareJob c k s = .ok () s') :
    JobKeeps s s' :=
  (prepareJobOn_jobKeepsR c 0 k).ok_of h

theorem cleanupJob_jobKeepsR (k : Nat) : JobKeepsR (Engine.Host.cleanupJob k) := fun s => by
  unfold Engine.Host.cleanupJob
  split
  · exact JobKeeps.refl _
  · split
    · exact ⟨rfl, fun _ _ h => h⟩
    · trivial

/-- AgentPrepareJob. -/
theorem agentPrepare_jobKeepsR (c : Cells) (next : Run Impl (Option Nat))
    (ch : PrimId → List (Val Impl) → Run Impl (Val Impl)) (vs : List (Val Impl)) :
    JobKeepsR (Engine.Host.agentJobs names c next ch Known.pAgentPrepareJob vs) := fun s => by
  unfold Engine.Host.agentJobs
  simp only [show (Known.pAgentPrepareJob == Known.pAgentNextJob) = false from rfl, beq_self_eq_true,
    Bool.false_eq_true, ↓reduceIte]
  split
  · rename_i x
    cases hk : Engine.Model.MathVal.idx x with
    | none => trivial
    | some k =>
      dsimp only
      exact (JobKeepsR.bind (by unfold Engine.Host.prepareJob; exact prepareJobOn_jobKeepsR c 0 _) fun _ =>
        JobKeepsR.bind (JobKeepsR.of_keepsR KeepsR.get) fun t => by
          try dsimp only
          split
          · exact JobKeepsR.of_keepsR (KeepsR.pure' _)
          · exact JobKeepsR.of_keepsR (KeepsR.stop _)) s
  · trivial

/-- AgentCleanupJob. -/
theorem agentCleanup_jobKeepsR (c : Cells) (next : Run Impl (Option Nat))
    (ch : PrimId → List (Val Impl) → Run Impl (Val Impl)) (vs : List (Val Impl)) :
    JobKeepsR (Engine.Host.agentJobs names c next ch Known.pAgentCleanupJob vs) := fun s => by
  unfold Engine.Host.agentJobs
  simp only [show (Known.pAgentCleanupJob == Known.pAgentNextJob) = false from rfl,
    show (Known.pAgentCleanupJob == Known.pAgentPrepareJob) = false from rfl, beq_self_eq_true,
    Bool.false_eq_true, ↓reduceIte]
  split
  · rename_i x
    cases hk : Engine.Model.MathVal.idx x with
    | none => trivial
    | some k => exact (JobKeepsR.bind (cleanupJob_jobKeepsR k) fun _ => JobKeepsR.of_keepsR (KeepsR.pure' _)) s
  · trivial

theorem agentPrepareJob_law (c : Cells) {next : Run Impl (Option Nat)}
    {ch : PrimId → List (Val Impl) → Run Impl (Val Impl)} (vs : List (Val Impl)) (s : State Impl) (r : Val Impl)
    (s' : State Impl) (h : Engine.Host.agentJobs names c next ch Known.pAgentPrepareJob vs s = .ok r s') :
    ∃ k, vs = [.math (Impl.ofNat k)] ∧ scheduled s.hostLog k = some r ∧ promisePrepared s k s' := by
  unfold Engine.Host.agentJobs at h
  simp only [show (Known.pAgentPrepareJob == Known.pAgentNextJob) = false from rfl, beq_self_eq_true,
    Bool.false_eq_true, ↓reduceIte] at h
  split at h
  · rename_i x
    cases hk : Engine.Model.MathVal.idx x with
    | none => rw [hk] at h; simp [Run.stop] at h
    | some k =>
      rw [hk] at h
      dsimp only at h
      simp only [bind, Run.bind] at h
      cases hp : Engine.Host.prepareJob names c k s with
      | ok u t =>
        rw [hp] at h
        have hp' : Engine.Host.prepareJobOn names c 0 k s = .ok () t := hp
        have hlog : t.hostLog = s.hostLog := by rw [((prepareJobOn_jobKeepsR c 0 k).ok_of hp').1]
        simp only [Run.Res.bind, Run.bind, Run.get] at h
        rw [hlog] at h
        cases hs : scheduled s.hostLog k with
        | none => rw [hs] at h; simp [Run.stop] at h
        | some j =>
          rw [hs] at h
          cases j
          case clo =>
            simp only [pure, Run.pure, Res.ok.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            exact ⟨k, by rw [ofNat_of_idx hk], hs, fun c' job realm xs sm rl r' he hc hr =>
              promiseJobPrepared_law c s k _ c' job realm xs sm rl r' hp he hc hr⟩
          all_goals simp [Run.stop] at h
      | _ => rw [hp] at h; simp [Run.Res.bind] at h
  · simp [Run.stop] at h

theorem agentCleanupJob_law (c : Cells) {next : Run Impl (Option Nat)}
    {ch : PrimId → List (Val Impl) → Run Impl (Val Impl)} (vs : List (Val Impl)) (s : State Impl) (r : Val Impl)
    (s' : State Impl) (h : Engine.Host.agentJobs names c next ch Known.pAgentCleanupJob vs s = .ok r s') :
    r = .enum Known.eUnused ∧ Impl.eq (Impl.seqLen s'.stack) (Impl.ofNat 0) = true := by
  unfold Engine.Host.agentJobs at h
  simp only [show (Known.pAgentCleanupJob == Known.pAgentNextJob) = false from rfl,
    show (Known.pAgentCleanupJob == Known.pAgentPrepareJob) = false from rfl, beq_self_eq_true,
    Bool.false_eq_true, ↓reduceIte] at h
  split at h
  · rename_i x
    cases hk : Engine.Model.MathVal.idx x with
    | none => rw [hk] at h; simp [Run.stop] at h
    | some k =>
      rw [hk] at h
      dsimp only at h
      simp only [bind, Run.bind] at h
      cases hp : Engine.Host.cleanupJob k s with
      | ok u t =>
        rw [hp] at h
        simp only [Run.Res.bind, pure, Run.pure, Res.ok.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨rfl, jobCleanup_law k s t hp⟩
      | _ => rw [hp] at h; simp [Run.Res.bind] at h
  · simp [Run.stop] at h

theorem cleanupJob_jobKeeps {k : Nat} {s s' : State Impl} (h : Engine.Host.cleanupJob k s = .ok () s') :
    JobKeeps s s' := by
  unfold Engine.Host.cleanupJob at h
  split at h
  · cases h; exact JobKeeps.refl _
  · split at h
    · cases h
      exact ⟨rfl, fun _ _ h => h⟩
    · cases h

/-! A host step that writes Lists only (`LK`): the agent, every cell that is no List, and every List cell's
being one are kept; such a step keeps every Record and object (`StepKeeps`). `print` writes its output List,
the host's own Job and idle step the realm's cell, HostGlobalProperties only the global object. -/

/-- `s'` keeps `s`'s agent and each of its cells that is no List; a List cell is still one. -/
def LK (s s' : State Impl) : Prop :=
  s'.agent = s.agent ∧
    (∀ q c, Impl.heapGet s.heap q = some c → (∀ xs o, c ≠ .list xs o) → Impl.heapGet s'.heap q = some c) ∧
    ∀ q xs o, Impl.heapGet s.heap q = some (.list xs o) → ∃ ys o', Impl.heapGet s'.heap q = some (.list ys o')

theorem LK.trans {s₁ s₂ s₃ : State Impl} (h₁ : LK s₁ s₂) (h₂ : LK s₂ s₃) : LK s₁ s₃ := by
  refine ⟨h₂.1.trans h₁.1, fun q c hq hc => h₂.2.1 q c (h₁.2.1 q c hq hc) hc, fun q xs o hq => ?_⟩
  obtain ⟨ys, o', h⟩ := h₁.2.2 q xs o hq
  exact h₂.2.2 q ys o' h

theorem JobKeeps.lk {s s' : State Impl} (h : JobKeeps s s') : LK s s' :=
  ⟨by rw [h.1], fun q c hq _ => h.2 q c hq, fun q xs o hq => ⟨xs, o, h.2 q _ hq⟩⟩

theorem LK.stepKeeps {s s' : State Impl} (h : LK s s') : StepKeeps s s' :=
  RecKeeps.stepKeeps ⟨h.1, fun q _ _ hq => h.2.1 q _ hq fun _ _ e => by cases e⟩
    fun a _ _ ha => h.2.1 a _ ha fun _ _ e => by cases e

/-- Every answer or escape of `m` is `LK` of the state it starts from. -/
def LKR {α : Type} (m : Run Impl α) : Prop := ∀ s, (m s).EndsIn (LK s)

theorem LKR.of_jobKeepsR {α : Type} {m : Run Impl α} (h : JobKeepsR m) : LKR m := fun s => by
  have hk := h s
  cases e : m s <;> rw [e] at hk <;> first | trivial | exact hk.lk

theorem LKR.ok_of {α : Type} {m : Run Impl α} (hm : LKR m) {s : State Impl} {a : α} {s' : State Impl}
    (h : m s = .ok a s') : LK s s' := by
  have hk := hm s
  rw [h] at hk
  exact hk

/-- A read of a List cell: the state as it was, the cell a List. -/
theorem readList_ok {a : Impl.Addr} {s : State Impl} {xs : List (Val Impl)} {s' : State Impl}
    (h : Engine.Host.readList a s = .ok xs s') : s' = s ∧ ∃ ys o, Impl.heapGet s.heap a = some (.list ys o) := by
  unfold Engine.Host.readList at h
  simp only [bind, Run.bind, Ecma.readCell] at h
  revert h
  cases hc : s.heap.get a with
  | none => intro h; simp [hc, Run.Res.bind, Run.stop] at h
  | some x =>
    cases x with
    | list ys o =>
      intro h
      simp only [hc, Run.Res.bind, pure, Run.pure, Res.ok.injEq] at h
      exact ⟨h.2.symm, ys, o, hc⟩
    | _ => intro h; simp [hc, Run.Res.bind, Run.stop] at h

/-- A read of a List cell does not escape. -/
theorem readList_esc {a : Impl.Addr} {s : State Impl} {v : Val Impl} {s' : State Impl} :
    Engine.Host.readList a s ≠ .esc v s' := by
  unfold Engine.Host.readList
  simp only [bind, Run.bind, Ecma.readCell]
  cases hc : s.heap.get a with
  | none => simp [hc, Run.Res.bind, Run.stop]
  | some x => cases x <;> simp [hc, Run.Res.bind, Run.stop, pure, Run.pure]

/-- Writing the List cell at `a` keeps `LK` where `a` holds a List. -/
theorem writeElems_lk {a : Impl.Addr} {vs : List (Val Impl)} {s : State Impl} {ys : Impl.Seq (Val Impl)} {o : Nat}
    (ha : Impl.heapGet s.heap a = some (.list ys o)) : (Engine.Host.writeElems a vs s).EndsIn (LK s) := by
  simp only [Engine.Host.writeElems, Ecma.writeList, Res.EndsIn]
  refine ⟨rfl, fun q c hq hc => ?_, fun q xs o' hq => ?_⟩
  · have hne : a ≠ q := fun e => by subst e; rw [ha] at hq; cases hq; exact hc _ _ rfl
    rw [Engine.Host.heapGet_set_ne _ _ hne]; exact hq
  · by_cases hq' : a = q
    · subst hq'; exact ⟨_, _, Engine.Host.heapGet_set_self ha⟩
    · exact ⟨xs, o', by rw [Engine.Host.heapGet_set_ne _ _ hq']; exact hq⟩

/-- A read of a List cell, then a step that is `LK` where it is a List: `LK`. -/
theorem readList_bind_lk {β : Type} (a : Impl.Addr) {f : List (Val Impl) → Run Impl β}
    (hf : ∀ xs s ys o, Impl.heapGet s.heap a = some (.list ys o) → (f xs s).EndsIn (LK s)) :
    LKR (Engine.Host.readList a >>= f) := fun s => by
  change (Run.Res.bind (Engine.Host.readList a s) f).EndsIn _
  cases e : Engine.Host.readList a s with
  | ok xs s₁ =>
    obtain ⟨rfl, ys, o, ha⟩ := readList_ok e
    exact hf xs s₁ ys o ha
  | esc c s₁ => exact (readList_esc e).elim
  | stop => trivial

/-- A step that is `LK` at `s`, then one that is `LK` from where it ends. -/
theorem lk_bind {α β : Type} {m : Run Impl α} {f : α → Run Impl β} {s : State Impl} (hm : (m s).EndsIn (LK s))
    (hf : ∀ a t, m s = .ok a t → (f a t).EndsIn (LK t)) : ((m >>= f) s).EndsIn (LK s) := by
  change (Run.Res.bind (m s) f).EndsIn _
  cases e : m s with
  | ok a t =>
    rw [e] at hm
    have h2 := hf a t e
    change (f a t).EndsIn _
    cases e2 : f a t <;> rw [e2] at h2 <;> first | trivial | exact hm.trans h2
  | esc c t => rw [e] at hm; exact hm
  | stop => trivial

/-- The host's own steps' `do` blocks, for `JobKeepsR`: values, stops, reads, allocations, pushes. -/
macro "jk_tac" : tactic => `(tactic| repeat' (first
  | exact JobKeepsR.of_keepsR (KeepsR.pure' _) | exact JobKeepsR.of_keepsR (KeepsR.pure _)
  | exact JobKeepsR.of_keepsR (KeepsR.stop _) | exact pushCtx_jobKeepsR _ _
  | exact JobKeepsR.of_keepsR (KeepsR.listOf fast_allocKeeps _) | exact JobKeepsR.of_keepsR (readList_keeps _)
  | exact JobKeepsR.of_keepsR KeepsR.get
  | refine JobKeepsR.bind ?_ fun _ => ?_
  | split
  | (dsimp only; done) | dsimp only))

/-- The host's own first Job keeps `LK`: it writes the realm's cell, pushes a context and allocates. -/
theorem first_lk (o : Engine.Host.HostOpts) (c : Cells) : LKR (Engine.Host.hostBy names o c).first := by
  refine readList_bind_lk _ fun xs s ys o' ha => ?_
  split
  · refine lk_bind (writeElems_lk ha) fun _ t _ => (LKR.of_jobKeepsR ?_) t
    jk_tac
  · exact JobKeeps.lk (JobKeeps.refl s)

/-- The host's idle step keeps `LK`: it reads the realm's cell and pushes a context. -/
theorem idle_lk (o : Engine.Host.HostOpts) (c : Cells) : LKR (Engine.Host.hostBy names o c).idle := by
  refine LKR.of_jobKeepsR ?_
  show JobKeepsR (Run.get >>= _)
  jk_tac

/-- The host's cleanup after its own Job or idle step keeps `LK`: it pops the stack and writes the realm's cell. -/
theorem idleEnd_lk (o : Engine.Host.HostOpts) (c : Cells) (v : Val Impl) :
    LKR ((Engine.Host.hostBy names o c).idleEnd v) := by
  intro s
  refine lk_bind ?_ fun _ t _ => ?_
  · cases e : Engine.Host.cleanupJob 0 s with
    | ok u t => exact (cleanupJob_jobKeeps e).lk
    | esc w t =>
      unfold Engine.Host.cleanupJob at e
      split at e
      · cases e
      · split at e <;> cases e
    | stop => trivial
  · refine readList_bind_lk _ (fun xs s' ys o' ha => ?_) t
    split
    · exact lk_bind (writeElems_lk ha) fun _ t' _ => JobKeeps.lk (JobKeeps.refl t')
    · exact JobKeeps.lk (JobKeeps.refl s')

theorem printLine_lk {c : Cells} {vs : List (Val Impl)} {s : State Impl} {r : Val Impl}
    {s' : State Impl} (h : Run.boundary (printLine c vs) s = .ok r s') : LK s s' := by
  unfold printLine at h
  split at h
  · simp only [Run.boundary, bind, Run.bind, readList, readCell] at h
    revert h
    cases hc : s.heap.get c.out with
    | none => intro h; cases h
    | some x =>
      intro h
      cases x with
      | list xs o =>
        simp [Run.Res.bind, pure, Run.pure, writeElems, writeList, Run.bind, Run.Res.boundary] at h
        obtain ⟨-, rfl⟩ := h
        have hw := writeElems_lk (a := c.out) (vs := Engine.Host.elems xs ++ [.str ‹_›]) (s := s) (ys := xs) (o := o) hc
        simpa [Engine.Host.writeElems, Ecma.writeList, hc, Res.EndsIn] using hw
      | _ => simp [Run.Res.bind, Run.stop, Run.Res.boundary] at h
  · cases h

/-- The agent API's clauses keep every cell and the rest of the state. -/
theorem agentHook_keeps (k : ClauseId) (vs : List (Val Impl)) : KeepsR (Engine.Host.agentHook k vs) := by
  have hA := fast_allocKeeps
  unfold Engine.Host.agentHook
  dsimp only
  refine KeepsR.ite ?_ <| KeepsR.ite ?_ <| KeepsR.ite ?_ <| KeepsR.ite ?_ <| KeepsR.ite ?_ <| KeepsR.ite ?_ <|
    KeepsR.ite ?_ <| KeepsR.ite ?_ <| KeepsR.ite ?_ <| KeepsR.ite ?_ <| KeepsR.ite ?_ <| KeepsR.stop _
  all_goals (rcases vs with _ | ⟨v, _ | ⟨_, _ | ⟨_, _⟩⟩⟩ <;> try cases v)
  all_goals first | exact KeepsR.pure _ | exact KeepsR.stop _ | exact KeepsR.ok fun _ => ⟨_, rfl⟩ | skip
  all_goals intro s; dsimp only
  all_goals repeat' split
  all_goals first | exact Keeps.refl _ | exact KeepsR.listOf hA _ _

theorem ownHook_stepKeeps {c : Cells} {k : ClauseId} {vs : List (Val Impl)} {s : State Impl} {r : Val Impl}
    {s' : State Impl} (h : Run.boundary (ownHook c k vs) s = .ok r s') : StepKeeps s s' := by
  unfold ownHook at h
  split at h
  · exact (printLine_lk h).stepKeeps
  · refine (KeepsR.boundary ?_ h).stepKeeps
    refine KeepsR.ite ?_ (KeepsR.ite ?_ (KeepsR.ite ?_ (KeepsR.ite ?_ (KeepsR.ite (agentHook_keeps k vs) (KeepsR.stop _)))))
    · fun_cases Engine.Host.loadedModule vs <;> keeps_tac
    · unfold Engine.Host.moduleLoaded; keeps_tac
    · unfold Engine.Host.moduleSource; keeps_tac
    · fun_cases Engine.Host.moduleKey c vs <;> keeps_tac

/-- Every host-defined operation, the data's or the host's own, keeps the agent, each Record cell and every
object. -/
theorem fast_hook_stepKeeps {c : Cells} {k : ClauseId} {xs : List (Val Impl)} {s : State Impl} {r : Val Impl}
    {s' : State Impl} (h : (host c).answers k xs s r s') : StepKeeps s s' := by
  unfold Host.answers at h
  cases hk : secOf k with
  | some sec => exact (KeepsR.boundary (hook_keeps hk xs) h).stepKeeps
  | none => rw [hook_own hk] at h; exact ownHook_stepKeeps h

/-- Every choice keeps the agent, each Record cell and every object. -/
theorem fast_choice_stepKeeps {c : Cells} {q : PrimId} {vs : List (Val Impl)} {s : State Impl} {r : Val Impl}
    {s' : State Impl} (h : Run.boundary ((host c).choice q vs) s = .ok r s') : StepKeeps s s' := by
  by_cases hq : q = Known.pHostGlobalProperties
  · subst hq; rw [choice_globalProps] at h; exact globalProps_stepKeeps h
  by_cases h1 : q = Known.pAgentPrepareJob
  · subst h1; exact ((agentPrepare_jobKeepsR c nextJob (Engine.Host.choice names) vs).boundary h).stepKeeps
  by_cases h2 : q = Known.pAgentCleanupJob
  · subst h2; exact ((agentCleanup_jobKeepsR c nextJob (Engine.Host.choice names) vs).boundary h).stepKeeps
  exact (KeepsR.boundary (host_choice_keeps c q vs hq h1 h2) h).stepKeeps

/-- Every step of the Impl host keeps the agent, each Record cell and every object. -/
theorem fast_stepKeeps (c : Cells) : ∀ s s', (host c).Step s s' → StepKeeps s s' :=
  Host.stepKeeps_of (fun _ _ _ _ _ h => fast_hook_stepKeeps h) (fun _ _ _ _ _ h => fast_choice_stepKeeps h)
    (fun s _ _ h => by rw [nextJob_same (checkElapsed_ok h).1]; exact (Keeps.refl s).stepKeeps)
    (fun s _ _ h => by cases h; exact (Keeps.refl s).stepKeeps)
    (fun _ _ _ h => (prepareJob_jobKeeps h).stepKeeps) (fun k _ _ h => (cleanupJob_jobKeeps (k := k) h).stepKeeps)
    (fun _ _ _ h => ((first_lk {} c).ok_of h).stepKeeps) (fun _ _ _ h => ((idle_lk {} c).ok_of h).stepKeeps)
    (fun v _ _ _ h => ((idleEnd_lk {} c v).ok_of h).stepKeeps)

/-- The host satisfies the host laws. -/
theorem wf (c : Cells) : Host.WF (host c) where
  nextJob s k s' h := ⟨(jobScheduled_law c s k s' h).1, (jobScheduled_law c s k s' h).2, jobOwned_law c s k s' h,
    fun hk i hik hi ho => promiseJobsOrder_law c s k s' h hk i hik hi ho⟩
  nanEncoding v w p _ hp := nanEncoding_law c v w p hp
  approxInteger x s r s' h := approxInteger_law c x s r s' h
  ownsAgent s k h := ownsAgent_law c s k h
  ownsSingle s k h _ := ownsSingle_law c s k h
  agentNextJob vs s r s' h := agentNextJob_law c vs s r s' h
  agentPrepareJob vs s r s' h := agentPrepareJob_law c (next := nextJob) (ch := Engine.Host.choice names) vs s r s' h
  agentCleanupJob vs s r s' h := agentCleanupJob_law c (next := nextJob) (ch := Engine.Host.choice names) vs s r s' h
  promiseJobPrepared s k s' h c' job realm xs sm rl r he hc hr :=
    promiseJobPrepared_law c s k s' c' job realm xs sm rl r h he hc hr
  jobCleanup k s s' h := jobCleanup_law k s s' h
  hookCompletion k xs s r s' h := .inl (hookCompletion_law c k xs s r s' h)
  privateElementSameKind := ⟨fun _ => Known.eNormal, fun k xs s r s' hk h => by rw [private_law hk h]; rfl⟩
  supportedImportAttributes := ⟨[Impl.strLit "type"], fun k xs s r s' hk h => by
    simp only [Host.answers, hook_of ((secOf_eq k).trans hk)] at h
    simp [hooks, Engine.Host.hooks, List.lookup, Run.boundary, Run.Res.boundary, listOf, alloc, bind, Run.bind, Run.Res.bind, pure,
      Run.pure] at h
    obtain ⟨rfl, rfl⟩ := h
    have hnew : (Engine.Model.ChunkedHeap.alloc s.heap
        (.list #[.str (Engine.Model.utf16 "type")] 0)).2.get s.heap.next =
        some (.list #[.str (Engine.Model.utf16 "type")] 0) :=
      Engine.Model.ChunkedHeap.alloc_get_self _ _
    simp [listElems, hnew]⟩
  getCodeForEval k xs s r s' hk h := .inl (codeForEval_law hk h)
  hasSourceTextAvailable := ⟨fun _ => .bool true, fun k xs s r s' hk h => source_law hk h⟩
  resizeArrayBuffer k a n s r s' hk h := by
    simp only [Host.answers, hook_of ((secOf_eq k).trans hk)] at h
    have hl : hooks.lookup "sec-hostresizearraybuffer" = some (fun _ _ => normalEnum "unhandled") := by
      simp [hooks, Engine.Host.hooks, List.lookup]
    rw [hl, Option.getD_some] at h
    unfold normalEnum Engine.Host.normalEnum at h
    revert h
    cases he : names.enum? "unhandled" <;> intro h
    · cases h
    · simp only [Run.boundary, Run.pure, Run.Res.boundary, Res.ok.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      refine ⟨fun _ _ hd => hd, fun e' hv hh => ?_⟩
      simp [normalValue, normal] at hv
      subst hv
      rw [idxOf?_getElem? he] at hh
      simp at hh
  listSeparator k xs s r s' hk h := ⟨(listSeparator_law hk h).1, _, (listSeparator_law hk h).2⟩
  additionalTimeout vs s r s' h := by
    simp [host, Engine.Host.host, Engine.Host.agentJobs, Known.pAgentNextJob, Known.pAgentPrepareJob, Known.pAgentCleanupJob, choice, Known.pWebBrowser, Known.pApprox, Known.pNaNEncoding, Known.pApproxInteger,
      Known.pHostChoice, Known.pHostInitializeBuiltinContext,
      Known.pAdditionalTimeout, Run.pure] at h
    exact ⟨h.2.symm, _, h.1.symm, by decide⟩
  timeZoneNameSuffix vs s r s' h := by
    simp [host, Engine.Host.host, Engine.Host.agentJobs, Known.pAgentNextJob, Known.pAgentPrepareJob, Known.pAgentCleanupJob, choice, Known.pWebBrowser, Known.pApprox, Known.pNaNEncoding, Known.pApproxInteger,
      Known.pHostChoice, Known.pHostInitializeBuiltinContext,
      Known.pAdditionalTimeout, Known.pTimeZoneNameSuffix, Run.pure] at h
    exact ⟨h.2.symm, _, h.1.symm, .inl (beq_self_eq_true _)⟩
  systemTimeZoneString vs s r s' h := by
    simp [host, Engine.Host.host, Engine.Host.agentJobs, Known.pAgentNextJob, Known.pAgentPrepareJob, Known.pAgentCleanupJob, choice, Known.pWebBrowser, Known.pApprox, Known.pNaNEncoding, Known.pApproxInteger,
      Known.pHostChoice, Known.pHostInitializeBuiltinContext,
      Known.pAdditionalTimeout, Known.pTimeZoneNameSuffix, Known.pSystemTimeZoneString, Run.pure] at h
    exact ⟨h.2.symm, _, h.1.symm, .inl (beq_self_eq_true _)⟩
  primaryTimeZoneId vs s r s' h := by
    simp [host, Engine.Host.host, Engine.Host.agentJobs, Known.pAgentNextJob, Known.pAgentPrepareJob, Known.pAgentCleanupJob, choice, Known.pWebBrowser, Known.pApprox, Known.pNaNEncoding, Known.pApproxInteger,
      Known.pHostChoice, Known.pHostInitializeBuiltinContext,
      Known.pAdditionalTimeout, Known.pTimeZoneNameSuffix, Known.pSystemTimeZoneString, Known.pTimeNow,
      Known.pSpinWaitHint, Known.pDiscardContextResources, Known.pCanAllocate, Known.pDebuggerEnabled,
      Known.pSupportsOnlyUTC, Known.pHasTimeZoneRules, Known.pAvailableNamedTimeZoneIds,
      Known.pIsNonPrimaryTimeZoneId, Known.pPrimaryTimeZoneId, Run.pure] at h
    exact ⟨h.2.symm, _, h.1.symm, .inl (beq_self_eq_true _)⟩
  timeNow vs s r s' h := by
    rw [choice_timeNow] at h
    obtain ⟨h1, h2⟩ := readClock_ok h
    exact ⟨h1, _, h2, clockNumIn_instant _ (.inl rfl)⟩
  spinWaitHint vs s r s' h := by
    simp [host, Engine.Host.host, Engine.Host.agentJobs, Known.pAgentNextJob, Known.pAgentPrepareJob, Known.pAgentCleanupJob, choice, Known.pWebBrowser, Known.pApprox, Known.pNaNEncoding, Known.pApproxInteger,
      Known.pHostChoice, Known.pHostInitializeBuiltinContext,
      Known.pAdditionalTimeout, Known.pTimeZoneNameSuffix, Known.pSystemTimeZoneString,
      Known.pTimeNow, Known.pSpinWaitHint, Run.pure, unused] at h
    exact ⟨h.2.symm, h.1.symm⟩
  discardContextResources vs s r s' h := by
    simp [host, Engine.Host.host, Engine.Host.agentJobs, Known.pAgentNextJob, Known.pAgentPrepareJob, Known.pAgentCleanupJob, choice, Known.pWebBrowser, Known.pApprox, Known.pNaNEncoding, Known.pApproxInteger,
      Known.pHostChoice, Known.pHostInitializeBuiltinContext,
      Known.pAdditionalTimeout, Known.pTimeZoneNameSuffix, Known.pSystemTimeZoneString,
      Known.pTimeNow, Known.pSpinWaitHint, Known.pDiscardContextResources, Run.pure, unused] at h
    exact ⟨h.2.symm, h.1.symm⟩
  selectAgent vs s r s' h := by
    have e : (host c).choice Known.pHostSelectAgent vs =
        selectNext (fun s => isRecordOf s "Agent Record") clusterSigs vs := by
      have : (fun s => names.isRecordOf s "Agent Record") = fun (s : State Impl) => isRecordOf s "Agent Record" :=
        funext fun s => funext (isRecordOf_names s "Agent Record")
      exact congrArg (selectNext · clusterSigs vs) this
    rw [e] at h
    exact selectNext_law h
  chooseReadsBytesFrom vs s r s' h := by
    have e : (host c).choice Known.pChooseReadsBytesFrom vs = scWrites isWriteEvent vs := by
      have : Engine.Host.isWriteIn names = fun (s : State Impl) e => isWriteEvent s e :=
        funext fun s => funext fun e => by
          simp only [Engine.Host.isWriteIn, isWriteEvent, isRecordOf_names]
      exact congrArg (scWrites · vs) this
    rw [e] at h
    exact scWrites_law h
  chooseReadsValid vs s r s' h := by
    have e : (host c).choice Known.pChooseReadsBytesFrom vs = scWrites isWriteEvent vs := by
      have : Engine.Host.isWriteIn names = fun (s : State Impl) e => isWriteEvent s e :=
        funext fun s => funext fun e => by
          simp only [Engine.Host.isWriteIn, isWriteEvent, isRecordOf_names]
      exact congrArg (scWrites · vs) this
    rw [e] at h
    exact MemoryModel.scWrites_valid fastIntFacts addrEq_iff h
  elapsedMono := elapsedMono_of_check rfl
  timeoutAfter := timeoutAfter_of_check rfl
  contextResources _ h := absurd h Bool.false_ne_true
  parseDateString vs s r s' h := parseDateString_law c vs s r s' h
  dateFormUTC x s r s' f h hfits hlegal _ hu := (parsesDates c).dateFormUTC h hfits hlegal hu
  dateFormLocal x s r s' f id h hfits hlegal hloc hu hz := by
    have hid : Impl.strEq id (Impl.strLit "UTC") = true := by
      rcases hz with ⟨-, he⟩ | ⟨hf, -⟩
      · exact he
      · rw [choice_onlyUTC c s] at hf; cases hf
    refine ⟨fun _ => ?_, fun l o hl ho => by rw [utc_noOffset id l hid hl] at ho; cases ho⟩
    have := (parsesDates c).dateFormUTC h hfits hlegal hu
    rw [DateForm.offsetMin_local hloc] at this
    simpa using this
  dateFormIllegal x s r s' f h hfits hill hu := (parsesDates c).dateFormIllegal h hfits hill hu
  canAllocate vs s r s' h := canAllocate_law c vs s r s' h
  debuggerEnabled vs s r s' h := by
    simp [host, Engine.Host.host, Engine.Host.agentJobs, Known.pAgentNextJob, Known.pAgentPrepareJob, Known.pAgentCleanupJob, choice, Known.pDebuggerEnabled, Known.pWebBrowser, Known.pApprox, Known.pNaNEncoding,
      Known.pApproxInteger, Known.pHostChoice, Known.pHostInitializeBuiltinContext,
      Known.pAdditionalTimeout, Known.pTimeZoneNameSuffix,
      Known.pSystemTimeZoneString, Known.pTimeNow, Known.pSpinWaitHint, Known.pDiscardContextResources,
      Known.pCanAllocate, Run.pure] at h
    exact ⟨h.2.symm, false, h.1.symm⟩
  debuggerAction vs s r s' h := by
    simp [host, Engine.Host.host, Engine.Host.agentJobs, Known.pAgentNextJob, Known.pAgentPrepareJob, Known.pAgentCleanupJob, choice, Known.pDebuggerAction, Known.pDebuggerEnabled, Known.pWebBrowser, Known.pApprox,
      Known.pNaNEncoding, Known.pApproxInteger, Known.pHostChoice, Known.pHostInitializeBuiltinContext,
      Known.pAdditionalTimeout, Known.pTimeZoneNameSuffix,
      Known.pSystemTimeZoneString, Known.pTimeNow, Known.pSpinWaitHint, Known.pDiscardContextResources,
      Known.pCanAllocate, Known.pHostJobCallbackData, Known.pHostPrepareCallJobCallback, Known.pHostCleanupCallJobCallback, Known.pSupportsOnlyUTC, Known.pHasTimeZoneRules, Known.pAvailableNamedTimeZoneIds,
      Known.pIsNonPrimaryTimeZoneId, Known.pPrimaryTimeZoneId, Known.pLastTransitionBefore, Known.pHostGlobalObject, Known.pHostThisValue, Known.pMayCleanup,
      Known.pHostGlobalProperties, Known.pHostReportCleanupError, Known.pHostReportErrors, Known.pForInStep, Known.pPropertyOrder, Known.pOmitSharedArrayBuffer,
      Known.pHostSupportsOptional, Known.pEscapePattern, Known.pLocaleUppercase,
      Known.pLocaleLowercase, Known.pLocaleCompare, Known.pLocaleNumberString, Known.pLocaleDateString, Known.pNativeFunctionSource,
      Known.pSortStep, Known.pParseDateString, Known.pSuspendAgentUntil, Known.pExpandedYearForm,
      Known.pHostExtendIntrinsics, Known.pHostExtendObject, Known.pHostSelectAgent, Known.pAgentWoken,
      Known.pAgentTimeout, Known.pWakeAgent, Known.pChooseReadsBytesFrom, Known.pApproxPower, Known.pBigIntTooLarge,
      Known.pStringTooLarge, Run.stop] at h
  nativeFunctionSource f s r s' h := nativeFunctionSource_law c f s r s' h
  escapePattern p fl s r s' h := by
    simpa only [choice_escape] using escapeChoice_law (by rwa [choice_escape] at h)
  supportsOnlyUTC s r s' h := by
    simp [host, Engine.Host.host, Engine.Host.agentJobs, Known.pAgentNextJob, Known.pAgentPrepareJob, Known.pAgentCleanupJob, choice,
      Known.pAdditionalTimeout, Known.pTimeZoneNameSuffix, Known.pSystemTimeZoneString,
      Known.pTimeNow, Known.pSpinWaitHint, Known.pDiscardContextResources, Known.pCanAllocate,
      Known.pDebuggerEnabled,
      Known.pWebBrowser, Known.pApprox, Known.pNaNEncoding, Known.pApproxInteger, Known.pHostChoice,
      Known.pHostInitializeBuiltinContext, Known.pSupportsOnlyUTC, Run.pure] at h
    exact ⟨h.2.symm, true, h.1.symm⟩
  mathRandom k xs s r s' hc h := random_law ((secOf_eq k).trans hc) h
  hostGlobalObject vs s r s' h := by
    simp [host, Engine.Host.host, Engine.Host.agentJobs, Known.pAgentNextJob, Known.pAgentPrepareJob, Known.pAgentCleanupJob, choice, Known.pWebBrowser, Known.pApprox, Known.pNaNEncoding, Known.pApproxInteger,
      Known.pHostChoice, Known.pHostInitializeBuiltinContext,
      Known.pAdditionalTimeout, Known.pTimeZoneNameSuffix,
      Known.pSystemTimeZoneString, Known.pTimeNow, Known.pSpinWaitHint, Known.pDiscardContextResources,
      Known.pCanAllocate, Known.pDebuggerEnabled, Known.pSupportsOnlyUTC, Known.pHasTimeZoneRules,
      Known.pAvailableNamedTimeZoneIds, Known.pIsNonPrimaryTimeZoneId, Known.pPrimaryTimeZoneId, Known.pLastTransitionBefore,
      Known.pHostGlobalObject, Known.pHostThisValue,
      Known.pMayCleanup, Run.pure] at h
    obtain ⟨rfl, rfl⟩ := h
    exact .inl ⟨rfl, rfl⟩
  hostThisValue vs s r s' h := by
    simp [host, Engine.Host.host, Engine.Host.agentJobs, Known.pAgentNextJob, Known.pAgentPrepareJob, Known.pAgentCleanupJob, choice, Known.pWebBrowser, Known.pApprox, Known.pNaNEncoding, Known.pApproxInteger,
      Known.pHostChoice, Known.pHostInitializeBuiltinContext,
      Known.pAdditionalTimeout, Known.pTimeZoneNameSuffix,
      Known.pSystemTimeZoneString, Known.pTimeNow, Known.pSpinWaitHint, Known.pDiscardContextResources,
      Known.pCanAllocate, Known.pDebuggerEnabled, Known.pSupportsOnlyUTC, Known.pHasTimeZoneRules,
      Known.pAvailableNamedTimeZoneIds, Known.pIsNonPrimaryTimeZoneId, Known.pPrimaryTimeZoneId, Known.pLastTransitionBefore,
      Known.pHostGlobalObject, Known.pHostThisValue,
      Known.pMayCleanup, Run.pure] at h
    obtain ⟨rfl, rfl⟩ := h
    exact .inl ⟨rfl, rfl⟩
  hostGlobalProperties realm g s r s' h := by
    rw [choice_globalProps] at h
    exact ⟨(globalProps_law none realm g s r s' h).1, (globalProps_law none realm g s r s' h).2.1⟩
  hostReportCleanupError vs s r s' h := by
    simp [host, Engine.Host.host, Engine.Host.agentJobs, Known.pAgentNextJob, Known.pAgentPrepareJob, Known.pAgentCleanupJob, choice, Known.pWebBrowser, Known.pApprox, Known.pNaNEncoding, Known.pApproxInteger,
      Known.pHostChoice, Known.pHostInitializeBuiltinContext,
      Known.pAdditionalTimeout, Known.pTimeZoneNameSuffix,
      Known.pSystemTimeZoneString, Known.pTimeNow, Known.pSpinWaitHint, Known.pDiscardContextResources,
      Known.pCanAllocate, Known.pDebuggerEnabled, Known.pSupportsOnlyUTC, Known.pHasTimeZoneRules,
      Known.pAvailableNamedTimeZoneIds, Known.pIsNonPrimaryTimeZoneId, Known.pPrimaryTimeZoneId, Known.pLastTransitionBefore,
      Known.pHostGlobalObject, Known.pHostThisValue,
      Known.pMayCleanup, Known.pHostGlobalProperties, Known.pHostReportCleanupError, Known.pHostReportErrors, Run.pure, unused] at h
    exact h.1.symm
  hostReportErrors vs s r s' h := by
    simp [host, Engine.Host.host, Engine.Host.agentJobs, Known.pAgentNextJob, Known.pAgentPrepareJob, Known.pAgentCleanupJob, choice, Known.pWebBrowser, Known.pApprox, Known.pNaNEncoding, Known.pApproxInteger,
      Known.pHostChoice, Known.pHostInitializeBuiltinContext,
      Known.pAdditionalTimeout, Known.pTimeZoneNameSuffix,
      Known.pSystemTimeZoneString, Known.pTimeNow, Known.pSpinWaitHint, Known.pDiscardContextResources,
      Known.pCanAllocate, Known.pDebuggerEnabled, Known.pSupportsOnlyUTC, Known.pHasTimeZoneRules,
      Known.pAvailableNamedTimeZoneIds, Known.pIsNonPrimaryTimeZoneId, Known.pPrimaryTimeZoneId, Known.pLastTransitionBefore,
      Known.pHostGlobalObject, Known.pHostThisValue,
      Known.pMayCleanup, Known.pHostGlobalProperties, Known.pHostReportCleanupError, Known.pHostReportErrors, Run.pure, unused] at h
    exact h.1.symm
  mayCleanup reg s r s' h := by
    simp [host, Engine.Host.host, Engine.Host.agentJobs, Known.pAgentNextJob, Known.pAgentPrepareJob, Known.pAgentCleanupJob, choice, Known.pWebBrowser, Known.pApprox, Known.pNaNEncoding, Known.pApproxInteger,
      Known.pHostChoice, Known.pHostInitializeBuiltinContext,
      Known.pAdditionalTimeout, Known.pTimeZoneNameSuffix,
      Known.pSystemTimeZoneString, Known.pTimeNow, Known.pSpinWaitHint, Known.pDiscardContextResources,
      Known.pCanAllocate, Known.pDebuggerEnabled, Known.pSupportsOnlyUTC, Known.pHasTimeZoneRules,
      Known.pAvailableNamedTimeZoneIds, Known.pIsNonPrimaryTimeZoneId, Known.pPrimaryTimeZoneId, Known.pLastTransitionBefore,
      Known.pHostGlobalObject, Known.pHostThisValue,
      Known.pMayCleanup, Run.pure] at h
    exact ⟨h.2.symm, .inl h.1.symm⟩
  sortStep _ _ _ _ _ _ _ hr hc := sortStepBy_law idx_ofNat (host_sortStep c) sortCall_inj_fast sortDone_ne_call_fast
    hr (by rwa [host_sortStep] at hc)
  sortStepEnds := sortStepBy_ends idx_ofNat (host_sortStep c) sortCall_inj_fast sortDone_ne_call_fast
  forInStep obj h s r s' hc es he _ := by
    have hq : (host c).choice Known.pForInStep [.obj obj, h] = forInChoice [.obj obj, h] := by
      have e : (host c).choice Known.pForInStep [.obj obj, h] =
          forInChoiceBy Engine.Host.forInHistFast [.obj obj, h] := rfl
      rw [e, forInHistFast_eq]; rfl
    rw [hq] at hc
    exact forInChoice_law (fun _ _ => beq_iff_eq) (fun _ _ => beq_iff_eq) obj h s r s' hc es he
  propertyOrder o l s r s' h := documentOrder_perm o l s r s' h
  omitSharedArrayBuffer := ⟨false, fun vs s r s' h => by
    have hq : (host c).choice Known.pOmitSharedArrayBuffer vs = Run.pure (.bool false) := rfl
    simp only [hq, Run.pure, Res.ok.injEq] at h
    exact ⟨h.2.symm, h.1.symm⟩⟩
  localeCase q l s r s' hq h := by
    rcases hq with rfl | rfl
    · have e : (host c).choice Known.pLocaleUppercase [l] = caseAsDefault Impl.toUpper [l] := rfl
      rw [e] at h
      exact caseAsDefault_law _ l s r s' h
    · have e : (host c).choice Known.pLocaleLowercase [l] = caseAsDefault Impl.toLower [l] := rfl
      rw [e] at h
      exact caseAsDefault_law _ l s r s' h
  localeCompare := by
    obtain ⟨le, h1, h2, h3⟩ := compareBy_law (M := Impl) Engine.Host.fastKey (.inr ⟨_, rfl, rfl⟩) (.inr ⟨_, rfl, rfl⟩) rfl
    refine ⟨le, h1, h2, fun a b s r s' h => h3 a b s r s' ?_⟩
    have e : (host c).choice Known.pLocaleCompare [.str a, .str b] = compareBy Engine.Host.fastKey [.str a, .str b] := rfl
    rwa [e] at h
  localeNumberString vs s r s' h := by
    have e : (host c).choice Known.pLocaleNumberString vs = Run.pure (.enum Known.eEmpty) := rfl
    simp only [e, Run.pure, Res.ok.injEq] at h
    exact ⟨h.2.symm, .inl h.1.symm⟩
  localeDateString k v s r s' h := by
    have e : (host c).choice Known.pLocaleDateString [k, v] = dateAsDefault [k, v] := rfl
    rw [e] at h
    exact dateAsDefault_law k v s r s' h
  expandedYearForm vs s r s' h := by
    have hq : (host c).choice Known.pExpandedYearForm vs = Run.pure (.bool false) := rfl
    simp only [hq, Run.pure, Res.ok.injEq] at h
    exact ⟨h.2.symm, false, h.1.symm⟩
  hostExtendIntrinsics vs s r s' h := by
    have hq : (host c).choice Known.pHostExtendIntrinsics vs = Run.pure unused := rfl
    simp only [hq, Run.pure, Res.ok.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨rfl, onlyAdds_refl _ _, fun _ _ ps' _ h _ _ hk => ⟨ps', h, hk⟩⟩
  hostExtendObject o s r s' h := by
    have hq : (host c).choice Known.pHostExtendObject [.obj o] = Run.pure unused := rfl
    simp only [hq, Run.pure, Res.ok.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨rfl, onlyAdds_refl _ _, fun _ _ ps' _ h _ _ hk => ⟨ps', h, hk⟩⟩
  webBrowser := webBrowser_const false fun _ => rfl
  webBrowserSupports := webBrowserSupports_const false fun _ => rfl
  callJobCallback := (jobCallback_laws (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)).1
  jobCallbackDefault := (jobCallback_laws (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)).2
  collect _ _ _ h := Collected.of_pure h
  agentFixed s s' h := (fast_stepKeeps c s s' h).1.agentKept
  approx vs s r s' h := by
    have hq : (host c).choice Known.pApprox vs = Prims.Numbers.numberFor vs := rfl
    rw [hq] at h
    unfold Prims.Numbers.numberFor at h
    split at h <;> (try split at h) <;> first | (cases h; exact ⟨rfl, _, rfl⟩) | cases h
  approxPower vs s r s' h := by
    have hq : (host c).choice Known.pApproxPower vs = Engine.Host.approxPower vs := rfl
    rw [hq] at h
    unfold Engine.Host.approxPower at h
    split at h <;> first | (cases h; exact ⟨rfl, _, rfl⟩) | cases h
  bigIntTooLarge vs s r s' h := by
    have hq : (host c).choice Known.pBigIntTooLarge vs = Engine.Host.bigIntTooLarge vs := rfl
    rw [hq] at h
    unfold Engine.Host.bigIntTooLarge at h
    split at h <;> first | (cases h; exact ⟨rfl, _, rfl⟩) | cases h
  stringTooLarge vs s r s' h := by
    have hq : (host c).choice Known.pStringTooLarge vs = Engine.Host.stringTooLarge vs := rfl
    rw [hq] at h
    unfold Engine.Host.stringTooLarge at h
    split at h
    · split at h <;> cases h; exact ⟨rfl, _, rfl⟩
    · cases h
  hostChoice vs s r s' h := by
    have hq : (host c).choice Known.pHostChoice vs = Engine.Host.pairChoice vs := rfl
    rw [hq] at h
    unfold Engine.Host.pairChoice at h
    split at h <;> first | (cases h; exact ⟨rfl, by simp⟩) | cases h
  hostInitializeBuiltinContext ctx s r s' h := by
    have hq : (host c).choice Known.pHostInitializeBuiltinContext [.ref ctx] = Run.pure unused := rfl
    rw [hq] at h
    cases h
    exact ⟨rfl, rfl, fun _ _ _ h => h, fun _ fs h => ⟨fs, h, fun _ _ => rfl⟩⟩
  invariantsKept s s' h := (fast_stepKeeps c s s' h).2

/-- info: 'Engine.SpecHost.wf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms wf

/-- info: 'Engine.SpecHost.fast_stepKeeps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms fast_stepKeeps

end Engine.SpecHost
