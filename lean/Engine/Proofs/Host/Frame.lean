module

public import Engine.Host.SpecOpts
public import Engine.Proofs.Host.Inputs
public import Engine.Proofs.Host.WF
public import Engine.Proofs.Host.OptsOMap

@[expose] public section

/-!
# What the test host's steps change

`resizeInPlace_stepKeeps`: HostResizeArrayBuffer in place (`resizeInPlace`) changes only _buffer_'s Data Block
and its data slots, which keeps every object to its invariants (`StepKeeps`); `hookIn_stepKeeps`,
`choiceIn_keeps` and `nextJobIn_stepKeeps`: the same of `hostIn σ`'s hooks, choices and next job.
-/

namespace Engine.SpecHost

open Ecma Engine

/-! The test host's definitions at Ecma.Gen's names (the prover's `JSSpec.Host.Opts`; only the proofs use them). -/

/-- The field ids named `n`. -/
abbrev fieldsNamed (n : String) : List FieldId := names.fieldsNamed n

abbrev nextJobs := Engine.Host.nextJobs names
abbrev resizeCand := Engine.Host.resizeCand names
abbrev resizeInPlace := Engine.Host.resizeInPlace names

theorem fieldsNamed_get {f : FieldId} {n : String} (h : f ∈ fieldsNamed n) : Gen.fields[f]? = some n := by
  simp only [fieldsNamed, names, List.mem_filter, beq_iff_eq] at h
  exact h.2

/-- `normalEnum` ends where it starts. -/
theorem normalEnum_state (n : String) (t : State Impl) (r : Val Impl) (s' : State Impl)
    (h : Run.Res.boundary (normalEnum n t) = .ok r s') : s' = t := by
  unfold normalEnum Engine.Host.normalEnum at h
  revert h
  cases names.enum? n <;> intro h
  · cases h
  · simp only [Run.pure, Run.Res.boundary, Res.ok.injEq] at h
    exact h.2.symm

/-- The names of [[Extensible]] and [[Prototype]]. -/
theorem fields_ext_proto :
    Gen.fields[Known.fExtensible]? = some "Extensible" ∧ Gen.fields[Known.fPrototype]? = some "Prototype" := by
  decide +kernel

/-- An ArrayBuffer's data slots, which HostResizeArrayBuffer resizes. -/
def bufferField (f : FieldId) : Prop :=
  Gen.fields[f]? = some "ArrayBufferData" ∨ Gen.fields[f]? = some "ArrayBufferByteLength" ∨
    Gen.fields[f]? = some "ArrayBufferByteLengthData"

/-- A block cell written at `d` and the slots of `a` changed only at data slots keep the agent, each Record cell
and every object to its invariants. -/
theorem resize_stepKeeps {s : State Impl} {a d : Nat} {sl sl' : Impl.Rec (Val Impl)}
    {ps : Impl.Props (Val Impl)} {bs : Impl.Bytes} (L : Cell Impl)
    (ha : Impl.heapGet s.heap a = some (.object sl ps))
    (hdx : Impl.heapGet s.heap d = some (.block bs))
    (hsl : ∀ g, ¬bufferField g → Impl.recGet sl' g = Impl.recGet sl g) :
    StepKeeps s { s with heap := Impl.heapSet (Impl.heapSet s.heap d L) a (.object sl' ps) } := by
  have ad : a ≠ d := fun e => by subst e; rw [ha] at hdx; cases hdx
  have hget : ∀ p, p ≠ a → p ≠ d →
      Impl.heapGet (Impl.heapSet (Impl.heapSet s.heap d L) a (.object sl' ps)) p = Impl.heapGet s.heap p :=
    fun p h1 h2 => by rw [Engine.Host.heapGet_set_ne _ _ (Ne.symm h1), Engine.Host.heapGet_set_ne _ _ (Ne.symm h2)]
  have hat : Impl.heapGet (Impl.heapSet (Impl.heapSet s.heap d L) a (.object sl' ps)) a = some (.object sl' ps) :=
    Engine.Host.heapGet_set_self (by rw [Engine.Host.heapGet_set_ne _ _ (Ne.symm ad)]; exact ha)
  have hrec : ∀ q t fs, Impl.heapGet s.heap q = some (.record t fs) →
      Impl.heapGet ({ s with heap := Impl.heapSet (Impl.heapSet s.heap d L) a (.object sl' ps) } : State Impl).heap q =
        some (.record t fs) := fun q t fs hq => by
    show Impl.heapGet (Impl.heapSet (Impl.heapSet s.heap d L) a (.object sl' ps)) q = _
    rw [hget q (fun e => by subst e; rw [ha] at hq; cases hq) (fun e => by subst e; rw [hdx] at hq; cases hq)]
    exact hq
  have hext : ¬bufferField Known.fExtensible := by unfold bufferField; rw [fields_ext_proto.1]; decide
  have hproto : ¬bufferField Known.fPrototype := by unfold bufferField; rw [fields_ext_proto.2]; decide
  refine ⟨⟨rfl, hrec⟩, fun p sl₀ ps₀ hp => ?_⟩
  by_cases hpa : p = a
  · subst hpa
    rw [ha] at hp
    cases hp
    exact ⟨sl', ps, hat, .inl (hsl _ hext), fun _ => ⟨hsl _ hproto, fun _ h => h⟩,
      fun _ fs h _ => ⟨fs, attrsAt_keepsRec hrec h, attrsKept_refl fs⟩⟩
  · have hpd : p ≠ d := fun e => by subst e; rw [hdx] at hp; cases hp
    exact ⟨sl₀, ps₀, by show Impl.heapGet _ p = _; rw [hget p hpa hpd]; exact hp, objKept_keepsRec hrec sl₀ ps₀⟩

/-- `resizeCand`'s state keeps HostResizeArrayBuffer's frame, the agent and each Record cell. -/
theorem resizeCand_stepKeeps (xs : List (Val Impl)) (s t : State Impl) (h : resizeCand xs s = some t) :
    StepKeeps s t := by
  unfold resizeCand Engine.Host.resizeCand at h
  generalize hF : (names.fieldsNamed "ArrayBufferData").head? = F at h
  generalize hB : names.fieldsNamed "ArrayBufferByteLength" = B at h
  split at h
  · rename_i a i
    revert h
    cases ha : Impl.heapGet s.heap a with
    | none => intro h; cases h
    | some c =>
      cases c with
      | object sl ps =>
        cases F with
        | none => intro h; cases h
        | some f =>
          dsimp only [Option.bind]
          cases hsd : Model.WMap.get sl f with
          | none => intro h; cases h
          | some v =>
            cases v with
            | ref d =>
              dsimp only
              cases hdx : s.heap.get d with
              | none => intro h; cases h
              | some c' =>
                cases c' with
                | block bs =>
                  intro h
                  cases h
                  refine resize_stepKeeps _ ha hdx fun g hg => ?_
                  rw [Engine.Host.recGet_resized, if_neg]
                  intro hm
                  rw [← hB] at hm
                  exact hg (.inr (.inl (fieldsNamed_get hm)))
                | _ => intro h; cases h
            | _ => intro h; cases h
      | _ => intro h; cases h
  · cases h

/-- HostResizeArrayBuffer in place changes only _buffer_'s Data Block and data slots. -/
theorem resizeInPlace_stepKeeps (xs : List (Val Impl)) (s : State Impl) (r : Val Impl) (s' : State Impl)
    (h : Run.boundary (resizeInPlace xs) s = .ok r s') : StepKeeps s s' := by
  change Run.Res.boundary (resizeInPlace xs s) = _ at h
  unfold resizeInPlace Engine.Host.resizeInPlace at h
  split at h
  · rename_i t hc
    split at h
    · rw [normalEnum_state _ _ _ _ h]; exact resizeCand_stepKeeps _ s t hc
    · rw [normalEnum_state _ _ _ _ h]; exact (Keeps.refl s).stepKeeps
  · rw [normalEnum_state _ _ _ _ h]; exact (Keeps.refl s).stepKeeps

/-- The test host's host-defined operations keep the agent, each Record cell and every object. -/
theorem hookIn_stepKeeps (σ : Choices) (o : HostOpts) (c : Cells) (k : ClauseId) (xs : List (Val Impl))
    (s : State Impl) (r : Val Impl) (s' : State Impl) (h : (hostIn σ o c).answers k xs s r s') : StepKeeps s s' := by
  unfold Host.answers at h
  rcases o with ⟨_ | N, b, cb, w, ab⟩ <;> simp only [hostIn, Engine.Host.hostIn, Engine.Host.hookIn, names_clause] at h <;>
    by_cases hb : (b && secOf k == some resizeClause) = true <;> simp only [hb, ↓reduceIte] at h
  · exact resizeInPlace_stepKeeps xs s r s' h
  · exact fast_hook_stepKeeps (c := c) h
  · exact resizeInPlace_stepKeeps xs s r s' h
  · by_cases hr : (secOf k == some randomClause) = true <;> simp only [hr, ↓reduceIte] at h
    · exact (KeepsR.boundary (KeepsR.ok fun _ => ⟨_, rfl⟩) h).stepKeeps
    · exact fast_hook_stepKeeps (c := c) h

/-- The test host's next job leaves the state as it was. -/
theorem nextJobIn_keeps (σ : Choices) (o : HostOpts) : KeepsR (nextJobIn σ o) := by
  rcases o with ⟨_ | N, b, cb, w, ab⟩
  · exact nextJob_keeps
  · exact KeepsR.ok fun _ => ⟨_, rfl⟩

/-- HostSelectAgent by `σ` leaves the state as it was. -/
theorem selectIn_keeps (isAgent : State Impl → Val Impl → Bool) (xs : State Impl → List (Val Impl))
    (σ : Choices) (vs : List (Val Impl)) : KeepsR (selectIn isAgent xs σ vs) := by
  fun_cases selectIn isAgent xs σ vs
  · intro s; dsimp only; split <;> exact Keeps.refl s
  · exact KeepsR.stop _

/-- ChooseReadsBytesFrom by `σ` keeps every cell and the rest of the state but its new List. -/
theorem readsIn_keeps (isWrite : State Impl → Val Impl → Bool) (σ : Choices) (vs : List (Val Impl)) :
    KeepsR (readsIn isWrite σ vs) := by
  intro s; unfold readsIn; split
  · dsimp only; split
    · split
      · exact KeepsR.listOf fast_allocKeeps _ s
      · trivial
    · trivial
  · trivial

/-- The options' choices but HostGlobalProperties keep every cell and the rest of the state. -/
theorem fast_choiceIn_keeps (σ : Choices) (o : HostOpts) (q : PrimId) (vs : List (Val Impl))
    (hg : q ≠ Known.pHostGlobalProperties) : KeepsR (choiceIn σ o q vs) := by
  simp only [choiceIn, Engine.Host.choiceIn]
  split
  · exact KeepsR.pure _
  · split
    · exact absurd (beq_iff_eq.mp ‹(q == Known.pHostGlobalProperties) = true›) hg
    · split
      · exact selectIn_keeps _ _ σ vs
      · split
        · exact readsIn_keeps _ σ vs
        · rcases o with ⟨_ | N, b, cb, w, ab⟩
          · exact fast_choice_keeps q vs hg
          · intro s₀
            simp only [Engine.Host.seededChoiceIn]
            repeat' (first
              | exact Keeps.refl _ | trivial | exact readClock_keeps _ _ | exact fast_choice_keeps q vs hg _ | split)

/-- The test host's choices but HostGlobalProperties, AgentPrepareJob and AgentCleanupJob keep every cell
and the rest of the state. -/
theorem choiceIn_keeps (σ : Choices) (o : HostOpts) (c : Cells) (q : PrimId) (vs : List (Val Impl))
    (hg : q ≠ Known.pHostGlobalProperties) (h1 : q ≠ Known.pAgentPrepareJob) (h2 : q ≠ Known.pAgentCleanupJob) :
    KeepsR ((hostIn σ o c).choice q vs) :=
  agentJobs_keeps c (nextJobIn_keeps σ o) (fast_choiceIn_keeps σ o q vs hg) h1 h2

/-- The test host's next job leaves the state as it was. -/
theorem nextJobIn_same (σ : Choices) (o : HostOpts) (c : Cells) (s : State Impl) (k : Option Nat) (s' : State Impl)
    (h : (hostIn σ o c).nextJob s = .ok k s') : s' = s := by
  rcases o with ⟨_ | N, b, cb, w, ab⟩
  · exact nextJob_same (checkElapsed_ok h).1
  · simp only [hostIn, Engine.Host.hostIn] at h
    have h := (checkElapsed_ok h).1
    simp only [Engine.Host.nextJobIn, Engine.Host.seededNextJobIn, Res.ok.injEq] at h
    exact h.2.symm

/-- The test host's next job keeps the agent, each Record cell and every object. -/
theorem nextJobIn_stepKeeps (σ : Choices) (o : HostOpts) (c : Cells) (s : State Impl) (k : Option Nat)
    (s' : State Impl) (h : (hostIn σ o c).nextJob s = .ok k s') : StepKeeps s s' := by
  rw [nextJobIn_same σ o c s k s' h]
  exact (Keeps.refl s).stepKeeps

end Engine.SpecHost
