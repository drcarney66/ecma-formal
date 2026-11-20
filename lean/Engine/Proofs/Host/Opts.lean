module

public import Engine.Host.SpecOpts
public import Engine.Proofs.Host.WF
public import Engine.Proofs.Host.Frame
public import Engine.Proofs.Host.Inputs
public import Engine.Proofs.Host.Writes

@[expose] public section

/-!
# The test host's laws, over Ecma.Data

`wfByIn`: `hostIn σ o c` (`Proofs/Host/Inputs.lean`) satisfies the host laws for every option set and every
input `σ` whose reads are valid (`ReadsValid`, law L2 only); HostSelectAgent's law (`selectAgentIn`) and
ChooseReadsBytesFrom's L1 (`chooseReadsIn`) hold at every σ. `wfBy`: `hostBy o c`, the instance at
`σOf o`.
-/

namespace Engine.SpecHost

open Ecma Engine

theorem mem_fieldsNamed {f : FieldId} {n : String} (h : Gen.fields[f]? = some n) : f ∈ fieldsNamed n := by
  simp only [fieldsNamed, names, List.mem_filter, List.mem_range, h, beq_self_eq_true, and_true]
  exact (Array.getElem?_eq_some_iff.mp h).1

/-! The host laws for every option set and every input. -/

/-- The test host's next job is its options' next job, where `elapsedOk` checks it. -/
theorem hostIn_checked {σ : Choices} {o : HostOpts} {c : Cells} {s : State Impl} {k : Option Nat}
    {s' : State Impl} (h : (hostIn σ o c).nextJob s = .ok k s') :
    nextJobIn σ o s = .ok k s' ∧ elapsedOk s.hostLog k (Engine.Host.elapsedIn names σ o s) = true :=
  checkElapsed_ok h

/-- The test host's choices but the agents' job prims are its options' and inputs' (`choiceIn`). -/
theorem hostIn_choice_of (σ : Choices) (o : HostOpts) (c : Cells) {p : PrimId} (h1 : p ≠ Known.pAgentNextJob)
    (h2 : p ≠ Known.pAgentPrepareJob) (h3 : p ≠ Known.pAgentCleanupJob) : (hostIn σ o c).choice p = choiceIn σ o p := by
  funext vs
  show Engine.Host.agentJobs names c (nextJobIn σ o) (choiceIn σ o) p vs = _
  unfold Engine.Host.agentJobs
  rw [beq_false_of_ne h1, beq_false_of_ne h2, beq_false_of_ne h3]
  simp only [Bool.false_eq_true, ↓reduceIte]

/-- The host's choices but the agents' job prims are `choice`'s. -/
theorem host_choice_of (c : Cells) {p : PrimId} (h1 : p ≠ Known.pAgentNextJob)
    (h2 : p ≠ Known.pAgentPrepareJob) (h3 : p ≠ Known.pAgentCleanupJob) : (host c).choice p = Engine.Host.choice names p := by
  funext vs
  show Engine.Host.agentJobs names c nextJob (Engine.Host.choice names) p vs = _
  unfold Engine.Host.agentJobs
  rw [beq_false_of_ne h1, beq_false_of_ne h2, beq_false_of_ne h3]
  simp only [Bool.false_eq_true, ↓reduceIte]

/-- The choices no option or input changes: `fixedPrim`'s but HostSelectAgent and ChooseReadsBytesFrom. -/
def fixedIn (p : PrimId) : Bool := fixedPrim p && p != Known.pHostSelectAgent && p != Known.pChooseReadsBytesFrom

theorem choiceIn_eq (σ : Choices) (o : HostOpts) (c : Cells) {p : PrimId} (hp : fixedIn p = true)
    (vs : List (Val Impl)) : (hostIn σ o c).choice p vs = (host c).choice p vs := by
  simp only [fixedIn, fixedPrim, Bool.and_eq_true, bne_iff_ne, ne_eq] at hp
  obtain ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩ := hp
  by_cases e2 : p = Known.pAgentPrepareJob
  · subst e2; rfl
  by_cases e3 : p = Known.pAgentCleanupJob
  · subst e3; rfl
  rw [hostIn_choice_of σ o c h6 e2 e3, host_choice_of c h6 e2 e3]
  rcases o with ⟨_ | N, b, cb, w, ab⟩ <;> funext s <;>
    simp [choiceIn, Engine.Host.choiceIn, seededChoiceIn, Engine.Host.seededChoiceIn, h1, h2, h3, h4, h5, h7, h8]

/-- HostGlobalProperties gives `$262` its *"IsHTMLDDA"* by `ddaBy`. -/
theorem choiceIn_globalProps (σ : Choices) (o : HostOpts) (c : Cells) :
    (hostIn σ o c).choice Known.pHostGlobalProperties = Engine.Host.globalProps (Engine.Host.ddaBy names o) := rfl

/-- With a seed, the choices but the schedule, the reads, WebBrowser and HostGlobalProperties are `seededChoiceIn`. -/
theorem choiceIn_seed (σ : Choices) {o : HostOpts} {n : Nat} (ho : o.seed = some n) {p : PrimId}
    (h1 : p ≠ Known.pWebBrowser) (h2 : p ≠ Known.pHostGlobalProperties) (h3 : p ≠ Known.pHostSelectAgent)
    (h4 : p ≠ Known.pChooseReadsBytesFrom) : choiceIn σ o p = seededChoiceIn names σ p := by
  simp only [choiceIn, Engine.Host.choiceIn, beq_false_of_ne h1, beq_false_of_ne h2, beq_false_of_ne h3,
    beq_false_of_ne h4, ho, Bool.false_eq_true, ↓reduceIte]

/-- Without a seed, the time is the fixed host's. -/
theorem choiceTimeNow (σ : Choices) (b cb : Bool) (w : Bool) (ab : List String) (c : Cells) :
    (hostIn σ ⟨none, b, cb, w, ab⟩ c).choice Known.pTimeNow = (host c).choice Known.pTimeNow := rfl

/-- With a seed, TimeNow is the seeded clock over `σ`, checked against its taken timeout jobs. -/
theorem seededTimeNow (σ : Choices) (N : Nat) (b cb : Bool) (w : Bool) (ab : List String) (c : Cells)
    (vs : List (Val Impl)) :
    (hostIn σ ⟨some N, b, cb, w, ab⟩ c).choice Known.pTimeNow vs = readClock (seededNumIn σ) := by
  rw [hostIn_choice_of (p := Known.pTimeNow) _ _ c (by decide) (by decide) (by decide),
    choiceIn_seed σ rfl (by decide) (by decide) (by decide) (by decide)]
  funext s
  simp only [Engine.Host.seededChoiceIn, beq_false_of_ne (show Known.pTimeNow ≠ Known.pHostChoice by decide),
    beq_self_eq_true, Bool.false_eq_true, ↓reduceIte]

/-- Without a seed, CanAllocate is the fixed host's. -/
theorem choiceCanAllocate (σ : Choices) (b cb : Bool) (w : Bool) (ab : List String) (c : Cells) :
    (hostIn σ ⟨none, b, cb, w, ab⟩ c).choice Known.pCanAllocate = (host c).choice Known.pCanAllocate := rfl

theorem hookIn_eq (σ : Choices) (o : HostOpts) (c : Cells) {k : ClauseId} (h1 : secOf k ≠ some resizeClause)
    (h2 : secOf k ≠ some randomClause) (vs : List (Val Impl)) : (hostIn σ o c).hook k vs = (host c).hook k vs := by
  have e1 : (secOf k == some resizeClause) = false := by simpa using h1
  have e2 : (secOf k == some randomClause) = false := by simpa using h2
  rcases o with ⟨_ | N, b, cb, w, ab⟩ <;> simp only [hostIn, Engine.Host.hostIn, host, Engine.Host.host, Engine.Host.hookIn, names_clause, e1, e2, Bool.and_false, Bool.false_eq_true, ↓reduceIte]

theorem answers_eq (σ : Choices) (o : HostOpts) (c : Cells) {k : ClauseId} {sec : String}
    (hk : Gen.clauses[k]? = some sec) (h1 : sec ≠ resizeClause) (h2 : sec ≠ randomClause) {xs : List (Val Impl)}
    {s : State Impl} {r : Val Impl} {s' : State Impl} : (hostIn σ o c).answers k xs s r s' ↔ (host c).answers k xs s r s' := by
  have hs : secOf k = some sec := (secOf_eq k).trans hk
  simp only [Host.answers, hookIn_eq σ o c (by rw [hs]; simpa using h1) (by rw [hs]; simpa using h2)]

/-- Two different HostEnqueue…Job operations are never one call. -/
theorem free_not_called {log : List (HostCall Impl)} {own : Nat → Bool} {sec sec' : String} {k : Nat}
    (hne : sec ≠ sec') (hf : free log own [sec] k = true) (hc : calledAt log sec' k) : False := by
  simp only [free, Engine.Host.free, calledAt, callOf_names, Bool.and_eq_true, List.any_cons, List.any_nil, Bool.or_false] at hf hc
  cases he : log.reverse[k]? with
  | none => simp [he] at hc
  | some e =>
    simp only [he, Option.any_some] at hf hc
    cases e <;> simp only [HostCall.callOf, beq_iff_eq, reduceCtorEq, false_and] at hf hc
    exact hne (Option.some.inj (hf.1.1.symm.trans hc))

theorem seededNextJob_mem {σ : Choices} {s : State Impl} {k : Nat} {s' : State Impl}
    (h : seededNextJobIn σ s = .ok (some k) s') : k ∈ nextJobs (jobReady s) s.hostLog := by
  simp only [seededNextJobIn, Engine.Host.seededNextJobIn, Engine.Host.seededPickIn, Res.ok.injEq] at h
  exact (List.mem_filter.mp (List.mem_of_getElem? h.1)).1

/-- The seeded next job is a free one of some HostEnqueue…Job. -/
theorem seeded_free {σ : Choices} {s : State Impl} {k : Nat} {s' : State Impl}
    (h : seededNextJobIn σ s = .ok (some k) s') :
    ∃ sec ∈ [promiseJob, genericJob, timeoutJob], free s.hostLog (jobReady s) [sec] k = true := by
  have hm := seededNextJob_mem h
  simp only [nextJobs, Engine.Host.nextJobs, List.mem_append, List.mem_filter, Option.mem_toList] at hm
  rcases hm with (hm | hm) | hm
  · exact ⟨_, by simp, (List.find?_range_eq_some.mp hm).1⟩
  · exact ⟨_, by simp, hm.2⟩
  · exact ⟨_, by simp, hm.2⟩

theorem seeded_jobScheduled (σ : Choices) (s : State Impl) (k : Nat) (s' : State Impl)
    (h : seededNextJobIn σ s = .ok (some k) s') :
    (∃ sec ∈ jobHooks, calledAt s.hostLog sec k) ∧ ¬taken s.hostLog k := by
  obtain ⟨sec, hs, hf⟩ := seeded_free h
  obtain ⟨⟨sec', hs', hc⟩, -, ht⟩ := free_spec hf
  simp only [List.mem_singleton] at hs'
  subst hs'
  refine ⟨⟨sec', ?_, hc⟩, ht⟩
  simp only [promiseJob, genericJob, timeoutJob, List.mem_cons, List.not_mem_nil, or_false] at hs
  simp only [jobHooks, List.mem_cons, List.not_mem_nil, or_false]
  rcases hs with rfl | rfl | rfl <;> simp

theorem seeded_jobOwned (σ : Choices) (s : State Impl) (k : Nat) (s' : State Impl)
    (h : seededNextJobIn σ s = .ok (some k) s') : jobReady s k = true := by
  obtain ⟨sec, -, hf⟩ := seeded_free h
  exact (free_spec hf).2.1

theorem seeded_promiseJobsOrder (σ : Choices) (s : State Impl) (k : Nat) (s' : State Impl)
    (h : seededNextJobIn σ s = .ok (some k) s') (hk : calledAt s.hostLog "sec-hostenqueuepromisejob" k)
    (i : Nat) (hik : i < k) (hi : calledAt s.hostLog "sec-hostenqueuepromisejob" i) (ho : jobReady s i = true) :
    taken s.hostLog i := by
  have hm := seededNextJob_mem h
  simp only [nextJobs, Engine.Host.nextJobs, List.mem_append, List.mem_filter, Option.mem_toList] at hm
  rcases hm with (hm | hm) | hm
  · have := (List.find?_range_eq_some.mp hm).2.2 i hik
    exact taken_of_not_free (List.mem_singleton_self promiseJob) hi ho (by simpa using this)
  · exact (free_not_called (by simp [genericJob]) hm.2 hk).elim
  · exact (free_not_called (by simp [timeoutJob]) hm.2 hk).elim

/-- The seeded next job leaves the state as it is. -/
theorem seeded_same {σ : Choices} {s : State Impl} {o : Option Nat} {s' : State Impl}
    (h : seededNextJobIn σ s = .ok o s') : s' = s := by
  simp only [seededNextJobIn, Engine.Host.seededNextJobIn, Res.ok.injEq] at h
  exact h.2.symm

/-- An ~unhandled~ answer at the state as it was meets HostResizeArrayBuffer's law. -/
theorem unhandled_law (a : Nat) (n : Val Impl) (s : State Impl) (r : Val Impl) (s' : State Impl)
    (h : Run.Res.boundary (normalEnum "unhandled" s) = .ok r s') :
    (∀ f, Gen.fields[f]? = some "ArrayBufferData" → slotOf s a f ≠ some .null → slotOf s' a f ≠ some .null) ∧
    (∀ e, normalValue r = some (.enum e) → Gen.enums[e]? = some "handled" →
      ∀ f m, Gen.fields[f]? = some "ArrayBufferByteLength" → n = .math m →
        ∃ m', slotOf s' a f = some (.math m') ∧ Impl.eq m' m = true) := by
  unfold normalEnum Engine.Host.normalEnum at h
  revert h
  cases he : names.enum? "unhandled" <;> intro h
  · cases h
  · simp only [Run.pure, Run.Res.boundary, Res.ok.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    refine ⟨fun _ _ hd => hd, fun e' hv hh => ?_⟩
    simp [normalValue, normal] at hv
    subst hv
    rw [idxOf?_getElem? he] at hh
    simp at hh

theorem resizeInPlace_law (a : Nat) (n : Val Impl) (s : State Impl) (r : Val Impl) (s' : State Impl)
    (h : Run.boundary (resizeInPlace [.obj a, n]) s = .ok r s') :
    (∀ f, Gen.fields[f]? = some "ArrayBufferData" → slotOf s a f ≠ some .null → slotOf s' a f ≠ some .null) ∧
    (∀ e, normalValue r = some (.enum e) → Gen.enums[e]? = some "handled" →
      ∀ f m, Gen.fields[f]? = some "ArrayBufferByteLength" → n = .math m →
        ∃ m', slotOf s' a f = some (.math m') ∧ Impl.eq m' m = true) := by
  change Run.Res.boundary (resizeInPlace [.obj a, n] s) = _ at h
  unfold resizeInPlace Engine.Host.resizeInPlace at h
  split at h
  · rename_i a' n' t he _
    simp only [List.cons.injEq, Val.obj.injEq, and_true] at he
    obtain ⟨rfl, rfl⟩ := he
    split at h
    · rename_i hok
      unfold Engine.Host.normalEnum at h
      revert h
      cases he : names.enum? "handled" <;> intro h
      · cases h
      · simp only [Run.pure, Run.Res.boundary, Res.ok.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        simp only [Engine.Host.resizeOk, Bool.and_eq_true, List.all_eq_true] at hok
        refine ⟨fun f hf hd => ?_, fun _ _ _ f m hf hn => ?_⟩
        · have := hok.1 f (mem_fieldsNamed hf)
          revert this hd
          split <;> simp_all
        · have := hok.2 f (mem_fieldsNamed hf)
          cases hn
          revert this
          split
          · rename_i m' hm; intro h; exact ⟨m', hm, h⟩
          · simp
    · exact unhandled_law a _ s r s' h
  · exact unhandled_law a n s r s' h

theorem resizeInPlace_normal (vs : List (Val Impl)) (s : State Impl) (r : Val Impl) (s' : State Impl)
    (h : Run.boundary (resizeInPlace vs) s = .ok r s') : compType r = Known.eNormal := by
  change Run.Res.boundary (resizeInPlace vs s) = _ at h
  unfold resizeInPlace Engine.Host.resizeInPlace at h
  split at h
  · split at h
    · exact normalEnum_normal _ _ r s' h
    · exact normalEnum_normal _ _ r s' h
  · exact normalEnum_normal _ _ r s' h

/-- The test host answers ParseDateString by `dateParse`, as the Impl host does. -/
theorem parsesDatesIn (σ : Choices) (o : HostOpts) (c : Cells) : ParsesDates (hostIn σ o c) := fun x s r s' l hp hu =>
  parsesDates c x s r s' l (by rwa [choiceIn_eq σ o c (by decide)] at hp) hu

/-- A web browser's WebBrowser answers true for every argument list. -/
theorem browserBy_web {N : Engine.Host.Names} {o : HostOpts} (h : o.webBrowser = true) (vs : List (Val Impl)) :
    Engine.Host.browserBy N o vs = true := by
  unfold Engine.Host.browserBy
  split <;> simp [h]

/-- The test host's choices keep the agent, each Record cell and every object. -/
theorem choiceIn_stepKeeps (σ : Choices) (o : HostOpts) (c : Cells) (q : PrimId) (vs : List (Val Impl))
    (s : State Impl) (r : Val Impl) (s' : State Impl) (h : Run.boundary ((hostIn σ o c).choice q vs) s = .ok r s') :
    StepKeeps s s' := by
  by_cases hq : q = Known.pHostGlobalProperties
  · subst hq
    rw [choiceIn_globalProps] at h
    exact globalProps_stepKeeps h
  by_cases h1 : q = Known.pAgentPrepareJob
  · subst h1; exact ((agentPrepare_jobKeepsR c (nextJobIn σ o) (choiceIn σ o) vs).boundary h).stepKeeps
  by_cases h2 : q = Known.pAgentCleanupJob
  · subst h2; exact ((agentCleanup_jobKeepsR c (nextJobIn σ o) (choiceIn σ o) vs).boundary h).stepKeeps
  exact (KeepsR.boundary (choiceIn_keeps σ o c q vs hq h1 h2) h).stepKeeps

/-! HostSelectAgent and ChooseReadsBytesFrom by `σ`. -/

/-- HostSelectAgent by `σ` gives ~empty~ or an agent (`isAgent`) of the cluster by its signifier, other than
the surrounding one, that can run; the state as it was. -/
theorem selectIn_law {M : Model} {isAgent : State M → Val M → Bool} {xs : State M → List (Val M)} {σ : Choices}
    {vs : List (Val M)} {s : State M} {r : Val M} {s' : State M} (h : selectIn isAgent xs σ vs s = .ok r s') :
    s' = s ∧ (r = .enum Known.eEmpty ∨ isAgent s r = true ∧
      (clusterSigs s).any (Val.same (sigOf s r)) = true ∧ Val.same (sigOf s r) (sigOf s s.agent) = false ∧
      Val.same r s.agent = false ∧ canRunAgent s r = true) := by
  revert h
  fun_cases selectIn isAgent xs σ vs
  · intro h
    dsimp only at h
    split at h
    · rename_i x hx
      simp only [Res.ok.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      have hp := (List.mem_filter.mp (List.mem_of_getElem? hx)).2
      simp only [switchable, Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at hp
      exact ⟨rfl, .inr ⟨hp.1.1.1.1, hp.1.1.1.2, hp.1.1.2, hp.1.2, canRunAgent_of_runnable hp.2⟩⟩
    · simp only [Res.ok.injEq] at h
      exact ⟨h.2.symm, .inl h.1.symm⟩
  · intro h; cases h

/-- ChooseReadsBytesFrom by `σ` gives a new List of _elementSize_ events of the execution, each a write
(`isWrite`) of its byte of the block: law L1, at every `σ`. -/
theorem readsIn_law {M : Model} {isWrite : State M → Val M → Bool} {σ : Choices} {vs : List (Val M)} {s : State M}
    {r : Val M} {s' : State M} (h : readsIn isWrite σ vs s = .ok r s') :
    ∃ ex er block idx size ws, vs = [ex, er, block, .math idx, .math size] ∧ listOf ws s = .ok r s' ∧
      M.eq (M.ofNat ws.length) size = true ∧
      ∀ j w, ws[j]? = some w → w ∈ execEvents s ex ∧ writesByte isWrite s block (M.add idx (M.ofNat j)) w = true := by
  simp only [readsIn] at h
  split at h
  · rename_i ex block idx size hargs
    obtain ⟨er, rfl⟩ := readArgs_some hargs
    split at h
    · rename_i heq
      split at h
      · rename_i ws hws
        obtain ⟨hl, hk⟩ := eachByteIx_spec hws
        refine ⟨ex, er, block, idx, size, ws, rfl, h, by rw [hl]; exact heq, fun j w hw => ?_⟩
        have hf := hk j w hw
        simp only [Nat.zero_add, Option.map_eq_some_iff] at hf
        obtain ⟨q, hq, rfl⟩ := hf
        obtain ⟨hm, hb⟩ := mem_writesOn (List.mem_of_getElem? hq)
        exact ⟨mem_placedEvents hm, hb⟩
      · cases h
    · cases h
  · cases h

/-- Law L2 for a ChooseReadsBytesFrom answer `ch`: a valid execution whose memory order agrees with the
interleaving order stays one with the read appended, reading the chosen events. -/
def ReadsValidFor {M : Model} (ch : List (Val M) → Run M (Val M)) : Prop :=
  ∀ vs s r s', ch vs s = .ok r s' →
    ∀ ex er b idx size, vs = [ex, er, .ref b, .math idx, .math size] →
    ∃ ws : List M.Addr, listOf (ws.map .ref) s = .ok r s' ∧
      ∀ (d : CloSite → List (Val M) → List (Val M) → Run M (Val M)) rbf hsw mo k (ev : MemoryModel.NewEvent M),
        let x := MemoryModel.View.exec memNames d s ex
        MemoryModel.ValidWith x rbf hsw → MemoryModel.MemoryOrder x rbf hsw mo → interleaved s ex mo →
        MemoryModel.View.Formed memNames d s ex → x.records[k]? = some (MemoryModel.View.eventsRecord memNames s er) →
        ev.IsRead → ev.block = b → ev.byteIndex = idx → ev.elementSize = size → (∃ m, size = M.ofNat m) →
        MemoryModel.ReadsValid x rbf hsw k ev ws

/-- The inputs whose reads are valid: ChooseReadsBytesFrom by `σ` meets law L2. -/
def ReadsValid (σ : Choices) : Prop := ReadsValidFor (readsIn (Engine.Host.isWriteIn names) σ)

/-- Inputs that pick each byte's latest write have valid reads (`scWrites_valid`). -/
theorem readsValid_zero {σ : Choices} (h : ∀ n i, σ Known.pChooseReadsBytesFrom n i = 0) : ReadsValid σ := by
  intro vs s r s' hr
  rw [Engine.Host.readsIn_zero _ h] at hr
  have e : Engine.Host.isWriteIn names = fun (s : State Impl) e => isWriteEvent s e :=
    funext fun s => funext fun e => by simp only [Engine.Host.isWriteIn, isWriteEvent, isRecordOf_names]
  rw [e] at hr
  exact MemoryModel.scWrites_valid fastIntFacts addrEq_iff hr

/-- The options' own inputs have valid reads. -/
theorem readsValid_σOf (o : HostOpts) : ReadsValid (σOf o) := readsValid_zero (Engine.Host.σOf_reads o)

/-- The test host's HostSelectAgent is `selectIn` at `σ`. -/
theorem choiceIn_select (σ : Choices) (o : HostOpts) (c : Cells) :
    (hostIn σ o c).choice Known.pHostSelectAgent = selectIn (fun s => names.isRecordOf s "Agent Record") clusterSigs σ := by
  rw [hostIn_choice_of σ o c (by decide) (by decide) (by decide)]
  simp only [choiceIn, Engine.Host.choiceIn, beq_false_of_ne (show Known.pHostSelectAgent ≠ Known.pWebBrowser by decide),
    beq_false_of_ne (show Known.pHostSelectAgent ≠ Known.pHostGlobalProperties by decide), beq_self_eq_true,
    Bool.false_eq_true, ↓reduceIte]

/-- The test host's ChooseReadsBytesFrom is `readsIn` at `σ`. -/
theorem choiceIn_reads (σ : Choices) (o : HostOpts) (c : Cells) :
    (hostIn σ o c).choice Known.pChooseReadsBytesFrom = readsIn (Engine.Host.isWriteIn names) σ := by
  rw [hostIn_choice_of σ o c (by decide) (by decide) (by decide)]
  simp only [choiceIn, Engine.Host.choiceIn,
    beq_false_of_ne (show Known.pChooseReadsBytesFrom ≠ Known.pWebBrowser by decide),
    beq_false_of_ne (show Known.pChooseReadsBytesFrom ≠ Known.pHostGlobalProperties by decide),
    beq_false_of_ne (show Known.pChooseReadsBytesFrom ≠ Known.pHostSelectAgent by decide), beq_self_eq_true,
    Bool.false_eq_true, ↓reduceIte]

/-- HostSelectAgent's law at every option set and every `σ`. -/
theorem selectAgentIn (σ : Choices) (o : HostOpts) (c : Cells) : ∀ vs s r s',
    (hostIn σ o c).choice Known.pHostSelectAgent vs s = .ok r s' →
    s' = s ∧ (r = .enum Known.eEmpty ∨ isRecordOf s "Agent Record" r = true ∧
      (clusterSigs s).any (Val.same (sigOf s r)) = true ∧ Val.same (sigOf s r) (sigOf s s.agent) = false ∧
      Val.same r s.agent = false ∧ canRunAgent s r = true) := by
  intro vs s r s' h
  rw [choiceIn_select] at h
  have e : (fun s => names.isRecordOf s "Agent Record") = fun (s : State Impl) => isRecordOf s "Agent Record" :=
    funext fun s => funext (isRecordOf_names s "Agent Record")
  rw [e] at h
  exact selectIn_law h

/-- ChooseReadsBytesFrom's law L1 at every option set and every `σ`. -/
theorem chooseReadsIn (σ : Choices) (o : HostOpts) (c : Cells) : ∀ vs s r s',
    (hostIn σ o c).choice Known.pChooseReadsBytesFrom vs s = .ok r s' →
    ∃ ex er block idx size ws, vs = [ex, er, block, .math idx, .math size] ∧ listOf ws s = .ok r s' ∧
      Impl.eq (Impl.ofNat ws.length) size = true ∧
      ∀ j w, ws[j]? = some w → w ∈ execEvents s ex ∧
        writesByte isWriteEvent s block (Impl.add idx (Impl.ofNat j)) w = true := by
  intro vs s r s' h
  rw [choiceIn_reads] at h
  have e : Engine.Host.isWriteIn names = fun (s : State Impl) e => isWriteEvent s e :=
    funext fun s => funext fun e => by simp only [Engine.Host.isWriteIn, isWriteEvent, isRecordOf_names]
  rw [e] at h
  exact readsIn_law h

/-- Every step of `hostIn` keeps the agent, each Record cell and every object. -/
theorem stepKeepsIn (σ : Choices) (o : HostOpts) (c : Cells) : ∀ s s', (hostIn σ o c).Step s s' → StepKeeps s s' :=
  Host.stepKeeps_of (hookIn_stepKeeps σ o c) (choiceIn_stepKeeps σ o c) (nextJobIn_stepKeeps σ o c)
    (fun s _ _ h => by cases h; exact (Keeps.refl s).stepKeeps)
    (fun _ _ _ h => (prepareJob_jobKeeps h).stepKeeps) (fun k _ _ h => (cleanupJob_jobKeeps (k := k) h).stepKeeps)
    (fun _ _ _ h => ((first_lk o c).ok_of h).stepKeeps) (fun _ _ _ h => ((idle_lk o c).ok_of h).stepKeeps)
    (fun v _ _ _ h => ((idleEnd_lk o c v).ok_of h).stepKeeps)

/-- The host with any options and inputs whose reads are valid satisfies the host laws; `hv` gives L2 only. -/

theorem wfByIn (σ : Choices) (o : HostOpts) (c : Cells) (hv : ReadsValid σ) : Host.WF (hostIn σ o c) where
  nextJob s k s' h := by
    rcases o with ⟨_ | N, b, cb, w, ab⟩
    · exact ⟨(jobScheduled_law c s k s' h).1, (jobScheduled_law c s k s' h).2, jobOwned_law c s k s' h,
        fun hk i hik hi ho => promiseJobsOrder_law c s k s' h hk i hik hi ho⟩
    · exact ⟨(seeded_jobScheduled σ s k s' (hostIn_checked h).1).1, (seeded_jobScheduled σ s k s' (hostIn_checked h).1).2,
        seeded_jobOwned σ s k s' (hostIn_checked h).1,
        fun hk i hik hi ho => seeded_promiseJobsOrder σ s k s' (hostIn_checked h).1 hk i hik hi ho⟩
  nanEncoding v w p hv hp := by
    obtain ⟨k, hk, h⟩ := (wf c).nanEncoding v w p hv hp
    exact ⟨k, hk, fun s => by rw [choiceIn_eq σ o c (by decide)]; exact h s⟩
  approxInteger x s r s' h := (wf c).approxInteger x s r s' (by rwa [choiceIn_eq σ o c (by decide)] at h)
  approxPower vs s r s' h := (wf c).approxPower vs s r s' (by rwa [choiceIn_eq σ o c (by decide)] at h)
  bigIntTooLarge vs s r s' h := (wf c).bigIntTooLarge vs s r s' (by rwa [choiceIn_eq σ o c (by decide)] at h)
  stringTooLarge vs s r s' h := (wf c).stringTooLarge vs s r s' (by rwa [choiceIn_eq σ o c (by decide)] at h)
  ownsAgent := (wf c).ownsAgent
  ownsSingle := (wf c).ownsSingle
  agentNextJob vs s r s' h := by
    rcases o with ⟨_ | N, b, cb, w, ab⟩
    · exact agentNextJob_of c (next := nextJobIn σ ⟨none, b, cb, w, ab⟩) (ch := choiceIn σ ⟨none, b, cb, w, ab⟩)
        jobReady (fun _ _ _ h => nextJob_same h) (fun _ _ _ h => nextJob_jobs h) vs s r s' h
    · exact agentNextJob_of c (next := nextJobIn σ ⟨some N, b, cb, w, ab⟩)
        (ch := choiceIn σ ⟨some N, b, cb, w, ab⟩) jobReady (fun _ _ _ h => seeded_same h)
        (fun s k s' h => ⟨(seeded_jobScheduled σ s k s' h).1, (seeded_jobScheduled σ s k s' h).2,
          seeded_jobOwned σ s k s' h, fun hk i hik hi ho => seeded_promiseJobsOrder σ s k s' h hk i hik hi ho⟩)
        vs s r s' h
  agentPrepareJob vs s r s' h :=
    agentPrepareJob_law c (next := nextJobIn σ o) (ch := choiceIn σ o) vs s r s' h
  agentCleanupJob vs s r s' h :=
    agentCleanupJob_law c (next := nextJobIn σ o) (ch := choiceIn σ o) vs s r s' h
  promiseJobPrepared := (wf c).promiseJobPrepared
  jobCleanup := (wf c).jobCleanup
  listSeparator k xs s r s' hk h :=
    (wf c).listSeparator k xs s r s' hk ((answers_eq σ o c hk (by decide) (by decide)).mp h)
  additionalTimeout vs s r s' h := (wf c).additionalTimeout vs s r s' (by rwa [choiceIn_eq σ o c (by decide)] at h)
  timeZoneNameSuffix vs s r s' h := (wf c).timeZoneNameSuffix vs s r s' (by rwa [choiceIn_eq σ o c (by decide)] at h)
  systemTimeZoneString vs s r s' h := by
    have := (wf c).systemTimeZoneString vs s r s' (by rwa [choiceIn_eq σ o c (by decide)] at h)
    simpa only [choiceIn_eq σ o c (p := Known.pAvailableNamedTimeZoneIds) (by decide),
      choiceIn_eq σ o c (p := Known.pIsNonPrimaryTimeZoneId) (by decide)] using this
  primaryTimeZoneId vs s r s' h := by
    have := (wf c).primaryTimeZoneId vs s r s' (by rwa [choiceIn_eq σ o c (by decide)] at h)
    simpa only [choiceIn_eq σ o c (p := Known.pAvailableNamedTimeZoneIds) (by decide),
      choiceIn_eq σ o c (p := Known.pIsNonPrimaryTimeZoneId) (by decide)] using this
  timeNow vs s r s' h := by
    rcases o with ⟨_ | N, b, cb, w, ab⟩
    · exact (wf c).timeNow vs s r s' (by rwa [choiceTimeNow] at h)
    · rw [seededTimeNow] at h
      obtain ⟨h1, h2⟩ := readClock_ok h
      refine ⟨h1, _, h2, ?_⟩
      unfold Engine.Host.seededNumIn
      dsimp only
      split
      · exact instantB_spec ‹_›
      · exact clockNum_instant _ (.inl rfl)
  spinWaitHint vs s r s' h := (wf c).spinWaitHint vs s r s' (by rwa [choiceIn_eq σ o c (by decide)] at h)
  discardContextResources vs s r s' h :=
    (wf c).discardContextResources vs s r s' (by rwa [choiceIn_eq σ o c (by decide)] at h)
  selectAgent := selectAgentIn σ o c
  chooseReadsBytesFrom := chooseReadsIn σ o c
  chooseReadsValid vs s r s' h := hv vs s r s' (by rwa [choiceIn_reads] at h)
  elapsedMono := elapsedMono_of_check rfl
  timeoutAfter := timeoutAfter_of_check rfl
  contextResources _ h := absurd h Bool.false_ne_true
  parseDateString vs s r s' h := (wf c).parseDateString vs s r s' (by rwa [choiceIn_eq σ o c (by decide)] at h)
  dateFormUTC x s r s' f h hfits hlegal _ hu := (parsesDatesIn σ o c).dateFormUTC h hfits hlegal hu
  dateFormLocal x s r s' f id h hfits hlegal hloc hu hz :=
    (wf c).dateFormLocal x s r s' f id (by rwa [choiceIn_eq σ o c (by decide)] at h) hfits hlegal hloc hu (by
      simpa only [sysTimeZone, choiceIn_eq σ o c (p := Known.pSupportsOnlyUTC) (by decide),
        choiceIn_eq σ o c (p := Known.pSystemTimeZoneString) (by decide)] using hz)
  dateFormIllegal x s r s' f h hfits hill hu := (parsesDatesIn σ o c).dateFormIllegal h hfits hill hu
  canAllocate vs s r s' h := by
    rcases o with ⟨_ | N, b, cb, w, ab⟩
    · exact (wf c).canAllocate vs s r s' (by rwa [choiceCanAllocate] at h)
    · rw [hostIn_choice_of (p := Known.pCanAllocate) _ _ c (by decide) (by decide) (by decide),
        choiceIn_seed σ rfl (by decide) (by decide) (by decide) (by decide)] at h
      simp only [Engine.Host.seededChoiceIn, beq_false_of_ne (show Known.pCanAllocate ≠ Known.pHostChoice by decide),
        beq_false_of_ne (show Known.pCanAllocate ≠ Known.pTimeNow by decide), Bool.false_eq_true, ↓reduceIte,
        beq_self_eq_true] at h
      split at h
      · simp only [Res.ok.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨rfl, _, rfl⟩
      · cases h
  debuggerEnabled vs s r s' h := (wf c).debuggerEnabled vs s r s' (by rwa [choiceIn_eq σ o c (by decide)] at h)
  debuggerAction vs s r s' h := (wf c).debuggerAction vs s r s' (by rwa [choiceIn_eq σ o c (by decide)] at h)
  nativeFunctionSource f s r s' h :=
    (wf c).nativeFunctionSource f s r s' (by rwa [choiceIn_eq σ o c (by decide)] at h)
  supportsOnlyUTC s r s' h := (wf c).supportsOnlyUTC s r s' (by rwa [choiceIn_eq σ o c (by decide)] at h)
  hookCompletion k xs s r s' h := by
    unfold Host.answers at h
    rcases o with ⟨_ | N, b, cb, w, ab⟩ <;> simp only [hostIn, Engine.Host.hostIn, Engine.Host.hookIn, names_clause] at h <;>
      by_cases hb : (b && secOf k == some resizeClause) = true <;> simp only [hb, Bool.false_eq_true, ↓reduceIte] at h
    · exact .inl (resizeInPlace_normal xs s r s' h)
    · exact (wf c).hookCompletion k xs s r s' h
    · exact .inl (resizeInPlace_normal xs s r s' h)
    · by_cases hr : (secOf k == some randomClause) = true <;> simp only [hr, ↓reduceIte] at h
      · simp only [Run.boundary, Engine.Host.seededRandomIn, Run.Res.boundary, Res.ok.injEq] at h
        rw [← h.1]
        exact .inl rfl
      · exact (wf c).hookCompletion k xs s r s' h
  privateElementSameKind := ⟨fun _ => Known.eNormal, fun k xs s r s' hk h => by
    rw [answers_eq σ o c hk (by decide) (by decide)] at h
    rw [private_law hk h]; rfl⟩
  supportedImportAttributes := by
    obtain ⟨ids, hids⟩ := (wf c).supportedImportAttributes
    exact ⟨ids, fun k xs s r s' hk h => hids k xs s r s' hk ((answers_eq σ o c hk (by decide) (by decide)).mp h)⟩
  getCodeForEval k xs s r s' hk h :=
    (wf c).getCodeForEval k xs s r s' hk ((answers_eq σ o c hk (by decide) (by decide)).mp h)
  hasSourceTextAvailable := ⟨fun _ => .bool true, fun k xs s r s' hk h => by
    rw [answers_eq σ o c hk (by decide) (by decide)] at h
    exact source_law hk h⟩
  resizeArrayBuffer k a n s r s' hk h := by
    have hs : secOf k = some resizeClause := (secOf_eq k).trans hk
    have hr : (some resizeClause == some randomClause) = false := by decide
    unfold Host.answers at h
    rcases o with ⟨_ | N, _ | _, cb, w, ab⟩ <;> simp only [hostIn, Engine.Host.hostIn, Engine.Host.hookIn, names_clause, hs, hr, beq_self_eq_true, Bool.and_true,
      Bool.false_eq_true, ↓reduceIte] at h
    all_goals first | exact resizeInPlace_law a n s r s' h | exact (wf c).resizeArrayBuffer k a n s r s' hk h
  mathRandom k xs s r s' hc h := by
    have hs : secOf k = some randomClause := (secOf_eq k).trans hc
    rcases o with ⟨_ | N, b, cb, w, ab⟩ <;> simp only [Host.answers, hostIn, Engine.Host.hostIn, Engine.Host.hookIn, names_clause, hs, show (some randomClause == some resizeClause) = false by decide,
      Bool.and_false, Bool.false_eq_true, ↓reduceIte, beq_self_eq_true] at h
    · exact (wf c).mathRandom k xs s r s' hc h
    · simp only [Engine.Host.seededRandomIn, Run.boundary, Run.Res.boundary, Res.ok.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      refine ⟨rfl, _, rfl, ?_⟩
      split
      · exact unitB_spec ‹_›
      · exact .inl rfl
  hostGlobalObject vs s r s' h :=
    (wf c).hostGlobalObject vs s r s' (by rwa [choiceIn_eq σ o c (by decide)] at h)
  hostThisValue vs s r s' h :=
    (wf c).hostThisValue vs s r s' (by rwa [choiceIn_eq σ o c (by decide)] at h)
  hostGlobalProperties realm g s r s' h :=
    ⟨(globalProps_law (Engine.Host.ddaBy names o) realm g s r s' (by rwa [choiceIn_globalProps] at h)).1,
      (globalProps_law (Engine.Host.ddaBy names o) realm g s r s' (by rwa [choiceIn_globalProps] at h)).2.1⟩
  hostReportCleanupError vs s r s' h :=
    (wf c).hostReportCleanupError vs s r s' (by rwa [choiceIn_eq σ o c (by decide)] at h)
  hostReportErrors vs s r s' h :=
    (wf c).hostReportErrors vs s r s' (by rwa [choiceIn_eq σ o c (by decide)] at h)
  mayCleanup reg s r s' h := (wf c).mayCleanup reg s r s' (by rwa [choiceIn_eq σ o c (by decide)] at h)
  escapePattern pattern flags s r s' h := by
    have := (wf c).escapePattern pattern flags s r s' (by rwa [choiceIn_eq σ o c (by decide)] at h)
    simpa only [choiceIn_eq σ o c (p := Known.pEscapePattern) (by decide)] using this
  sortStep n st res h s r s' hr hc := (wf c).sortStep n st res h s r s'
    (hr.congr (choiceIn_eq σ o c (p := Known.pSortStep) (by decide)))
    (by rwa [choiceIn_eq σ o c (by decide)] at hc)
  sortStepEnds n := by
    rw [sortNext_congr (choiceIn_eq σ o c (p := Known.pSortStep) (by decide)) n]
    exact (wf c).sortStepEnds n
  forInStep obj h s r s' hc := (wf c).forInStep obj h s r s' (by rwa [choiceIn_eq σ o c (by decide)] at hc)
  propertyOrder o' l s r s' h := (wf c).propertyOrder o' l s r s' (by rwa [choiceIn_eq σ o c (by decide)] at h)
  omitSharedArrayBuffer := by
    obtain ⟨b, h⟩ := (wf c).omitSharedArrayBuffer
    exact ⟨b, fun vs s r s' hc => h vs s r s' (by rwa [choiceIn_eq σ o c (by decide)] at hc)⟩
  localeCase q l s r s' hq h := by
    rcases hq with rfl | rfl
    · exact (wf c).localeCase _ l s r s' (.inl rfl) (by rwa [choiceIn_eq σ o c (by decide)] at h)
    · exact (wf c).localeCase _ l s r s' (.inr rfl) (by rwa [choiceIn_eq σ o c (by decide)] at h)
  localeCompare := by
    obtain ⟨le, h1, h2, h3⟩ := (wf c).localeCompare
    exact ⟨le, h1, h2, fun a b s r s' h => h3 a b s r s' (by rwa [choiceIn_eq σ o c (by decide)] at h)⟩
  localeNumberString vs s r s' h := (wf c).localeNumberString vs s r s' (by rwa [choiceIn_eq σ o c (by decide)] at h)
  localeDateString k v s r s' h := (wf c).localeDateString k v s r s' (by rwa [choiceIn_eq σ o c (by decide)] at h)
  expandedYearForm vs s r s' h := (wf c).expandedYearForm vs s r s' (by rwa [choiceIn_eq σ o c (by decide)] at h)
  hostExtendIntrinsics vs s r s' h :=
    (wf c).hostExtendIntrinsics vs s r s' (by rwa [choiceIn_eq σ o c (by decide)] at h)
  hostExtendObject o' s r s' h :=
    (wf c).hostExtendObject o' s r s' (by rwa [choiceIn_eq σ o c (by decide)] at h)
  webBrowser := webBrowser_of (browserBy names o) fun _ => rfl
  webBrowserSupports := webBrowserSupports_of (browserBy names o) (fun _ => rfl) fun h _ => browserBy_web (N := names) (o := o) h _
  callJobCallback := (jobCallback_laws (fun vs => by rw [choiceIn_eq σ o c (by decide)]; rfl)
    (fun vs => by rw [choiceIn_eq σ o c (by decide)]; rfl) (fun vs => by rw [choiceIn_eq σ o c (by decide)]; rfl)).1
  jobCallbackDefault := (jobCallback_laws (fun vs => by rw [choiceIn_eq σ o c (by decide)]; rfl)
    (fun vs => by rw [choiceIn_eq σ o c (by decide)]; rfl) (fun vs => by rw [choiceIn_eq σ o c (by decide)]; rfl)).2
  collect := (wf c).collect
  agentFixed s s' h := (stepKeepsIn σ o c s s' h).1.agentKept
  approx vs s r s' h := (wf c).approx vs s r s' (by rwa [choiceIn_eq σ o c (by decide)] at h)
  hostChoice vs s r s' h := by
    rcases o with ⟨_ | N, b, cb, w, ab⟩
    · exact (wf c).hostChoice vs s r s' h
    · rw [hostIn_choice_of (p := Known.pHostChoice) _ _ c (by decide) (by decide) (by decide),
        choiceIn_seed σ rfl (by decide) (by decide) (by decide) (by decide)] at h
      simp only [Engine.Host.seededChoiceIn, beq_self_eq_true, ↓reduceIte] at h
      split at h
      · split at h
        · simp only [Res.ok.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          exact ⟨rfl, by split <;> simp⟩
        · cases h
      · simp only [Res.ok.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨rfl, by split <;> simp⟩
      · cases h
  hostInitializeBuiltinContext ctx s r s' h :=
    (wf c).hostInitializeBuiltinContext ctx s r s' (by rwa [choiceIn_eq σ o c (by decide)] at h)
  invariantsKept s s' h := (stepKeepsIn σ o c s s' h).2

/-- The host with any options satisfies the host laws: `wfByIn` at their own inputs `σOf o`. -/
theorem wfBy (o : HostOpts) (c : Cells) : Host.WF (hostBy o c) := by
  rw [show hostBy o c = hostIn (σOf o) o c from Engine.Host.hostBy_eq_hostIn names o c]
  exact wfByIn (σOf o) o c (readsValid_σOf o)

/-- info: 'Engine.SpecHost.wfByIn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms wfByIn

/-- info: 'Engine.SpecHost.selectAgentIn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms selectAgentIn

/-- info: 'Engine.SpecHost.chooseReadsIn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms chooseReadsIn

/-- info: 'Engine.SpecHost.wfBy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms wfBy

/-- info: 'Engine.SpecHost.stepKeepsIn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms stepKeepsIn

end Engine.SpecHost
