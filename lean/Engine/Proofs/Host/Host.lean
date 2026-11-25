module

public import Engine.Host.Spec
public import Engine.Host.Opts
public import Engine.Proofs.Num
public import Engine.Proofs.Host.Dates
public import Engine.Proofs.Host.Native
public import Engine.Proofs.Host.ModelLemmas
public import Engine.Proofs.Host.ParseLemmas
public import Engine.Proofs.Host.CoreLemmas

@[expose] public section

/-!
# The Impl host's laws, over Ecma.Gen

The lemmas of each host law for the Impl host at Ecma.Gen's names (`Engine.SpecHost`); `Proofs/Host/WF.lean`
assembles them (`wf`).
-/

namespace Engine.Host

open Ecma Engine

variable (N : Names)

/-- The fixed host: `hostBy` with no option, its hook, choices, next job and clock the plain ones (`hook`, `choice`,
`nextJob`, `elapsed`); the rest (`first`, `idle`, `idleEnd` among it) are `hostBy`'s, which no option changes. The
definitions removed as dead code that only the proofs use. -/
def host (c : Cells) : Ecma.Host Impl :=
  { hostBy N {} c with
    hook := hook N c, choice := agentJobs N c (nextJob N) (choice N),
    nextJob := checkElapsed (elapsed N) (nextJob N), elapsed := elapsed N }

end Engine.Host

namespace Engine.SpecHost

open Ecma Engine

/-! The Impl host at Ecma.Gen's names (the abbreviations only the proofs use). -/

abbrev normalEnum := Engine.Host.normalEnum names
abbrev hooks := Engine.Host.hooks names
abbrev free := Engine.Host.free names
abbrev nextJob := Engine.Host.nextJob names
abbrev pushCtx := Engine.Host.pushCtx names
abbrev prepareJob := Engine.Host.prepareJob names
abbrev host := Engine.Host.host names

/-- Ecma.Gen's names' sec-ids are `secOf`'s. -/
@[simp] theorem names_clause (c : ClauseId) : names.clause c = secOf c := rfl

/-- Ecma.Gen's names find the logged calls `HostCall.callOf` does. -/
theorem callOf_names {M : Model} (sec : String) (e : HostCall M) : names.callOf sec e = e.callOf sec := by
  cases e <;> simp [Engine.Host.Names.callOf, HostCall.callOf, names, secOf_eq]

/-- Ecma.Gen's names' subsorts are the data's. -/
theorem subSort_names (f : Nat) (k t : SortId) : names.subSort f k t = dataSubSort f k t := by
  induction f generalizing k with
  | zero => rfl
  | succ f ih =>
    simp only [Engine.Host.Names.subSort, dataSubSort, ih]
    simp only [names]

/-- Ecma.Gen's names' Records of a sort are `isRecordOf`'s. -/
theorem isRecordOf_names {M : Model} (s : State M) (sort : String) (v : Val M) :
    names.isRecordOf s sort v = isRecordOf s sort v := by
  cases v <;> simp only [Engine.Host.Names.isRecordOf, isRecordOf, subSort_names]
  simp only [names]
  split <;> split <;> simp_all

/-! The host laws (`Host.WF`). -/

theorem nanEncoding_law (c : Cells) (v : Impl.Num) (w p : Nat) (hp : 2 ≤ p) : ∃ k, nanBits w p k ∧
    ∀ s, (host c).choice Known.pNaNEncoding [.num v, .math (Impl.ofNat w), .math (Impl.ofNat p)] s =
      .ok (.math (Impl.ofNat k)) s :=
  ⟨nanCode w p, nanCode_bits w p hp, fun _ => rfl⟩

theorem approxInteger_law (c : Cells) (x : Impl.Math) (s : State Impl) (r : Val Impl) (s' : State Impl)
    (h : (host c).choice Known.pApproxInteger [.math x] s = .ok r s') :
    s' = s ∧ ∃ m, r = .math m ∧ Impl.isInt m = true := by
  change (if Impl.isInt x then Run.pure (.math x) else Run.stop .residue : Run Impl (Val Impl)) s = _ at h
  split at h
  · rename_i hx; cases h; exact ⟨rfl, x, rfl, hx⟩
  · cases h

theorem choice_parseDate (c : Cells) (vs : List (Val Impl)) :
    (host c).choice Known.pParseDateString vs = Engine.Host.parseDate vs := rfl

/-- A String of Impl whose code units are `l` has them. -/
theorem unitsAre_fast {x : Impl.Str} {l : List Nat} (h : unitsAre (M := Impl) x l) : x.toList.map UInt16.toNat = l := by
  unfold unitsAre at h
  have e : seqList (M := Impl) (Impl.strUnits x) = x.toList.map fun u => Engine.Model.MathVal.int u.toNat := by
    show Array.foldl _ [] (x.map _) = _
    rw [← Array.foldl_toList, Array.toList_map]
    exact (foldl_snoc [] _).trans (List.nil_append _)
  rw [e] at h
  generalize x.toList = xs at h ⊢
  induction xs generalizing l with
  | nil => cases l <;> simp_all [unitsMatch]
  | cons u xs ih =>
    cases l with
    | nil => simp [unitsMatch] at h
    | cons c l =>
      simp only [List.map_cons, unitsMatch] at h
      have hu : ((u.toNat : Int) == (c : Int)) = true := h.1
      simp only [List.map_cons, ih h.2, List.cons.injEq, and_true]
      exact_mod_cast eq_of_beq hu

theorem numView_nan : Impl.numView Impl.numNaN = .nan := rfl

/-- ParseDateString's answer is `parseDateNum`'s Number of a String's code units, and leaves the state as it is. -/
theorem parseDate_ok {vs : List (Val Impl)} {s s' : State Impl} {r : Val Impl} (h : Engine.Host.parseDate vs s = .ok r s') :
    s' = s ∧ ∃ x n, vs = [.str x] ∧ parseDateNum (M := Impl) (x.toList.map UInt16.toNat) = some n ∧ r = .num n := by
  unfold Engine.Host.parseDate at h
  split at h
  · rename_i x
    cases hn : parseDateNum (M := Impl) (x.toList.map UInt16.toNat) with
    | none => rw [hn] at h; cases h
    | some n => rw [hn] at h; cases h; exact ⟨rfl, x, n, rfl, hn, rfl⟩
  · cases h

/-- The Impl host answers ParseDateString by `dateParse`, residue aside. -/
theorem parsesDates (c : Cells) : ParsesDates (host c) := by
  intro x s r s' l hp hu
  rw [choice_parseDate] at hp
  obtain ⟨-, x', n, hx, hn, rfl⟩ := parseDate_ok hp
  cases hx
  rw [← unitsAre_fast hu]
  exact (parseDateNum_spec numView_nan hn).1

theorem parseDateString_law (c : Cells) (vs : List (Val Impl)) (s : State Impl) (r : Val Impl)
    (s' : State Impl) (h : (host c).choice Known.pParseDateString vs s = .ok r s') :
    s' = s ∧ ∃ n, r = .num n ∧ (Impl.numView n = .nan ∨ instantTimeValue n) ∧ Impl.numView n ≠ .negZero := by
  rw [choice_parseDate] at h
  obtain ⟨rfl, x, n, -, hn, rfl⟩ := parseDate_ok h
  exact ⟨rfl, n, rfl, (parseDateNum_spec numView_nan hn).2⟩

/-- *"UTC"* has no UTC offset. -/
theorem utc_noOffset (x : Impl.Str) (l : List Nat) (he : Impl.strEq x (Impl.strLit "UTC") = true)
    (hl : unitsAre x l) : utcOffsetNs l = none := by
  have hx : x = Engine.Model.utf16 "UTC" := eq_of_beq (α := Array UInt16) he
  have hu : (Engine.Model.utf16 "UTC").toList.map UInt16.toNat = [85, 84, 67] := by simp [Engine.Model.utf16]
  rw [← unitsAre_fast hl, hx, hu]
  rfl

theorem choice_onlyUTC (c : Cells) (s : State Impl) :
    (host c).choice Known.pSupportsOnlyUTC [] s = .ok (.bool true) s := rfl

theorem canAllocate_law (c : Cells) (vs : List (Val Impl)) (s : State Impl) (r : Val Impl)
    (s' : State Impl) (h : (host c).choice Known.pCanAllocate vs s = .ok r s') :
    s' = s ∧ ∃ b, r = .bool b := by
  have e : ∀ vs : List (Val Impl), (host c).choice Known.pCanAllocate vs = match vs with
      | [.math n, .bool _] => Run.pure (.bool !(Impl.lt (Impl.ofNat 4294967296) n))
      | _ => Run.stop .sortError := fun _ => rfl
  rw [e] at h
  split at h
  · simp only [Run.pure] at h; cases h; exact ⟨rfl, _, rfl⟩
  · cases h

/-- The next job is `pickJob`'s of those ready. -/
theorem nextJob_pick {s : State Impl} {k : Nat} {s' : State Impl} (h : nextJob s = .ok (some k) s') :
    Engine.Host.pickJob names s.hostLog (jobReady s) = some k := by
  simp only [nextJob, Engine.Host.nextJob, Engine.Host.pickJobFast_eq] at h
  split at h
  · cases h; assumption
  · cases h

/-- The next job is a free one. -/
theorem nextJob_free (s : State Impl) (k : Nat) (s' : State Impl) (h : nextJob s = .ok (some k) s') :
    free s.hostLog (jobReady s) [genericJob, promiseJob] k = true ∨
      free s.hostLog (jobReady s) [timeoutJob] k = true := by
  have h := nextJob_pick h
  simp only [Engine.Host.pickJob] at h
  cases h1 : (List.range s.hostLog.length).find? (free s.hostLog (jobReady s) [genericJob, promiseJob]) with
  | some j =>
    rw [h1] at h
    cases h
    exact .inl (List.find?_range_eq_some.mp h1).1
  | none =>
    rw [h1] at h
    exact .inr (List.find?_range_eq_some.mp h).1

/-- A free position is a call of one of `secs` that `own` allows and whose job has not been taken. -/
theorem free_spec {log : List (HostCall Impl)} {own : Nat → Bool} {secs : List String} {k : Nat}
    (h : free log own secs k = true) : (∃ sec ∈ secs, calledAt log sec k) ∧ own k = true ∧ ¬taken log k := by
  simp only [free, Engine.Host.free, Bool.and_eq_true, Bool.not_eq_true'] at h
  obtain ⟨⟨h1, ho⟩, h2⟩ := h
  refine ⟨?_, ho, by simp [taken, h2]⟩
  cases he : log.reverse[k]? with
  | none => simp [he] at h1
  | some e =>
    simp only [he, Option.any_some, List.any_eq_true] at h1
    obtain ⟨sec, hs, hc⟩ := h1
    exact ⟨sec, hs, by simpa [calledAt, he, callOf_names] using hc⟩

/-- A call of one of `secs` that `own` allows and whose job is not free has been taken. -/
theorem taken_of_not_free {log : List (HostCall Impl)} {own : Nat → Bool} {secs : List String} {sec : String}
    {k : Nat} (hs : sec ∈ secs) (hc : calledAt log sec k) (ho : own k = true) (h : free log own secs k = false) :
    taken log k := by
  simp only [calledAt] at hc
  cases he : log.reverse[k]? with
  | none => simp [he] at hc
  | some e =>
    simp only [he, Option.any_some] at hc
    have : secs.any (e.callOf ·) = true := List.any_eq_true.mpr ⟨sec, hs, hc⟩
    simp only [free, Engine.Host.free, he, Option.any_some, callOf_names, this, ho, Bool.true_and,
      Bool.not_eq_false'] at h
    exact h

/-- The next job is one a HostEnqueue…Job call scheduled, not taken. -/
theorem nextJob_scheduled {s : State Impl} {k : Nat} {s' : State Impl} (h : nextJob s = .ok (some k) s') :
    (∃ sec ∈ jobHooks, calledAt s.hostLog sec k) ∧ ¬taken s.hostLog k := by
  rcases nextJob_free s k s' h with h | h <;>
  · obtain ⟨⟨sec, hs, hc⟩, -, ht⟩ := free_spec h
    refine ⟨⟨sec, ?_, hc⟩, ht⟩
    simp only [genericJob, promiseJob, timeoutJob, List.mem_cons, List.not_mem_nil, or_false] at hs
    simp only [jobHooks, List.mem_cons, List.not_mem_nil, or_false]
    first | (rcases hs with hs | hs <;> simp [hs]) | simp [hs]

/-- The next job is a ready one. -/
theorem nextJob_owned {s : State Impl} {k : Nat} {s' : State Impl} (h : nextJob s = .ok (some k) s') :
    jobReady s k = true := by
  rcases nextJob_free s k s' h with h | h <;> exact (free_spec h).2.1

/-- A next promise job comes after every earlier-scheduled ready promise job. -/
theorem nextJob_promiseOrder {s : State Impl} {k : Nat} {s' : State Impl} (h : nextJob s = .ok (some k) s')
    (hk : calledAt s.hostLog "sec-hostenqueuepromisejob" k) (i : Nat) (hik : i < k)
    (hi : calledAt s.hostLog "sec-hostenqueuepromisejob" i) (ho : jobReady s i = true) : taken s.hostLog i := by
  have hp : promiseJob ∈ [genericJob, promiseJob] := by simp
  have hok := nextJob_owned h
  have h := nextJob_pick h
  simp only [Engine.Host.pickJob] at h
  cases h1 : (List.range s.hostLog.length).find? (free s.hostLog (jobReady s) [genericJob, promiseJob]) with
  | some j =>
    rw [h1] at h
    cases h
    have := (List.find?_range_eq_some.mp h1).2.2 i hik
    exact taken_of_not_free hp hi ho (by simpa using this)
  | none =>
    rw [h1] at h
    have h2 := List.find?_range_eq_some.mp h
    have hfree : free s.hostLog (jobReady s) [genericJob, promiseJob] k = true := by
      cases hf : free s.hostLog (jobReady s) [genericJob, promiseJob] k
      · exact absurd (taken_of_not_free hp hk hok hf) (free_spec h2.1).2.2
      · rfl
    exact absurd hfree (List.find?_eq_none.mp h1 k h2.2.1)

/-- `nextJob` leaves the state as it is. -/
theorem nextJob_same {s : State Impl} {o : Option Nat} {s' : State Impl} (h : nextJob s = .ok o s') : s' = s := by
  simp only [nextJob, Engine.Host.nextJob] at h
  split at h <;> cases h <;> rfl

theorem jobScheduled_law (c : Cells) (s : State Impl) (k : Nat) (s' : State Impl)
    (h : (host c).nextJob s = .ok (some k) s') :
    (∃ sec ∈ jobHooks, calledAt s.hostLog sec k) ∧ ¬taken s.hostLog k :=
  nextJob_scheduled (checkElapsed_ok h).1

theorem promiseJobsOrder_law (c : Cells) (s : State Impl) (k : Nat) (s' : State Impl)
    (h : (host c).nextJob s = .ok (some k) s') (hk : calledAt s.hostLog "sec-hostenqueuepromisejob" k)
    (i : Nat) (hik : i < k) (hi : calledAt s.hostLog "sec-hostenqueuepromisejob" i)
    (ho : (host c).owns s i = true) : taken s.hostLog i :=
  nextJob_promiseOrder (checkElapsed_ok h).1 hk i hik hi ho

theorem jobOwned_law (c : Cells) (s : State Impl) (k : Nat) (s' : State Impl)
    (h : (host c).nextJob s = .ok (some k) s') : (host c).owns s k = true :=
  nextJob_owned (checkElapsed_ok h).1

theorem ownsAgent_law (c : Cells) (s : State Impl) (k : Nat) (h : (host c).owns s k = true) :
    (clusterSigs s).length ≤ 1 ∨ (jobAgents s)[k]?.any (Val.same (sigOf s s.agent)) = true := by
  by_cases hl : (clusterSigs s).length ≤ 1
  · exact .inl hl
  · right
    have h' : jobReady s k = true := h
    simp only [jobReady, if_neg hl, readyFor, Bool.and_eq_true] at h'
    exact h'.1

theorem ownsSingle_law (c : Cells) (s : State Impl) (k : Nat) (h : (clusterSigs s).length ≤ 1) :
    (host c).owns s k = true := by
  show jobReady s k = true
  simp only [jobReady, if_pos h]

/-- AgentNextJob is `next`'s position, else ~empty~: a law of `next`'s jobs (`own`) is one of its answers. -/
theorem agentNextJob_of (c : Cells) {next : Run Impl (Option Nat)}
    {ch : PrimId → List (Val Impl) → Run Impl (Val Impl)} (own : State Impl → Nat → Bool)
    (hs : ∀ s o s', next s = .ok o s' → s' = s)
    (hj : ∀ s k s', next s = .ok (some k) s' → (∃ sec ∈ jobHooks, calledAt s.hostLog sec k) ∧
      ¬taken s.hostLog k ∧ own s k = true ∧ (calledAt s.hostLog "sec-hostenqueuepromisejob" k →
        ∀ i < k, calledAt s.hostLog "sec-hostenqueuepromisejob" i → own s i = true → taken s.hostLog i))
    (vs : List (Val Impl)) (s : State Impl) (r : Val Impl) (s' : State Impl)
    (h : Engine.Host.agentJobs names c next ch Known.pAgentNextJob vs s = .ok r s') : s' = s ∧
    (r = .enum Known.eEmpty ∨ ∃ k, r = .math (Impl.ofNat k) ∧ (∃ sec ∈ jobHooks, calledAt s.hostLog sec k) ∧
      ¬taken s.hostLog k ∧ own s k = true ∧ (calledAt s.hostLog "sec-hostenqueuepromisejob" k →
        ∀ i < k, calledAt s.hostLog "sec-hostenqueuepromisejob" i → own s i = true →
          taken s.hostLog i)) := by
  unfold Engine.Host.agentJobs at h
  simp only [beq_self_eq_true, ↓reduceIte] at h
  split at h
  · simp only [bind, Run.bind] at h
    cases hn : next s with
    | ok o t =>
      rw [hn] at h
      obtain rfl := hs _ _ _ hn
      cases o with
      | none =>
        simp only [Run.Res.bind, pure, Run.pure, Res.ok.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨rfl, .inl rfl⟩
      | some k =>
        simp only [Run.Res.bind, pure, Run.pure, Res.ok.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨rfl, .inr ⟨k, rfl, hj _ _ _ hn⟩⟩
    | _ => rw [hn] at h; simp [Run.Res.bind] at h
  · simp [Run.stop] at h

/-- The host's next job is a law of its jobs. -/
theorem nextJob_jobs {s : State Impl} {k : Nat} {s' : State Impl} (h : nextJob s = .ok (some k) s') :
    (∃ sec ∈ jobHooks, calledAt s.hostLog sec k) ∧ ¬taken s.hostLog k ∧ jobReady s k = true ∧
      (calledAt s.hostLog "sec-hostenqueuepromisejob" k → ∀ i < k, calledAt s.hostLog "sec-hostenqueuepromisejob" i →
        jobReady s i = true → taken s.hostLog i) :=
  ⟨(nextJob_scheduled h).1, (nextJob_scheduled h).2, nextJob_owned h, fun hk i hik hi ho => nextJob_promiseOrder h hk i hik hi ho⟩

theorem agentNextJob_law (c : Cells) (vs : List (Val Impl)) (s : State Impl) (r : Val Impl) (s' : State Impl)
    (h : (host c).choice Known.pAgentNextJob vs s = .ok r s') : s' = s ∧
    (r = .enum Known.eEmpty ∨ ∃ k, r = .math (Impl.ofNat k) ∧ (∃ sec ∈ jobHooks, calledAt s.hostLog sec k) ∧
      ¬taken s.hostLog k ∧ (host c).owns s k = true ∧ (calledAt s.hostLog "sec-hostenqueuepromisejob" k →
        ∀ i < k, calledAt s.hostLog "sec-hostenqueuepromisejob" i → (host c).owns s i = true →
          taken s.hostLog i)) :=
  agentNextJob_of c (next := nextJob) (ch := Engine.Host.choice names) jobReady (fun _ _ _ h => nextJob_same h)
    (fun _ _ _ h => nextJob_jobs h) vs s r s' h

theorem jobCleanup_law (k : Nat) (s s' : State Impl) (h : cleanupJob k s = .ok () s') :
    Impl.eq (Impl.seqLen s'.stack) (Impl.ofNat 0) = true := by
  unfold cleanupJob at h
  split at h
  · cases h
    show Engine.Model.MathVal.eq (.int _) (.int _) = true
    simp [Engine.Model.MathVal.eq, *]
  · split at h
    · cases h; rfl
    · cases h

/-- A Record's field read after a write. -/
theorem recGet_put (m : Engine.Model.WMap FieldId (Val Impl)) (f g : FieldId) (v : Val Impl) :
    (m.put f v).get g = if g = f then some v else m.get g := m.property.get_put f v g

/-- A value's cell, where it has one, is kept by an allocation. -/
theorem heapGet_alloc {h : Impl.Heap (Cell Impl)} {x : Cell Impl} {b : Impl.Addr} {y : Cell Impl}
    (hb : Impl.heapGet h b = some y) : Impl.heapGet (Impl.heapAlloc h x).2 b = some y := by
  simp only [Impl, Impl] at hb ⊢
  rw [Array.getElem?_push, if_neg, hb]
  rintro rfl
  simp at hb

theorem heapGet_alloc_new (h : Impl.Heap (Cell Impl)) (x : Cell Impl) :
    Impl.heapGet (Impl.heapAlloc h x).2 (Impl.heapAlloc h x).1 = some x := by
  simp [Impl, Impl]

theorem fieldOf_kept {s s' : State Impl} (hh : ∀ b y, Impl.heapGet s.heap b = some y → Impl.heapGet s'.heap b = some y)
    {f : FieldId} {v w : Val Impl} (hv : fieldOf s f v = some w) : fieldOf s' f v = some w := by
  match v, hv with
  | .ref b, hv =>
    simp only [fieldOf] at hv ⊢
    split at hv
    · rename_i fs hg; rw [show s'.heap[b]? = _ from hh _ _ hg]; exact hv
    · cases hv

theorem isRecordOf_kept {s s' : State Impl} (hh : ∀ b y, Impl.heapGet s.heap b = some y → Impl.heapGet s'.heap b = some y)
    {sort : String} {v : Val Impl} (hv : isRecordOf s sort v = true) : isRecordOf s' sort v = true := by
  match v, hv with
  | .ref b, hv =>
    simp only [isRecordOf] at hv ⊢
    split at hv
    · rename_i k fs t hg ht; rw [show s'.heap[b]? = _ from hh _ _ hg, ht]; exact hv
    · cases hv

/-- GetActiveScriptOrModule's step over one execution context, in the heap `h`. -/
def smStep (h : Impl.Heap (Cell Impl)) (r ctx : Val Impl) : Val Impl :=
  match ctx with
  | .ref a => match Impl.heapGet h a with
    | some (.record _ fs) => match Impl.recGet fs Known.fScriptOrModule with
      | some .null | none => r
      | some v => v
    | _ => r
  | _ => r

theorem active_eq (s : State Impl) : activeScriptOrModule s = s.stack.foldl (smStep s.heap) .null := by
  unfold activeScriptOrModule
  show Array.foldl _ _ _ = _
  congr 1
  funext r ctx
  unfold smStep
  cases ctx with
  | ref a =>
    dsimp only
    generalize s.heap[a]? = o
    cases o with
    | none => rfl
    | some x =>
      cases x with
      | record k fs =>
        dsimp only
        generalize fs.get Known.fScriptOrModule = o'
        cases o' with
        | none => rfl
        | some v => cases v <;> rfl
      | _ => rfl
  | _ => rfl

/-- A pushed execution context `a` whose ScriptOrModule is `sm`, over a stack with no active script or
module, in a heap that keeps the old cells and adds only `a`: `sm` is active. -/
theorem active_push {s s' : State Impl} {a : Impl.Addr} {ec : SortId} {fs : Impl.Rec (Val Impl)} {sm : Val Impl}
    (hst : s'.stack = Impl.seqPush s.stack (.ref a)) (ha : Impl.heapGet s'.heap a = some (.record ec fs))
    (hS : Impl.recGet fs Known.fScriptOrModule = some sm)
    (hkeep : ∀ b y, Impl.heapGet s.heap b = some y → Impl.heapGet s'.heap b = some y)
    (hnew : ∀ b y, Impl.heapGet s'.heap b = some y → Impl.heapGet s.heap b = some y ∨ b = a)
    (hn : activeScriptOrModule s = .null) : activeScriptOrModule s' = sm := by
  rw [active_eq] at hn ⊢
  rw [hst]
  show (s.stack.push _).foldl _ _ = _
  rw [Array.foldl_push]
  cases sm with
  | null =>
    have e : smStep s'.heap = smStep s.heap := funext fun r => funext fun ctx => by
      cases ctx with
      | ref b =>
        simp only [smStep]
        cases hb : s.heap[b]? with
        | some y => rw [show s'.heap[b]? = _ from hkeep b y hb]
        | none =>
          cases hb' : s'.heap[b]? with
          | none => rfl
          | some y =>
            rcases hnew b y hb' with h1 | rfl
            · have h1' : s.heap[b]? = some y := h1
              rw [hb] at h1'; cases h1'
            · rw [show s'.heap[b]? = _ from ha] at hb'; cases hb'; simp only [show fs.get Known.fScriptOrModule = _ from hS]
      | _ => rfl
    have ht : ∀ x, smStep s'.heap x (.ref a) = x := fun x => by
      simp only [smStep, show s'.heap[a]? = _ from ha, show fs.get Known.fScriptOrModule = _ from hS]
    rw [ht, e, hn]
  | _ => simp only [smStep, show s'.heap[a]? = _ from ha, show fs.get Known.fScriptOrModule = _ from hS]

/-- An allocation adds only the new address. -/
theorem heapGet_alloc_only {h : Impl.Heap (Cell Impl)} {x : Cell Impl} {b : Impl.Addr} {y : Cell Impl}
    (hb : Impl.heapGet (Impl.heapAlloc h x).2 b = some y) :
    Impl.heapGet h b = some y ∨ b = (Impl.heapAlloc h x).1 := by
  simp only [Impl, Impl] at hb ⊢
  rw [Array.getElem?_push] at hb
  split at hb
  · exact .inr ‹_›
  · exact .inl hb

/-- A state whose stack is an execution context `a` pushed over a state `s` whose cells it keeps:
prepared to evaluate ECMAScript code, with `sm` the active script or module, where `a`'s Realm `r` is a
Realm Record and `sm`'s [[Realm]] where `sm` is a Record. -/
theorem prepared_of {s s' : State Impl} {a : Impl.Addr} {ec : SortId} {fs : Impl.Rec (Val Impl)}
    {sm r : Val Impl} (hst : s'.stack = Impl.seqPush s.stack (.ref a))
    (ha : Impl.heapGet s'.heap a = some (.record ec fs)) (hR : Impl.recGet fs Known.fRealm = some r)
    (hS : Impl.recGet fs Known.fScriptOrModule = some sm)
    (hkeep : ∀ b y, Impl.heapGet s.heap b = some y → Impl.heapGet s'.heap b = some y)
    (hRealm : isRecordOf s "Realm Record" r = true) (hsmR : ∀ b, sm = .ref b → fieldOf s Known.fRealm sm = some r)
    (hact : activeScriptOrModule s' = sm) :
    preparedToEvaluate s' ∧ activeIs s' sm := by
  have hl : stackList s' = stackList s ++ [.ref a] := by
    rw [stackList, stackList, hst]
    exact Array.foldl_push
  have hf : ∀ f, fieldOf s' f (.ref a) = Impl.recGet fs f := by
    intro f; simp [fieldOf, show s'.heap[a]? = _ from ha]
  refine ⟨⟨?_, stackList s, _, r, hl, by rw [hf, hR], isRecordOf_kept hkeep hRealm⟩, hact, ?_⟩
  · rw [hst]
    show Engine.Model.MathVal.eq (.int _) (.int _) = false
    simp [Engine.Model.MathVal.eq, Impl, Impl] <;> omega
  · intro hsm
    refine ⟨stackList s, _, [], hl, by rw [hf, hS], by simp, r, by rw [hf, hR], ?_⟩
    cases sm <;> first
      | exact fieldOf_kept hkeep (hsmR _ rfl)
      | simp [isRecordOf] at hsm

/-- On a stack with no active script or module, a pushed execution context leaves an execution
prepared to evaluate ECMAScript code, with `sm` the active script or module. -/
theorem pushCtx_prepared (realm sm : Val Impl) (s s' : State Impl) (hn : activeScriptOrModule s = .null)
    (h : pushCtx realm sm s = .ok () s') : preparedToEvaluate s' ∧ activeIs s' sm := by
  unfold pushCtx Engine.Host.pushCtx at h
  split at h
  · rename_i r hr
    split at h
    · rename_i hR
      simp only [Res.ok.injEq] at h
      obtain ⟨-, rfl⟩ := h
      have hS : Impl.recGet (Impl.recSet (Impl.recSet (Impl.recSet Impl.recEmpty Known.fScriptOrModule sm)
          Known.fRealm r) Known.fFunction .null) Known.fScriptOrModule = some sm := by
        simp [recGet_put, Known.fScriptOrModule, Known.fRealm, Known.fFunction]
      refine prepared_of (s := s) rfl (heapGet_alloc_new _ _) ?_ hS (fun _ _ => heapGet_alloc)
        (by rwa [isRecordOf_names] at hR) ?_
        (active_push rfl (heapGet_alloc_new _ _) hS (fun _ _ => heapGet_alloc) (fun _ _ => heapGet_alloc_only) hn)
      · simp [recGet_put, Known.fScriptOrModule, Known.fRealm, Known.fFunction]
      · rintro b rfl; exact hr
    · cases h
  · cases h

/-- A promise job whose realm is not *null*, prepared on `base` contexts with no active script or
module, is prepared to evaluate ECMAScript code with its scheduling's script or module active. -/
theorem promiseJobPreparedOn (c : Cells) (base : Nat) (s : State Impl) (k : Nat) (s' : State Impl) (c' : ClauseId)
    (job realm : Val Impl) (xs : List (Val Impl)) (sm rl r : Val Impl)
    (h : Engine.Host.prepareJobOn names c base k s = .ok () s')
    (he : s.hostLog.reverse[k]? = some (.hook c' (job :: realm :: xs) sm rl r))
    (hc : Gen.clauses[c']? = some "sec-hostenqueuepromisejob") (hr : realm ≠ .null)
    (hn : s.stack.size = base → activeScriptOrModule s = .null) :
    preparedToEvaluate s' ∧ activeIs s' sm := by
  have hp : names.callOf promiseJob (.hook c' (job :: realm :: xs) sm rl r : HostCall Impl) = true := by
    simp [callOf_names, HostCall.callOf, hc, promiseJob]
  unfold Engine.Host.prepareJobOn at h
  rw [he] at h
  simp only [hp, ↓reduceIte] at h
  split at h
  · rename_i h0
    split at h
    · exact absurd rfl hr
    · exact pushCtx_prepared _ _ s s' (hn h0) h
  · cases h

theorem promiseJobPrepared_law (c : Cells) (s : State Impl) (k : Nat) (s' : State Impl) (c' : ClauseId)
    (job realm : Val Impl) (xs : List (Val Impl)) (sm rl r : Val Impl) (h : prepareJob c k s = .ok () s')
    (he : s.hostLog.reverse[k]? = some (.hook c' (job :: realm :: xs) sm rl r))
    (hc : Gen.clauses[c']? = some "sec-hostenqueuepromisejob") (hr : realm ≠ .null) :
    preparedToEvaluate s' ∧ activeIs s' sm :=
  promiseJobPreparedOn c 0 s k s' c' job realm xs sm rl r h he hc hr fun h0 => by
    rw [active_eq, Array.eq_empty_of_size_eq_zero h0]; rfl

/-- A Math value `idx` reads as `n` is `n`. -/
theorem ofNat_of_idx {x : Impl.Math} {n : Nat} (h : Engine.Model.MathVal.idx x = some n) : x = Impl.ofNat n := by
  cases x with
  | int i =>
    simp only [Engine.Model.MathVal.idx] at h
    split at h
    · cases h
      show Engine.Model.MathVal.int i = .int (i.toNat : Int)
      rw [Int.toNat_of_nonneg ‹_›]
    · cases h
  | _ => cases h

/-- A host-defined operation's answer, by its sec-id. -/
theorem hook_of {c : Cells} {k : ClauseId} {sec : String} (hk : secOf k = some sec) (vs : List (Val Impl)) :
    (host c).hook k vs = (hooks.lookup sec).getD (fun _ _ => Run.stop .residue) c vs := by
  simp only [host, Engine.Host.host]
  rw [Engine.Host.hook, names_clause, hk, Option.elim_some]

/-- Impl's addresses are equal exactly where `addrEq` says so. -/
theorem addrEq_iff (a b : Nat) : Impl.addrEq a b = true ↔ a = b := beq_iff_eq

theorem unitB_spec {n : Impl.Num} (h : Engine.Host.unitB n = true) : unitNum n := by
  unfold Engine.Host.unitB at h
  unfold unitNum
  split at h
  · exact .inl ‹_›
  · rename_i m hm
    simp only [Bool.and_eq_true] at h
    exact .inr ⟨m, hm, h.1, h.2⟩
  · cases h

/-- Math.random under a seed answers a Number with positive sign in [+0𝔽, 1𝔽), the state as it was. -/
theorem seededRandom_law {n : Nat} {s : State Impl} {r : Val Impl} {s' : State Impl}
    (h : Run.boundary (Engine.Host.seededRandom n) s = .ok r s') : s' = s ∧ ∃ m, r = .num m ∧ unitNum m := by
  simp only [Engine.Host.seededRandom, Run.boundary, Run.Res.boundary, Res.ok.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  refine ⟨rfl, _, rfl, ?_⟩
  split
  · exact unitB_spec ‹_›
  · exact .inl rfl

/-- Math.random's answer: `seededRandom` at the default seed. -/
theorem random_law {c : Cells} {k : ClauseId} (hk : secOf k = some "sec-math.random") {xs : List (Val Impl)}
    {s : State Impl} {r : Val Impl} {s' : State Impl} (h : (host c).answers k xs s r s') :
    s' = s ∧ ∃ m, r = .num m ∧ unitNum m := by
  simp only [Host.answers, hook_of hk] at h
  have e : (hooks.lookup "sec-math.random").getD (fun _ _ => Run.stop .residue) c xs =
      Engine.Host.seededRandom Engine.Host.defaultSeed := by
    simp [hooks, Engine.Host.hooks, List.lookup]
  rw [e] at h
  exact seededRandom_law h

/-- `print`'s answer is ~unused~. -/
theorem printLine_unused (c : Cells) (vs : List (Val Impl)) (s : State Impl) (r : Val Impl) (s' : State Impl)
    (h : Run.boundary (printLine c vs) s = .ok r s') : r = unused := by
  unfold printLine at h
  split at h
  · simp only [Run.boundary, bind, Run.bind, readList, readCell] at h
    revert h
    generalize s.heap[c.out]? = o
    cases o with
    | none => intro h; cases h
    | some x =>
      intro h
      cases x with
      | list xs o =>
        simp [Run.Res.bind, pure, Run.pure, writeElems, writeList, Run.bind, Run.Res.boundary] at h
        exact h.1.symm
      | _ => simp [Run.Res.bind, Run.stop, Run.Res.boundary] at h
  · cases h

/-- Every answer of `m` past the algorithm boundary is a value, no Completion Record. -/
def AnsNormal (m : Run Impl (Val Impl)) : Prop :=
  ∀ s r s', Run.boundary m s = .ok r s' → compType r = Known.eNormal

theorem AnsNormal.ite {c : Prop} [Decidable c] {t e : Run Impl (Val Impl)} (ht : AnsNormal t) (he : AnsNormal e) :
    AnsNormal (if c then t else e) := by
  by_cases h : c
  · rw [if_pos h]; exact ht
  · rw [if_neg h]; exact he

theorem AnsNormal.stop (r : Stop) : AnsNormal (Run.stop r) := fun _ _ _ h => by cases h

/-- The agent API's answers are values, no Completion Record. -/
theorem agentHook_normal (k : ClauseId) (vs : List (Val Impl)) (s : State Impl) (r : Val Impl) (s' : State Impl)
    (h : Run.boundary (Engine.Host.agentHook k vs) s = .ok r s') : compType r = Known.eNormal := by
  revert s r s' h
  show AnsNormal (Engine.Host.agentHook k vs)
  unfold Engine.Host.agentHook
  dsimp only
  refine AnsNormal.ite ?_ <| AnsNormal.ite ?_ <| AnsNormal.ite ?_ <| AnsNormal.ite ?_ <| AnsNormal.ite ?_ <|
    AnsNormal.ite ?_ <| AnsNormal.ite ?_ <| AnsNormal.ite ?_ <| AnsNormal.ite ?_ <| AnsNormal.ite ?_ <|
    AnsNormal.ite ?_ <| AnsNormal.stop _
  all_goals intro s r s' h
  all_goals rcases vs with _ | ⟨v, _ | ⟨w, _ | ⟨u, t⟩⟩⟩
  all_goals first
    | (cases h; done)
    | skip
  all_goals try (cases v <;> first | (cases h; done) | skip)
  all_goals simp only [Run.boundary] at h
  all_goals try dsimp only at h
  all_goals repeat' split at h
  all_goals first
    | (simp only [Run.pure, Run.stop, Run.Res.boundary, reduceCtorEq] at h; done)
    | (simp only [Run.pure, Run.Res.boundary, Res.ok.injEq] at h; obtain ⟨rfl, -⟩ := h)
    | skip
  all_goals first
    | rfl
    | (unfold Engine.Host.wakeAfter; split <;> (try split) <;> rfl)
    | (unfold Engine.Host.reportOf; split <;> rfl)
    | (unfold Engine.Host.jobClauseOf; split <;> rfl)
    | (simp only [listOf, alloc, Run.Res.boundary, bind, Run.bind, Run.Res.bind, pure, Run.pure] at h; cases h; rfl)
    | (cases jobDue s s.agent <;> rfl)
    | (cases hf : List.find? (fun x => Engine.Host.isRef x && !x.same (sigOf s s.agent) && Engine.Host.idleIn s x)
          (clusterSigs s) with
        | none => rfl
        | some x =>
          have hx := List.find?_some hf
          cases x <;> simp [Engine.Host.isRef] at hx
          rfl)

/-- The answer of one of the host's own clauses is a value, no Completion Record. -/
theorem ownHook_normal (c : Cells) (k : ClauseId) (vs : List (Val Impl)) (s : State Impl) (r : Val Impl)
    (s' : State Impl) (h : Run.boundary (ownHook c k vs) s = .ok r s') : compType r = Known.eNormal := by
  unfold ownHook at h
  split at h
  · rw [printLine_unused c vs s r s' h]; rfl
  split at h
  · revert h
    fun_cases loadedModule vs
    · intro h
      simp only [Run.boundary, Run.Res.boundary, Res.ok.injEq] at h
      rw [← h.1]
      rename_i k t
      cases hl : loadedIn s.hostLog k t with
      | none => rfl
      | some m =>
        obtain ⟨e, -, he⟩ := List.exists_of_findSome?_eq_some hl
        split at he
        · split at he
          · cases he; rfl
          · cases he
        · cases he
    · intro h; cases h
  split at h
  · unfold moduleLoaded at h
    split at h
    · cases h; rfl
    · cases h
  split at h
  · unfold moduleSource at h
    split at h
    · simp only [Run.boundary, Run.pure, Run.Res.boundary, Res.ok.injEq] at h
      rw [← h.1]
      cases List.find? _ _ <;> rfl
    · cases h
  split at h
  · revert h
    fun_cases moduleKey c vs
    · intro h
      simp only [Run.boundary] at h
      split at h <;> (simp only [Run.Res.boundary, Res.ok.injEq] at h; rw [← h.1]; rfl)
    · intro h; cases h
  split at h
  · exact agentHook_normal k vs s r s' h
  · cases h

/-- A clause the data does not have is one of the host's own. -/
theorem hook_own {c : Cells} {k : ClauseId} (hk : secOf k = none) (vs : List (Val Impl)) :
    (host c).hook k vs = ownHook c k vs := by
  simp only [host, Engine.Host.host]
  rw [Engine.Host.hook, names_clause, hk, Option.elim_none]

/-- `normalEnum`'s answer is a normal completion. -/
theorem normalEnum_normal (n : String) (s : State Impl) (r : Val Impl) (s' : State Impl)
    (h : Run.boundary (normalEnum n) s = .ok r s') : compType r = Known.eNormal := by
  unfold normalEnum Engine.Host.normalEnum at h
  revert h
  cases names.enum? n <;> intro h
  · cases h
  · simp only [Run.boundary, Run.pure, Run.Res.boundary, Res.ok.injEq] at h
    rw [← h.1]
    rfl

/-- §4.2: every hook's answer is a normal completion or a value. -/
theorem hookCompletion_law (c : Cells) (k : ClauseId) (xs : List (Val Impl)) (s : State Impl) (r : Val Impl)
    (s' : State Impl) (h : (host c).answers k xs s r s') : compType r = Known.eNormal := by
  unfold Host.answers at h
  cases hk : secOf k with
  | none =>
    rw [hook_own hk] at h
    exact ownHook_normal c k xs s r s' h
  | some sec =>
    rw [hook_of hk] at h
    cases hl : hooks.lookup sec with
    | none => rw [hl, Option.getD_none] at h; cases h
    | some f =>
      rw [hl, Option.getD_some] at h
      have hm := lookup_some_mem hl
      simp only [hooks, Engine.Host.hooks, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hm
      rcases hm with ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ |
        ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ <;>
      first
        | exact normalEnum_normal _ s r s' h
        | (unfold Engine.Host.enumNamed at h
           split at h
           · simp only [Run.boundary, Run.pure, Run.Res.boundary, Res.ok.injEq] at h
             rw [← h.1]; rfl
           · cases h)
        | (simp only [Run.pure, listOf, alloc, normal, unused, Run.boundary, Run.Res.boundary, bind, Run.bind,
            Run.Res.bind, pure] at h
           rcases xs with _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | _⟩⟩⟩ <;> first | (cases h; rfl) | cases h)

/-- HostEnsureCanAddPrivateElement: NormalCompletion(~unused~). -/
theorem private_law {c : Cells} {k : ClauseId} (hk : Gen.clauses[k]? = some "sec-hostensurecanaddprivateelement")
    {xs : List (Val Impl)} {s : State Impl} {r : Val Impl} {s' : State Impl} (h : (host c).answers k xs s r s') :
    r = normal unused := by
  simp only [Host.answers, hook_of ((secOf_eq k).trans hk)] at h
  simp [hooks, Engine.Host.hooks, List.lookup, Run.boundary, Run.Res.boundary, Run.pure] at h
  exact h.1.symm

/-- HostHasSourceTextAvailable: *true*. -/
theorem source_law {c : Cells} {k : ClauseId} (hk : Gen.clauses[k]? = some "sec-hosthassourcetextavailable")
    {xs : List (Val Impl)} {s : State Impl} {r : Val Impl} {s' : State Impl} (h : (host c).answers k xs s r s') :
    r = .bool true := by
  simp only [Host.answers, hook_of ((secOf_eq k).trans hk)] at h
  simp [hooks, Engine.Host.hooks, List.lookup, Run.boundary, Run.Res.boundary, Run.pure] at h
  exact h.1.symm

/-- LocalizedListSeparator: the String ", ", the state as it was. -/
theorem listSeparator_law {c : Cells} {k : ClauseId} (hk : Gen.clauses[k]? = some "sec-localizedlistseparator")
    {xs : List (Val Impl)} {s : State Impl} {r : Val Impl} {s' : State Impl} (h : (host c).answers k xs s r s') :
    s' = s ∧ r = .str (Impl.strLit ", ") := by
  simp only [Host.answers, hook_of ((secOf_eq k).trans hk)] at h
  simp [hooks, Engine.Host.hooks, List.lookup, Run.boundary, Run.Res.boundary, Run.pure] at h
  exact ⟨h.2.symm, h.1.symm⟩

/-- HostGetCodeForEval: its default, ~no-code~. -/
theorem codeForEval_law {c : Cells} {k : ClauseId} (hk : Gen.clauses[k]? = some "sec-hostgetcodeforeval")
    {xs : List (Val Impl)} {s : State Impl} {r : Val Impl} {s' : State Impl} (h : (host c).answers k xs s r s') :
    ∃ e, r = .enum e ∧ Gen.enums[e]? = some "no-code" := by
  simp only [Host.answers, hook_of ((secOf_eq k).trans hk)] at h
  simp only [hooks, Engine.Host.hooks, List.lookup] at h
  simp only [String.reduceBEq, Bool.false_eq_true, ↓reduceIte, Option.getD_some] at h
  unfold Engine.Host.enumNamed at h
  revert h
  cases he : names.enum? "no-code" <;> intro h
  · cases h
  · simp only [Run.boundary, Run.pure, Run.Res.boundary, Res.ok.injEq] at h
    exact ⟨_, h.1.symm, idxOf?_getElem? he⟩

/-- EscapePattern's answer is `escapeChoice`'s. -/
theorem choice_escape (c : Cells) (vs : List (Val Impl)) :
    (host c).choice Known.pEscapePattern vs = Engine.Host.escapeChoice vs := rfl

/-- NativeFunctionSource's answer is `nativeChoice`'s. -/
theorem choice_native (c : Cells) (vs : List (Val Impl)) :
    (host c).choice Known.pNativeFunctionSource vs = Engine.Host.nativeChoice vs := rfl

/-- Pushing an ASCII name's code units one by one appends them. -/
theorem foldl_utf16_ascii (cs : List Char) (ha : ∀ c ∈ cs, c.toNat < 128) (acc : Array UInt16) :
    cs.foldl (fun a c =>
      let v := c.val.toNat
      if v < 0x10000 then a.push v.toUInt16
      else (a.push (0xD800 + (v - 0x10000) / 0x400).toUInt16).push (0xDC00 + (v - 0x10000) % 0x400).toUInt16) acc =
      acc ++ (cs.map fun c => c.toNat.toUInt16).toArray := by
  induction cs generalizing acc with
  | nil => simp
  | cons c cs ih =>
    have hc : c.val.toNat < 0x10000 := by have := ha c List.mem_cons_self; simp only [Char.toNat] at this; omega
    simp only [List.foldl_cons, hc, ↓reduceIte]
    rw [ih fun d hd => ha d (List.mem_cons_of_mem c hd)]
    apply Array.toList_inj.1
    simp

/-- The String of a name whose code points are `y`'s code units, ASCII and not NUL, is `y`. -/
theorem strLit_nameUnits {y : Impl.Str} {cs : List Char} (hm : cs.map Char.toNat = y.toList.map UInt16.toNat)
    (ha : ∀ c ∈ cs, 0 < c.toNat ∧ c.toNat < 128) : Impl.strLit (String.ofList cs) = y := by
  show Engine.Model.utf16 (String.ofList cs) = y
  unfold Engine.Model.utf16
  rw [String.foldl_eq_foldl_toList, String.toList_ofList, foldl_utf16_ascii cs fun c hc => (ha c hc).2]
  apply Array.toList_inj.1
  simp only [Array.toList_append, List.nil_append]
  have hy : y.toList = (y.toList.map UInt16.toNat).map Nat.toUInt16 := by
    rw [List.map_map]
    conv => lhs; rw [← List.map_id y.toList]
    exact List.map_congr_left fun u _ => by simp
  rw [hy, ← hm, List.map_map]
  simp

/-- §20.2.3.5 steps 3–4: NativeFunctionSource's answer is `nativeWrap` of a name the law admits, which is
_func_.[[InitialName]] where that is a String. -/
theorem nativeFunctionSource_law (c : Cells) (f : Val Impl) (s : State Impl) (r : Val Impl) (s' : State Impl)
    (h : (host c).choice Known.pNativeFunctionSource [f] s = .ok r s') :
    s' = s ∧ ∃ cs, nativeName cs = true ∧ r = .str (Impl.strLit (nativeWrap cs)) ∧
      ∀ a sl ps y, f = .obj a → Impl.heapGet s.heap a = some (.object sl ps) →
        Impl.recGet sl Known.fInitialName = some (.str y) → Impl.strEq y (Impl.strLit (String.ofList cs)) = true := by
  rw [choice_native] at h
  obtain ⟨hs, cs, hc, rfl⟩ := nativeAnswer_ok h
  refine ⟨hs, cs, ?_, rfl, fun a sl ps y hf hh hy => ?_⟩
  · cases hn : (initialNameIn s f).map (·.toList.map UInt16.toNat) with
    | none => rw [hn] at hc; cases hc; rfl
    | some us => rw [hn] at hc; exact (nativeNameOf_units hc).1
  subst hf
  rw [initialNameIn_of hh hy] at hc
  obtain ⟨-, hm, ha⟩ := nativeNameOf_units hc
  have hy : Impl.strLit (String.ofList cs) = y := strLit_nameUnits hm ha
  rw [hy]; exact beq_self_eq_true (α := Array UInt16) y

/-- The host's SortStep is `sortStepBy` over Impl's indices. -/
theorem host_sortStep (c : Cells) (vs : List (Val Impl)) :
    (host c).choice Known.pSortStep vs = sortStepBy Engine.Model.MathVal.idx vs := rfl

/-- Impl's indices read a natural as itself. -/
theorem idx_ofNat (n : Nat) : Engine.Model.MathVal.idx (Impl.ofNat n) = some n := by
  simp [Impl, Engine.Model.MathVal.idx]

/-- SortStep's call answer: a new List « _j_, _k_, _st_ » at the end of the heap. -/
theorem sortCall_fast (j k : Nat) (st : Val Impl) (s : State Impl) : sortCall (M := Impl) j k st s =
    .ok (.ref s.heap.size) { s with heap := s.heap.push (.list #[.math (Impl.ofNat j), .math (Impl.ofNat k), st] 0) } :=
  rfl

/-- SortStep's call answer names its pair and the state. -/
theorem sortCall_inj_fast {j k : Nat} {st : Val Impl} {j' k' : Nat} {st' : Val Impl} {s : State Impl} {r s'}
    (h : sortCall (M := Impl) j k st s = .ok r s') (h' : sortCall (M := Impl) j' k' st' s = .ok r s') :
    j = j' ∧ k = k' ∧ st = st' := by
  rw [sortCall_fast] at h h'
  have e := congrArg (Array.toList (α := Cell Impl)) (congrArg State.heap (Res.ok.inj (h.trans h'.symm)).2)
  simp only [Array.toList_push] at e
  have e := List.append_cancel_left e
  simp only [List.cons.injEq, Cell.list.injEq, and_true] at e
  have e1 := congrArg (fun a : Array (Val Impl) => a[0]?) e
  have e2 := congrArg (fun a : Array (Val Impl) => a[1]?) e
  have e3 := congrArg (fun a : Array (Val Impl) => a[2]?) e
  simp only [List.getElem?_toArray, List.getElem?_cons_zero, List.getElem?_cons_succ, Option.some.injEq,
    Val.math.injEq] at e1 e2 e3
  have hj : some j = some j' :=
    (idx_ofNat j).symm.trans ((congrArg Engine.Model.MathVal.idx e1).trans (idx_ofNat j'))
  have hk : some k = some k' :=
    (idx_ofNat k).symm.trans ((congrArg Engine.Model.MathVal.idx e2).trans (idx_ofNat k'))
  exact ⟨Option.some.inj hj, Option.some.inj hk, e3⟩

/-- SortStep's order answer is not a call answer. -/
theorem sortDone_ne_call_fast {σ : List Nat} {j k : Nat} {st : Val Impl} {s : State Impl} {r s'}
    (h : sortDone (M := Impl) σ s = .ok r s') (h' : sortCall (M := Impl) j k st s = .ok r s') : False := by
  rw [sortCall_fast] at h'
  have hd : ∃ c s'', sortDone (M := Impl) σ s = .ok (.ref (Array.push s.heap c).size) s'' := ⟨_, _, rfl⟩
  obtain ⟨_, s'', hd⟩ := hd
  rw [hd] at h
  have e := (Res.ok.inj (h.trans h'.symm)).1
  injection e with e
  simp at e

/-! HostGlobalProperties: `globalProps` allocates and then changes only the global object's own
properties. -/

/-- `s'` is `s` but for a heap that keeps each of `s`'s cells. -/
def Grows (s s' : State Impl) : Prop :=
  (∃ h, s' = { s with heap := h }) ∧ ∀ a c, Impl.heapGet s.heap a = some c → Impl.heapGet s'.heap a = some c

theorem Grows.refl (s : State Impl) : Grows s s := ⟨⟨s.heap, rfl⟩, fun _ _ h => h⟩

theorem Grows.trans {s₁ s₂ s₃ : State Impl} (h₁ : Grows s₁ s₂) (h₂ : Grows s₂ s₃) : Grows s₁ s₃ := by
  obtain ⟨⟨k₁, rfl⟩, g₁⟩ := h₁
  obtain ⟨⟨k₂, rfl⟩, g₂⟩ := h₂
  exact ⟨⟨k₂, rfl⟩, fun a c h => g₂ a c (g₁ a c h)⟩

/-- Every normal end of `m` grows the heap. -/
def GrowsR {α : Type} (m : Run Impl α) : Prop := ∀ s a s', m s = .ok a s' → Grows s s'

theorem GrowsR.pure {α : Type} (a : α) : GrowsR (Run.pure a : Run Impl α) := fun s _ _ h => by
  cases h; exact Grows.refl s

theorem GrowsR.pure' {α : Type} (a : α) : GrowsR (Pure.pure a : Run Impl α) := GrowsR.pure a

theorem GrowsR.stop {α : Type} (r : Stop) : GrowsR (Run.stop r : Run Impl α) := fun _ _ _ h => by cases h

theorem GrowsR.bind {α β : Type} {m : Run Impl α} {f : α → Run Impl β} (hm : GrowsR m)
    (hf : ∀ a, GrowsR (f a)) : GrowsR (m >>= f) := fun s b s' h => by
  change Run.Res.bind (m s) f = _ at h
  cases hr : m s with
  | ok a s₁ => rw [hr] at h; exact (hm s a s₁ hr).trans (hf a s₁ b s' h)
  | _ => rw [hr] at h; cases h

theorem GrowsR.readCell (a : Impl.Addr) : GrowsR (Ecma.readCell a : Run Impl (Cell Impl)) := fun s _ _ h => by
  unfold Ecma.readCell at h
  split at h <;> cases h
  exact Grows.refl s

theorem GrowsR.alloc (c : Cell Impl) : GrowsR (Ecma.alloc c : Run Impl Impl.Addr) := fun s _ _ h => by
  cases h; exact ⟨⟨_, rfl⟩, fun _ _ hb => heapGet_alloc hb⟩

theorem GrowsR.get : GrowsR (Run.get : Run Impl (State Impl)) := fun s _ _ h => by
  cases h; exact Grows.refl s

theorem GrowsR.optOr {α : Type} (r : Stop) (o : Option α) : GrowsR (Ecma.optOr r o : Run Impl α) := by
  unfold Ecma.optOr; split
  · exact GrowsR.pure _
  · exact GrowsR.stop _

/-- `do` blocks of reads, allocations, values and stops. -/
macro "grows" : tactic => `(tactic| repeat' (first
  | exact GrowsR.pure _ | exact GrowsR.pure' _ | exact GrowsR.stop _ | exact GrowsR.readCell _
  | exact GrowsR.alloc _ | exact GrowsR.optOr _ _
  | refine GrowsR.bind ?_ fun _ => ?_
  | split))

theorem readField_grows (v : Val Impl) (f : FieldId) : GrowsR (Ecma.readField v f) := by
  unfold Ecma.readField; grows

theorem objectOf_grows (v : Val Impl) : GrowsR (Engine.Host.objectOf v) := by
  unfold Engine.Host.objectOf; grows

theorem ownValue_grows (v : Val Impl) (k : String) : GrowsR (Engine.Host.ownValue v k) := by
  unfold Engine.Host.ownValue
  refine GrowsR.bind (objectOf_grows _) fun _ => ?_
  split
  · exact readField_grows _ _
  · exact GrowsR.stop _

theorem dataProp_grows (v : Val Impl) (w e c : Bool) : GrowsR (Engine.Host.dataProp v w e c) := by
  unfold Engine.Host.dataProp; grows

theorem builtinLike_grows (f : Val Impl) (b : AlgId) (n : String) (l : Nat) :
    GrowsR (Engine.Host.builtinLike f b n l) := by
  unfold Engine.Host.builtinLike
  refine GrowsR.bind (objectOf_grows _) fun _ => ?_
  refine GrowsR.bind (dataProp_grows _ _ _ _) fun _ => ?_
  refine GrowsR.bind (dataProp_grows _ _ _ _) fun _ => ?_
  grows

theorem htmlDDA_grows (d : FieldId) (f : Val Impl) : GrowsR (Engine.Host.htmlDDA d f) := by
  unfold Engine.Host.htmlDDA
  refine GrowsR.bind (objectOf_grows _) fun _ => ?_
  refine GrowsR.bind (dataProp_grows _ _ _ _) fun _ => ?_
  refine GrowsR.bind (dataProp_grows _ _ _ _) fun _ => ?_
  grows

theorem ddaProps_grows (dda : Option FieldId) (f : Val Impl) (ps : Impl.Props (Val Impl)) :
    GrowsR (Engine.Host.ddaProps dda f ps) := by
  unfold Engine.Host.ddaProps
  split
  · refine GrowsR.bind (htmlDDA_grows _ _) fun _ => ?_
    refine GrowsR.bind (dataProp_grows _ _ _ _) fun _ => ?_
    exact GrowsR.pure' _
  · exact GrowsR.pure _

theorem memberProps_grows (f : Val Impl) :
    ∀ (ps : Impl.Props (Val Impl)) (ms : List (AlgId × String × Nat)), GrowsR (Engine.Host.memberProps f ps ms)
  | _, [] => GrowsR.pure _
  | _, (_, _, _) :: ms =>
    GrowsR.bind (builtinLike_grows _ _ _ _) fun _ =>
    GrowsR.bind (dataProp_grows _ _ _ _) fun _ => memberProps_grows f _ ms

theorem agentObject_grows (f : Val Impl) (sl : Impl.Rec (Val Impl)) : GrowsR (Engine.Host.agentObject f sl) := by
  unfold Engine.Host.agentObject
  refine GrowsR.bind GrowsR.get fun _ => ?_
  refine GrowsR.bind (memberProps_grows _ _ _) fun _ => ?_
  refine GrowsR.bind (GrowsR.alloc _) fun _ => ?_
  exact GrowsR.pure' _

theorem newGlobals_grows (dda : Option FieldId) (g : Val Impl) : GrowsR (Engine.Host.newGlobals dda g) := by
  unfold Engine.Host.newGlobals
  refine GrowsR.bind (ownValue_grows _ _) fun _ => ?_
  refine GrowsR.bind (builtinLike_grows _ _ _ _) fun _ => ?_
  refine GrowsR.bind (builtinLike_grows _ _ _ _) fun _ => ?_
  refine GrowsR.bind (builtinLike_grows _ _ _ _) fun _ => ?_
  refine GrowsR.bind (builtinLike_grows _ _ _ _) fun _ => ?_
  refine GrowsR.bind (ownValue_grows _ _) fun _ => ?_
  refine GrowsR.bind (objectOf_grows _) fun p => ?_
  obtain ⟨_, _⟩ := p
  refine GrowsR.bind (dataProp_grows _ _ _ _) fun _ => ?_
  refine GrowsR.bind (dataProp_grows _ _ _ _) fun _ => ?_
  refine GrowsR.bind (dataProp_grows _ _ _ _) fun _ => ?_
  refine GrowsR.bind (dataProp_grows _ _ _ _) fun _ => ?_
  refine GrowsR.bind (agentObject_grows _ _) fun _ => ?_
  refine GrowsR.bind (dataProp_grows _ _ _ _) fun _ => ?_
  refine GrowsR.bind (ddaProps_grows _ _ _) fun _ => ?_
  refine GrowsR.bind (GrowsR.alloc _) fun _ => ?_
  refine GrowsR.bind (builtinLike_grows _ _ _ _) fun _ => ?_
  refine GrowsR.bind (dataProp_grows _ _ _ _) fun _ => ?_
  refine GrowsR.bind (dataProp_grows _ _ _ _) fun _ => ?_
  refine GrowsR.bind (dataProp_grows _ _ _ _) fun _ => ?_
  exact GrowsR.pure' _

/-- `objectOf` reads the object's cell. -/
theorem objectOf_ok {a : Impl.Addr} {s : State Impl} {sl : Impl.Rec (Val Impl)} {ps : Impl.Props (Val Impl)}
    {s' : State Impl} (h : Engine.Host.objectOf (.obj a) s = .ok (sl, ps) s') :
    s' = s ∧ Impl.heapGet s.heap a = some (.object sl ps) := by
  unfold Engine.Host.objectOf at h
  change Run.Res.bind (Ecma.readCell a s) _ = _ at h
  unfold Ecma.readCell at h
  split at h
  · rename_i c hc
    cases c <;> simp [Run.Res.bind, Run.stop, Run.pure, Pure.pure] at h
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h
    exact ⟨rfl, hc⟩
  · cases h

theorem globalProps_law (dda : Option FieldId) (realm : Val Impl) (g : Impl.Addr) (s : State Impl) (r : Val Impl)
    (s' : State Impl) (h : Engine.Host.globalProps dda [realm, .obj g] s = .ok r s') : r = unused ∧ onlyPropsOf g s s' ∧
    ∀ sl ps, Impl.heapGet s.heap g = some (.object sl ps) → Impl.heapGet s'.heap g = some (.object sl ps) ∨
      Impl.recGet sl Known.fExtensible = some (.bool true) ∧ ∃ pp po pt, Impl.heapGet s'.heap g =
        some (.object sl (Engine.Host.putNew (Engine.Host.putNew (Engine.Host.putNew ps "print" pp) "$262" po) "setTimeout" pt)) := by
  unfold Engine.Host.globalProps at h
  change Run.Res.bind (Engine.Host.newGlobals dda (.obj g) s) _ = _ at h
  cases h₁ : Engine.Host.newGlobals dda (.obj g) s with
  | ok x s₁ =>
    rw [h₁] at h
    obtain ⟨⟨k₁, rfl⟩, g₁⟩ := newGlobals_grows _ _ s x _ h₁
    obtain ⟨pp, po, pt⟩ := x
    change Run.Res.bind (Engine.Host.objectOf (.obj g) _) _ = _ at h
    cases h₂ : Engine.Host.objectOf (.obj g) { s with heap := k₁ } with
    | ok y s₂ =>
      rw [h₂] at h
      obtain ⟨sl, ps⟩ := y
      obtain ⟨rfl, hg⟩ := objectOf_ok h₂
      have hlt : @LT.lt Nat _ g k₁.size := by
        simp only [Impl, Impl] at hg
        exact (Array.getElem?_eq_some_iff.mp hg).1
      simp only [Run.Res.bind, Bind.bind, Run.bind, Pure.pure, Run.pure] at h
      split at h
      · rename_i hx
        replace hx : Impl.recGet sl Known.fExtensible = some (.bool true) := by
          revert hx; unfold Engine.Host.extensibleIn; split <;> simp_all
        simp only [Ecma.writeCell, Run.Res.bind, Run.bind, Run.pure] at h
        obtain ⟨rfl, rfl⟩ := h
        refine ⟨rfl, ⟨rfl, fun a c ha hc => ?_, fun sl₀ ps₀ h₀ => ?_⟩, fun sl₀ ps₀ h₀ => ?_⟩
        · simp only [Impl, Impl] at g₁ ⊢
          rw [Array.getElem?_setIfInBounds_ne (Ne.symm ha)]
          exact g₁ a c hc
        · have := g₁ g _ h₀
          rw [hg] at this
          cases this
          refine ⟨Engine.Host.putNew (Engine.Host.putNew (Engine.Host.putNew ps "print" pp) "$262" po) "setTimeout" pt, ?_⟩
          simp only [Impl, Impl]
          exact Array.getElem?_setIfInBounds_self_of_lt hlt
        · have := g₁ g _ h₀
          rw [hg] at this
          cases this
          refine .inr ⟨hx, pp, po, pt, ?_⟩
          simp only [Impl, Impl]
          exact Array.getElem?_setIfInBounds_self_of_lt hlt
      · obtain ⟨rfl, rfl⟩ := h
        refine ⟨rfl, ⟨rfl, fun a c _ hc => g₁ a c hc, fun sl₀ ps₀ h₀ => ⟨ps₀, g₁ g _ h₀⟩⟩, fun sl₀ ps₀ h₀ => .inl (g₁ g _ h₀)⟩
    | _ => rw [h₂] at h; cases h
  | _ => rw [h₁] at h; cases h

theorem choice_globalProps (c : Cells) (vs : List (Val Impl)) :
    (host c).choice Known.pHostGlobalProperties vs = Engine.Host.globalProps none vs := rfl

/-- TimeNow is the default clock, read back from the log's newest entries. -/
theorem choice_timeNow (c : Cells) (vs : List (Val Impl)) : (host c).choice Known.pTimeNow vs = readClock clockNumIn := by
  simp [host, Engine.Host.host, Engine.Host.agentJobs, Known.pAgentNextJob, Known.pAgentPrepareJob, Known.pAgentCleanupJob, choice, Known.pWebBrowser, Known.pApprox, Known.pNaNEncoding, Known.pApproxInteger,
    Known.pHostChoice, Known.pHostInitializeBuiltinContext,
    Known.pAdditionalTimeout, Known.pTimeZoneNameSuffix, Known.pSystemTimeZoneString,
    Known.pTimeNow, Engine.Host.clock]

end Engine.SpecHost
