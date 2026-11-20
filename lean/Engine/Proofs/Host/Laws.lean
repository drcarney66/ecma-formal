module

public import Ecma.Host.Laws
public import Engine.Host.Spec
public import Engine.Proofs.Host.ForIn
public import Engine.Proofs.Host.Sort

@[expose] public section

/-!
# The lemmas of the host laws

The proofs about the specification's host definitions that the engine's hosts share, kept out of
`lean/Ecma`, which holds no theorem (`scripts/quick_check.py` checks it): the log lemmas of the leaf
operations, and those of the host laws' definitions (`Ecma.Host.Laws`).
-/

namespace Ecma

/-- A state is `onlyAdds` of itself. -/
theorem onlyAdds_refl {M : Model} (to : M.Addr → Prop) (s : State M) : onlyAdds to s s :=
  ⟨rfl, fun _ _ h _ => h, fun _ _ ps _ h => ⟨ps, h, fun _ _ h => h, fun _ _ h => h⟩⟩

/-- `instantB` decides `instantTimeValue`. -/
theorem instantB_spec {M : Model} {n : M.Num} (h : instantB n = true) : instantTimeValue n := by
  unfold instantB at h
  unfold instantTimeValue
  split at h
  · exact .inl ‹_›
  · exact .inr (.inl ‹_›)
  · rename_i m hm
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at h
    exact .inr (.inr ⟨m, hm, h.1.1, h.1.2, h.2⟩)
  · cases h

/-- The default clock reads a time value identifying an instant, given that +0𝔽 is one. -/
theorem clockNum_instant {M : Model} (log : List (HostCall M)) (h0 : instantTimeValue (M.numZero false)) :
    instantTimeValue (clockNum log) := by
  unfold clockNum
  dsimp only
  split
  · exact instantB_spec ‹_›
  · exact h0

/-- The default clock by `nowIn` reads a time value identifying an instant, given that +0𝔽 is one. -/
theorem clockNumIn_instant {M : Model} (log : List (HostCall M)) (h0 : instantTimeValue (M.numZero false)) :
    instantTimeValue (clockNumIn log) := by
  unfold clockNumIn
  dsimp only
  split
  · exact instantB_spec ‹_›
  · exact h0

section Clock
variable {M : Model}

/-- `readClock`'s answer is the reading, the state as it was. -/
theorem readClock_ok {read : List (HostCall M) → M.Num} {s : State M} {r : Val M} {s' : State M}
    (h : readClock read s = .ok r s') : s' = s ∧ r = .num (read s.hostLog) := by
  unfold readClock at h
  simp only [Res.ok.injEq] at h
  exact ⟨h.2.symm, h.1.symm⟩

/-- `checkElapsed`'s answer is its run's, where `elapsedOk` checks it. -/
theorem checkElapsed_ok {e : State M → M.Math} {m : Run M (Option Nat)} {s : State M} {k : Option Nat}
    {s' : State M} (h : checkElapsed e m s = .ok k s') : m s = .ok k s' ∧ elapsedOk s.hostLog k (e s) = true := by
  dsimp only [checkElapsed] at h
  revert h
  cases m s with
  | ok k' t =>
    dsimp only
    split
    · intro h; cases h; exact ⟨rfl, ‹_›⟩
    · intro h; cases h
  | _ => intro h; cases h

/-- A host whose next job is `checkElapsed`'s at its own clock never reads it back. -/
theorem elapsedMono_of_check {H : Host M} {m : Run M (Option Nat)} (hH : H.nextJob = checkElapsed H.elapsed m) :
    ∀ s k (s' : State M), H.nextJob s = .ok k s' → ∀ j t, HostCall.next j t ∈ s.hostLog →
    M.lt (H.elapsed s) t = false := by
  intro s k s' h j t hm
  rw [hH] at h
  have h := (checkElapsed_ok h).2
  simp only [elapsedOk, Bool.and_eq_true, List.all_eq_true] at h
  simpa [HostCall.notAfter] using h.1 _ hm

/-- A host whose next job is `checkElapsed`'s at its own clock takes a timeout job at least its
_milliseconds_ past the elapsed time logged before its call (§9.5.6). -/
theorem timeoutAfter_of_check {H : Host M} {m : Run M (Option Nat)} (hH : H.nextJob = checkElapsed H.elapsed m) :
    ∀ (s : State M) pre c job realm ms a rl r rest (s' : State M),
    s.hostLog = pre ++ .hook c [job, realm, .num ms] a rl r :: rest →
    Gen.clauses[c]? = some "sec-hostenqueuetimeoutjob" → H.nextJob s = .ok (some rest.length) s' →
    mathAfter (lastElapsed rest) (H.elapsed s) ms = true := by
  intro s pre c job realm ms a rl r rest s' hl _ h
  rw [hH] at h
  have h := (checkElapsed_ok h).2
  have hd : s.hostLog.length - 1 - rest.length = pre.length := by simp [hl]
  simp only [elapsedOk, Bool.and_eq_true, hd] at h
  rw [hl, List.drop_left] at h
  simpa [HostCall.timeoutMs] using h.2

end Clock

theorem wakeFinite_eq {M : Model} (vs : List (Val M)) : wakeFinite vs = (wakeTime vs).isSome := by
  rcases vs with _ | ⟨_, _ | ⟨v, _ | _⟩⟩
  · rfl
  · rfl
  · cases v <;> simp [wakeFinite, wakeTime]
    cases M.lt (M.ofNat maxTime) _ <;> simp
  · cases v <;> rfl

theorem pendingFinite_eq {M : Model} (x sig : Val M) :
    ∀ es, pendingFinite x sig es = (pendingIn x sig es).map Option.isSome
  | [] => rfl
  | (e, a) :: es => by
    cases e with
    | choice q vs ans =>
      simp only [pendingFinite, pendingIn]
      split
      · rfl
      · split
        · simp [wakeFinite_eq]
        · exact pendingFinite_eq x sig es
    | _ => exact pendingFinite_eq x sig es

theorem canRunAgent_of_runnable {M : Model} {s : State M} {x : Val M} (h : runnable s x = true) :
    canRunAgent s x = true := by
  simp only [runnable, Bool.or_eq_true, Bool.and_eq_true] at h
  simp only [canRunAgent, Bool.or_eq_true, Bool.and_eq_true]
  rcases h with hp | ⟨hi, hr⟩
  · left
    rw [pendingFinite_eq]
    change (match pendingAt s x with | none => true | some none => false | some (some t) => _) = true at hp
    unfold pendingAt at hp
    cases hpa : pendingIn x (sigOf s x) (withAgents s.agent s.hostLog)
    · rfl
    · rename_i o
      rw [hpa] at hp
      cases o <;> simp at hp ⊢
  · refine .inr ⟨hi, ?_⟩
    simp only [hasReadyJob, hasScheduledJob, List.any_eq_true] at hr ⊢
    obtain ⟨ek, hmem, hok⟩ := hr
    simp only [Bool.and_eq_true, readyFor] at hok
    exact ⟨ek, hmem, by simp [hok.1.1, hok.1.2.1, hok.2]⟩

/-- Round-robin HostSelectAgent gives ~empty~ or an agent (`isAgent`) of the cluster by its signifier,
other than the surrounding one, that can run; the state as it was. -/
theorem selectNext_law {M : Model} {isAgent : State M → Val M → Bool} {xs : State M → List (Val M)}
    {vs : List (Val M)} {s : State M} {r : Val M} {s' : State M} (h : selectNext isAgent xs vs s = .ok r s') :
    s' = s ∧ (r = .enum Known.eEmpty ∨ isAgent s r = true ∧
      (clusterSigs s).any (Val.same (sigOf s r)) = true ∧ Val.same (sigOf s r) (sigOf s s.agent) = false ∧
      Val.same r s.agent = false ∧ canRunAgent s r = true) := by
  match vs, h with
  | [], h | [_], h => unfold selectNext at h; cases h
  | _ :: v :: _ :: _, h => unfold selectNext at h; cases v <;> cases h
  | [_, v], h =>
    unfold selectNext at h
    cases v <;> first | cases h | skip
    dsimp only at h
    split at h
    · rename_i x hx
      simp only [Res.ok.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      have hp := List.find?_some hx
      simp only [switchable, Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at hp
      exact ⟨rfl, .inr ⟨hp.1.1.1.1, hp.1.1.1.2, hp.1.1.2, hp.1.2, canRunAgent_of_runnable hp.2⟩⟩
    · simp only [Res.ok.injEq] at h
      exact ⟨h.2.symm, .inl h.1.symm⟩

/-- ChooseReadsBytesFrom's arguments as `readArgs` reads them. -/
theorem readArgs_some {M : Model} {vs : List (Val M)} {ex block : Val M} {idx size : M.Math}
    (h : readArgs vs = some (ex, block, idx, size)) : ∃ er, vs = [ex, er, block, .math idx, .math size] := by
  match vs, h with
  | [a, b, c, d, e], h =>
    simp only [readArgs] at h
    split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl, rfl⟩ := h
      exact ⟨b, rfl⟩
    · cases h
  | [], h | [_], h | [_, _], h | [_, _, _], h | [_, _, _, _], h | _ :: _ :: _ :: _ :: _ :: _ :: _, h =>
    simp [readArgs] at h

/-- `eachByte` gives `n` values, the one at index `k` `f`'s at `idx` + `j₀` + `k`. -/
theorem eachByte_spec {M : Model} {α : Type} {f : M.Math → Option α} {idx : M.Math} :
    ∀ {j₀ n : Nat} {ws : List α}, eachByte f idx j₀ n = some ws →
    ws.length = n ∧ ∀ k w, ws[k]? = some w → f (M.add idx (M.ofNat (j₀ + k))) = some w
  | _, 0, ws, h => by
    simp only [eachByte, Option.some.injEq] at h
    subst h; exact ⟨rfl, fun _ _ h => by simp at h⟩
  | j₀, n + 1, ws, h => by
    simp only [eachByte, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨w, hw, ws', hr, rfl⟩ := h
    obtain ⟨hl, hk⟩ := eachByte_spec hr
    refine ⟨by simp [hl], fun k x hx => ?_⟩
    cases k with
    | zero => simp only [List.getElem?_cons_zero, Option.some.injEq] at hx; subst hx; simpa using hw
    | succ k =>
      simp only [List.getElem?_cons_succ] at hx
      have e : j₀ + (k + 1) = j₀ + 1 + k := by omega
      rw [e]; exact hk k x hx

/-- An event `placed` is one of the events. -/
theorem mem_placed {M : Model} {f : Nat → Nat × Nat} {w : Val M} {p : Nat × Nat} :
    ∀ {i : Nat} {es : List (Val M)}, (w, p) ∈ placed f i es → w ∈ es
  | _, [], h => by simp [placed] at h
  | _, _ :: _, h => by
    simp only [placed, List.mem_cons, Prod.mk.injEq] at h
    rcases h with ⟨rfl, _⟩ | h
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (mem_placed h)

/-- A placed event of the candidate execution `ex` is one of its events. -/
theorem mem_placedEvents {M : Model} {s : State M} {cuts : List (Val M × M.Math)} {ex w : Val M}
    {p : Nat × Nat} (h : (w, p) ∈ placedEvents s cuts ex) : w ∈ execEvents s ex := by
  simp only [placedEvents, execEvents, List.mem_flatMap] at h ⊢
  obtain ⟨er, her, hw⟩ := h
  exact ⟨er, her, mem_placed hw⟩

/-- The latest write of byte `loc` is one of the placed events, and writes it. -/
theorem lastWrite_spec {M : Model} {isWrite : State M → Val M → Bool} {s : State M} {block : Val M}
    {loc : M.Math} {es : List (Val M × (Nat × Nat))} {q : Val M × (Nat × Nat)}
    (h : lastWrite isWrite s block loc es = some q) : q ∈ es ∧ writesByte isWrite s block loc q.1 = true := by
  let P : Option (Val M × (Nat × Nat)) → Prop := fun o => ∀ q, o = some q → q ∈ es ∧ writesByte isWrite s block loc q.1 = true
  have step : ∀ (l : List (Val M × (Nat × Nat))), (∀ x ∈ l, x ∈ es) → ∀ acc, P acc →
      P (l.foldl (fun acc ep => if writesByte isWrite s block loc ep.1 then
        match acc with
        | some q => if placeLe q.2 ep.2 then some ep else acc
        | none => some ep
      else acc) acc) := by
    intro l
    induction l with
    | nil => intro _ acc h; exact h
    | cons x l ih =>
      intro hl acc hacc
      simp only [List.foldl_cons]
      refine ih (fun y hy => hl y (List.mem_cons_of_mem _ hy)) _ ?_
      have hx := hl x List.mem_cons_self
      split
      · rename_i hw
        split
        · split
          · intro q e; simp only [Option.some.injEq] at e; subst e; exact ⟨hx, hw⟩
          · exact hacc
        · intro q e; simp only [Option.some.injEq] at e; subst e; exact ⟨hx, hw⟩
      · exact hacc
  exact step es (fun _ h => h) none (fun _ e => nomatch e) q h

/-- Sequentially consistent ChooseReadsBytesFrom gives a new List of _elementSize_ events of the
execution, each a write (`isWrite`) of its byte of the block; the state as it was but for the List. -/
theorem scWrites_law {M : Model} {isWrite : State M → Val M → Bool} {vs : List (Val M)} {s : State M}
    {r : Val M} {s' : State M} (h : scWrites isWrite vs s = .ok r s') :
    ∃ ex er block idx size ws, vs = [ex, er, block, .math idx, .math size] ∧ listOf ws s = .ok r s' ∧
      M.eq (M.ofNat ws.length) size = true ∧
      ∀ j w, ws[j]? = some w → w ∈ execEvents s ex ∧ writesByte isWrite s block (M.add idx (M.ofNat j)) w = true := by
  simp only [scWrites] at h
  split at h
  · rename_i ex block idx size hargs
    obtain ⟨er, rfl⟩ := readArgs_some hargs
    split at h
    · rename_i heq
      split at h
      · rename_i ws hws
        obtain ⟨hl, hk⟩ := eachByte_spec hws
        refine ⟨ex, er, block, idx, size, ws, rfl, h, by rw [hl]; exact heq, fun j w hw => ?_⟩
        have hf := hk j w hw
        rw [Nat.zero_add] at hf
        simp only [Option.map_eq_some_iff] at hf
        obtain ⟨q, hq, rfl⟩ := hf
        obtain ⟨hm, hb⟩ := lastWrite_spec hq
        exact ⟨mem_placedEvents hm, hb⟩
      · cases h
    · cases h
  · cases h

/-- Every format with 2 ≤ p has a NaN: the canonical quiet NaN. -/
theorem nanCode_bits (w p : Nat) (hp : 2 ≤ p) : nanBits w p (nanCode w p) := by
  obtain ⟨q, rfl⟩ : ∃ q, p = q + 2 := ⟨p - 2, by omega⟩
  have hA : 0 < 2 ^ w := Nat.two_pow_pos w
  have hB : 0 < 2 ^ q := Nat.two_pow_pos q
  have hC : 2 ^ (q + 1) = 2 * 2 ^ q := by rw [Nat.pow_succ, Nat.mul_comm]
  have e1 : q + 2 - 1 = q + 1 := by omega
  have e2 : q + 2 - 2 = q := by omega
  have hk : nanCode w (q + 2) = 2 ^ q + 2 ^ (q + 1) * (2 ^ w - 1) := by
    unfold nanCode; rw [e1, e2, Nat.mul_comm, Nat.add_comm]
  rw [nanBits, hk, e1]
  refine ⟨?_, ?_, ?_⟩
  · have hm : 2 ^ (q + 1) * (2 ^ w - 1) + 2 ^ (q + 1) = 2 ^ (q + 1) * 2 ^ w := by
      rw [Nat.mul_sub_one]
      have : 2 ^ (q + 1) ≤ 2 ^ (q + 1) * 2 ^ w := Nat.le_mul_of_pos_right _ hA
      omega
    have hp2 : 2 ^ (w + (q + 2)) = 2 * (2 ^ (q + 1) * 2 ^ w) := by
      rw [← Nat.pow_add, Nat.add_comm (q + 1) w, show w + (q + 2) = (w + (q + 1)) + 1 by omega, Nat.pow_succ,
        Nat.mul_comm]
    rw [hp2]
    have : 2 ^ q < 2 ^ (q + 1) := by omega
    have : 0 < 2 ^ (q + 1) * 2 ^ w := Nat.mul_pos (by omega) hA
    omega
  · rw [Nat.add_mul_div_left _ _ (by omega : 0 < 2 ^ (q + 1)),
      Nat.div_eq_of_lt (by omega : 2 ^ q < 2 ^ (q + 1)), Nat.zero_add, Nat.mod_eq_of_lt (by omega)]
  · rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega : 2 ^ q < 2 ^ (q + 1))]
    omega

/-- binary32's and binary64's canonical quiet NaNs. -/
example : nanCode 8 24 = 0x7FC00000 ∧ nanCode 11 53 = 0x7FF8000000000000 := by decide

/-- `secOf` unfolded. -/
theorem secOf_eq (c : ClauseId) : secOf c = Gen.clauses[c]? := by unfold secOf; rfl

/-- A host whose WebBrowser choice is a Boolean of its arguments alone meets the web-browser law. -/
theorem webBrowser_of {M : Model} {H : Host M} (f : List (Val M) → Bool)
    (h : ∀ vs, H.choice Known.pWebBrowser vs = Run.pure (.bool (f vs))) (vs : List (Val M)) :
    ∃ b', ∀ s, H.choice Known.pWebBrowser vs s = .ok (.bool b') s :=
  ⟨f vs, fun _ => by rw [h]; rfl⟩

/-- A host whose WebBrowser choice is one Boolean at every call meets the web-browser law. -/
theorem webBrowser_const {M : Model} {H : Host M} (b : Bool)
    (h : ∀ vs, H.choice Known.pWebBrowser vs = Run.pure (.bool b)) (vs : List (Val M)) :
    ∃ b', ∀ s, H.choice Known.pWebBrowser vs s = .ok (.bool b') s :=
  webBrowser_of (fun _ => b) h vs

/-- Such a host, true for every clause wherever it is a web browser, meets the browser-supports law. -/
theorem webBrowserSupports_of {M : Model} {H : Host M} (f : List (Val M) → Bool)
    (h : ∀ vs, H.choice Known.pWebBrowser vs = Run.pure (.bool (f vs)))
    (hf : f [.choice 1, .absent] = true → ∀ c, f [.choice 0, .clause c] = true) (c : ClauseId) (s : State M)
    (hw : H.choice Known.pWebBrowser [.choice 1, .absent] s = .ok (.bool true) s) :
    H.choice Known.pWebBrowser [.choice 0, .clause c] s = .ok (.bool true) s := by
  rw [h] at hw
  simp only [Run.pure, Res.ok.injEq, Val.bool.injEq, and_true] at hw
  rw [h, hf hw c]; rfl

/-- A host whose WebBrowser choice is one Boolean meets the browser-supports law. -/
theorem webBrowserSupports_const {M : Model} {H : Host M} (b : Bool)
    (h : ∀ vs, H.choice Known.pWebBrowser vs = Run.pure (.bool b)) (c : ClauseId) (s : State M)
    (hw : H.choice Known.pWebBrowser [.choice 1, .absent] s = .ok (.bool true) s) :
    H.choice Known.pWebBrowser [.choice 0, .clause c] s = .ok (.bool true) s :=
  webBrowserSupports_of (fun _ => b) h (fun hb _ => hb) c s hw

/-- Document order is a permutation of the given List's elements, in a new List. -/
theorem documentOrder_perm {M : Model} (o l : Val M) (s : State M) (r : Val M) (s' : State M)
    (h : documentOrder [o, l] s = .ok r s') :
    ∃ xs ys, listElems s l = some xs ∧ ys.Perm xs ∧ listOf ys s = .ok r s' := by
  unfold documentOrder at h
  dsimp only at h
  split at h
  · next xs hx => exact ⟨xs, xs, hx, .refl _, h⟩
  · cases h

/-- A key's value in an association list is one of its pairs. -/
theorem lookup_some_mem {α β : Type} [BEq α] [LawfulBEq α] {l : List (α × β)} {k : α} {b : β}
    (h : l.lookup k = some b) : (k, b) ∈ l := by
  induction l with
  | nil => cases h
  | cons p l ih =>
    obtain ⟨k', b'⟩ := p
    by_cases hk : k = k'
    · subst hk
      simp only [List.lookup_cons_self, Option.some.injEq] at h
      subst h
      exact List.mem_cons_self
    · have : (k == k') = false := by simpa using hk
      simp only [List.lookup, this] at h
      exact List.mem_cons_of_mem _ (ih h)

/-- An index `idxOf?` gives holds the value. -/
theorem idxOf?_getElem? {α : Type} [BEq α] [LawfulBEq α] {xs : Array α} {a : α} {i : Nat}
    (h : xs.idxOf? a = some i) : xs[i]? = some a := by
  rcases xs with ⟨l⟩
  simp only [List.idxOf?_toArray, List.idxOf?_eq_some_iff] at h
  obtain ⟨hi, ha, -⟩ := h
  simp [hi, ha]

/-! The locale-sensitive choices' strategies (`Ecma.Strategy`) and their laws. -/

section Locale
variable {M : Model}

/-- `caseAsDefault` gives a new List of code points. -/
theorem caseAsDefault_law (f : M.Seq M.Math → M.Seq M.Math) (l : Val M) (s : State M) (r : Val M)
    (s' : State M) (h : caseAsDefault f [l] s = .ok r s') :
    ∃ cps : List M.Math, (∀ c ∈ cps, Prims.Strings.isPoint c = true) ∧ listOf (cps.map .math) s = .ok r s' := by
  unfold caseAsDefault at h
  dsimp only at h
  split at h
  · split at h
    · rename_i hall
      exact ⟨_, fun c hc => List.all_eq_true.mp hall c hc, h⟩
    · cases h
  · cases h

/-- `dateAsDefault` obeys LocaleDateString's law. -/
theorem dateAsDefault_law (k v : Val M) (s : State M) (r : Val M) (s' : State M)
    (h : dateAsDefault [k, v] s = .ok r s') : s' = s ∧
    (dateValued s v = true → r = .enum Known.eEmpty ∨ ∃ x, r = .str x) ∧
    (dateValued s v = false → r = .enum Known.eThrow ∨ ∃ x, r = .str x) := by
  unfold dateAsDefault at h
  simp only [Res.ok.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  exact ⟨rfl, fun hd => .inl (by simp [hd]), fun hd => .inl (by simp [hd])⟩

theorem natLexLt_irrefl : ∀ x : List Nat, natLexLt x x = false
  | [] => rfl
  | a :: as => by simp [natLexLt, natLexLt_irrefl as]

theorem natLexLt_trans (x y z : List Nat) (h1 : natLexLt x y = true) (h2 : natLexLt y z = true) :
    natLexLt x z = true := by
  induction x generalizing y z with
  | nil => cases y with
    | nil => simp [natLexLt] at h1
    | cons b bs => cases z with
      | nil => simp [natLexLt] at h2
      | cons c cs => rfl
  | cons a as ih => cases y with
    | nil => simp [natLexLt] at h1
    | cons b bs => cases z with
      | nil => simp [natLexLt] at h2
      | cons c cs =>
        simp only [natLexLt, Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true, beq_iff_eq] at h1 h2 ⊢
        rcases h1 with h1 | ⟨rfl, h1⟩ <;> rcases h2 with h2 | ⟨rfl, h2⟩
        · exact .inl (Nat.lt_trans h1 h2)
        · exact .inl h1
        · exact .inl h2
        · exact .inr ⟨rfl, ih bs cs h1 h2⟩

theorem natLexLt_tri (x y : List Nat) : natLexLt x y = true ∨ x = y ∨ natLexLt y x = true := by
  induction x generalizing y with
  | nil => cases y with
    | nil => exact .inr (.inl rfl)
    | cons => exact .inl rfl
  | cons a as ih => cases y with
    | nil => exact .inr (.inr rfl)
    | cons b bs =>
      simp only [natLexLt, Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true, beq_iff_eq, List.cons.injEq]
      rcases Nat.lt_trichotomy a b with h | rfl | h
      · exact .inl (.inl h)
      · rcases ih bs with h | h | h
        · exact .inl (.inr ⟨rfl, h⟩)
        · exact .inr (.inl ⟨rfl, h⟩)
        · exact .inr (.inr (.inr ⟨rfl, h⟩))
      · exact .inr (.inr (.inl h))

theorem natLexLt_asymm {x y : List Nat} (h1 : natLexLt x y = true) (h2 : natLexLt y x = true) : False := by
  have := natLexLt_trans _ _ _ h1 h2
  rw [natLexLt_irrefl] at this
  cases this

/-- `compareBy g` obeys the law of LocaleCompare, given -1𝔽 negative, 1𝔽 positive and +0𝔽's view. -/
theorem compareBy_law (g : M.Seq M.Math → List Nat) (hneg : negNum (M.numOf (M.neg (M.ofNat 1))))
    (hpos : posNum (M.numOf (M.ofNat 1))) (hz : M.numView (M.numZero false) = .posZero) :
    ∃ le : M.Str → M.Str → Prop, (∀ a b, le a b ∨ le b a) ∧ (∀ a b c, le a b → le b c → le a c) ∧
      ∀ a b s r s', compareBy g [.str a, .str b] s = .ok r s' → s' = s ∧ ∃ n, r = .num n ∧
        (¬le b a → negNum n) ∧ (¬le a b → posNum n) ∧ (le a b → le b a → zeroNum n) ∧
        (canonEquiv a b → M.numView n = .posZero) := by
  refine ⟨fun a b => natLexLt (nfdKey g b) (nfdKey g a) = false, ?_, ?_, ?_⟩
  · intro a b
    cases h : natLexLt (nfdKey g b) (nfdKey g a)
    · exact .inl h
    · cases h' : natLexLt (nfdKey g a) (nfdKey g b)
      · exact .inr h'
      · exact (natLexLt_asymm h h').elim
  · intro a b c h1 h2
    cases h3 : natLexLt (nfdKey g c) (nfdKey g a)
    · rfl
    · exfalso
      rcases natLexLt_tri (nfdKey g b) (nfdKey g a) with h | h | h
      · rw [h1] at h; cases h
      · rw [h] at h2; rw [h2] at h3; cases h3
      · have := natLexLt_trans _ _ _ h3 h
        rw [h2] at this; cases this
  · intro a b s r s' h
    have key : canonEquiv a b → nfdKey g a = nfdKey g b := fun hc => by
      unfold nfdKey; rw [hc]
    simp only [compareBy, Run.pure, Res.ok.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    refine ⟨rfl, _, rfl, ?_⟩
    by_cases hab : natLexLt (nfdKey g a) (nfdKey g b) = true
    · rw [if_pos hab]
      refine ⟨fun _ => hneg, fun h => (natLexLt_asymm hab (by simpa using h)).elim,
        fun _ h => (Bool.false_ne_true (h.symm.trans hab)).elim, fun hc => ?_⟩
      rw [key hc, natLexLt_irrefl] at hab; cases hab
    · have hab' : natLexLt (nfdKey g a) (nfdKey g b) = false := by simpa using hab
      rw [if_neg hab]
      by_cases hba : natLexLt (nfdKey g b) (nfdKey g a) = true
      · rw [if_pos hba]
        refine ⟨fun h => (h hab').elim, fun _ => hpos,
          fun h _ => (Bool.false_ne_true (h.symm.trans hba)).elim, fun hc => ?_⟩
        rw [key hc, natLexLt_irrefl] at hba; cases hba
      · have hba' : natLexLt (nfdKey g b) (nfdKey g a) = false := by simpa using hba
        rw [if_neg hba]
        exact ⟨fun h => (h hab').elim, fun h => (h hba').elim, fun _ _ => .inl hz, fun _ => hz⟩

end Locale

/-! The Date Time String Format's calendar bounds. -/

/-- A year has at most one leap day. -/
theorem leapDays_le (y : Int) : leapDays y ≤ 1 := by
  unfold leapDays; split <;> (try split) <;> (try split) <;> omega

/-- A month has at most 31 days. -/
theorem daysInMonth_le (y : Int) (mo : Nat) : daysInMonth y mo ≤ 31 := by
  have hl := leapDays_le y
  have hm : ∀ x ∈ [31, 28 + leapDays y, 31, 30, 31, 30, 31, 31, 30, 31, 30, 31], x ≤ 31 := by simp; omega
  unfold daysInMonth
  rw [List.getD_eq_getElem?_getD]
  cases h : [31, 28 + leapDays y, 31, 30, 31, 30, 31, 31, 30, 31, 30, 31][mo - 1]? with
  | none => simp
  | some x => exact hm x (List.mem_of_getElem? h)

end Ecma
