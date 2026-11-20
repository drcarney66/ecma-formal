module

public import Engine.Host.Program
public import Engine.Host.SpecOpts

@[expose] public section

/-!
# The test host over its inputs

`hostBy o c` is `hostIn (σOf o) o c` (`hostBy_eq_hostIn`): HostSelectAgent and ChooseReadsBytesFrom at index 0
are `selectNext` and `scWrites`, and the seeded functions at `seedChoices n` are `draw n`'s.

The host over its inputs (`Choices`, `hostIn` and what it is made of, `fixedPrim`) is defined here: only the proofs
use it.
-/

namespace Engine.Host

open Ecma Engine

variable (N : Names)

/-- The choices no option changes. -/
def fixedPrim (p : PrimId) : Bool :=
  p != Known.pHostChoice && p != Known.pTimeNow && p != Known.pCanAllocate && p != Known.pWebBrowser &&
    p != Known.pHostGlobalProperties && p != Known.pAgentNextJob

/-! The host over its inputs `σ` (`hostIn`): `hostBy o` is the instance at `σOf o` . -/

/-- The host's inputs: the word for the decision `q` at host-log length `n` and item `i`. -/
abbrev Choices := PrimId → Nat → Nat → Nat

/-- The seed `N`'s inputs: `draw`'s word, 0 for the schedule and the reads. -/
def seedChoices (N : Nat) : Choices := fun q n _ =>
  if q == Known.pHostSelectAgent || q == Known.pChooseReadsBytesFrom then 0 else draw N q n

/-- The inputs whose answers are the options' own: the seed's (`seedChoices`), else 0. -/
def σOf (o : HostOpts) : Choices :=
  match o.seed with
  | some n => seedChoices n
  | none => fun _ _ _ => 0

/-- `timeAt` over `σ`. -/
def timeIn (σ : Choices) (n : Nat) : Nat :=
  min maxTime (σ 0 0 0 % 2 ^ 41 + 1000 * n + σ Known.pTimeNow n 0 % 1000)

/-- `seededTime` over `σ`. -/
def seededTimeIn (σ : Choices) (log : List (HostCall Impl)) : Nat :=
  min maxTime (timeIn σ log.length + (clockOf log).now)

/-- `seededNum` over `σ`. -/
def seededNumIn (σ : Choices) (log : List (HostCall Impl)) : Impl.Num :=
  let t := Impl.numOf (Impl.ofNat (seededTimeIn σ log))
  if instantB t then t else clockNum log

/-- `seededChoice` over `σ`. -/
def seededChoiceIn (σ : Choices) (p : PrimId) (vs : List (Val Impl)) : Run Impl (Val Impl) := fun s =>
  let r := σ p s.hostLog.length 0
  if p == Known.pHostChoice then match vs with
    | [.math a, .math b] =>
      if Engine.Model.MathVal.toNum a == Engine.Model.MathVal.toNum b then .ok (.math (if r % 2 == 0 then a else b)) s
      else .stop .residue
    | [.str a, .str b] => .ok (.str (if r % 2 == 0 then a else b)) s
    | _ => .stop .residue
  else if p == Known.pTimeNow then readClock (seededNumIn σ) s
  else if p == Known.pCanAllocate then match vs with
    | [.math n, .bool _] => .ok (.bool (!Impl.lt (Impl.ofNat 4294967296) n && r % 8 != 0)) s
    | _ => .stop .sortError
  else choice N p vs s

/-- `seededRandom` over `σ`. -/
def seededRandomIn (σ : Choices) : Run Impl (Val Impl) := fun s =>
  let x := Impl.numOf (Model.MathVal.ofQ (mkRat (σ randomKey s.hostLog.length 0 % 2 ^ 53) (2 ^ 53)))
  .ok (.num (if unitB x then x else Impl.numZero false)) s

/-- `seededPick` over `σ`. -/
def seededPickIn (σ : Choices) (own : Nat → Bool) (log : List (HostCall Impl)) : Option Nat :=
  let cs := (nextJobs N own log).filter fun k => timeIn σ k + dueAt log k ≤ maxTime
  cs[σ jobKey log.length 0 % cs.length]?

/-- `seededNextJob` over `σ`. -/
def seededNextJobIn (σ : Choices) : Run Impl (Option Nat) := fun s =>
  .ok (seededPickIn N σ (jobReady s) s.hostLog) s

/-- HostSelectAgent's answers: the `switchable` agents of `xs` after the surrounding one's, wrapping around. -/
def selectable {M : Model} (isAgent : State M → Val M → Bool) (xs : State M → List (Val M)) (s : State M) :
    List (Val M) :=
  (afterAgent (sigOf s s.agent) (xs s)).filter (switchable isAgent s)

/-- HostSelectAgent(_agent_, _n_) by `σ`: `selectable`'s answer at `σ`'s index, ~empty~ where there is none. -/
def selectIn {M : Model} (isAgent : State M → Val M → Bool) (xs : State M → List (Val M)) (σ : Choices) :
    List (Val M) → Run M (Val M)
  | [_, .math _] => fun s =>
    let l := selectable isAgent xs s
    match l[σ Known.pHostSelectAgent s.hostLog.length 0 % l.length]? with
    | some x => .ok x s
    | none => .ok (.enum Known.eEmpty) s
  | _ => Run.stop .sortError

/-- `ep` put into `es` before the first event not after it. -/
def insLatest {M : Model} (ep : Val M × (Nat × Nat)) : List (Val M × (Nat × Nat)) → List (Val M × (Nat × Nat))
  | [] => [ep]
  | q :: qs => if placeLe q.2 ep.2 then ep :: q :: qs else q :: insLatest ep qs

/-- The placed events `es` that write byte `loc` of `block`, latest first (`lastWrite` first). -/
def writesOn {M : Model} (isWrite : State M → Val M → Bool) (s : State M) (block : Val M) (loc : M.Math)
    (es : List (Val M × (Nat × Nat))) : List (Val M × (Nat × Nat)) :=
  es.foldl (fun acc ep => if writesByte isWrite s block loc ep.1 then insLatest ep acc else acc) []

/-- `eachByte` with each byte's number `j`. -/
def eachByteIx {M : Model} {α : Type} (f : Nat → M.Math → Option α) (idx : M.Math) (j₀ : Nat) :
    Nat → Option (List α)
  | 0 => some []
  | n + 1 => (f j₀ (M.add idx (M.ofNat j₀))).bind fun w => (eachByteIx f idx (j₀ + 1) n).map (w :: ·)

/-- ChooseReadsBytesFrom by `σ`: each byte `j`'s write at `σ`'s index (item `j`) of `writesOn`; residue for none. -/
def readsIn {M : Model} (isWrite : State M → Val M → Bool) (σ : Choices) (vs : List (Val M)) : Run M (Val M) :=
  fun s =>
  match readArgs vs with
  | some (ex, block, idx, size) =>
    let n := ceilIn size 17 0 65536
    if M.eq (M.ofNat n) size then
      match eachByteIx (fun j loc =>
          let ws := writesOn isWrite s block loc (placedEvents s (cutsOf s.hostLog) ex)
          ws[σ Known.pChooseReadsBytesFrom s.hostLog.length j % ws.length]?.map (·.1)) idx 0 n with
      | some ws => listOf ws s
      | none => .stop .residue
    else .stop .sortError
  | none => .stop .sortError

/-- `hookBy` over `σ`. -/
def hookIn (σ : Choices) (o : HostOpts) (c : Cells) (k : ClauseId) (vs : List (Val Impl)) : Run Impl (Val Impl) :=
  if o.resizeInPlace && N.clause k == some resizeClause then resizeInPlace N vs
  else match o.seed with
    | some _ => if N.clause k == some randomClause then seededRandomIn σ else hook N c k vs
    | none => hook N c k vs

/-- `choiceBy` over `σ`, with HostSelectAgent `selectIn` and ChooseReadsBytesFrom `readsIn`. -/
def choiceIn (σ : Choices) (o : HostOpts) (p : PrimId) : List (Val Impl) → Run Impl (Val Impl) :=
  if p == Known.pWebBrowser then fun vs => Run.pure (.bool (browserBy N o vs))
  else if p == Known.pHostGlobalProperties then globalProps (ddaBy N o)
  else if p == Known.pHostSelectAgent then selectIn (fun s => N.isRecordOf s "Agent Record") clusterSigs σ
  else if p == Known.pChooseReadsBytesFrom then readsIn (isWriteIn N) σ
  else match o.seed with
    | some _ => seededChoiceIn N σ p
    | none => choice N p

/-- `nextJobBy` over `σ`. -/
def nextJobIn (σ : Choices) (o : HostOpts) : Run Impl (Option Nat) :=
  match o.seed with
  | some _ => seededNextJobIn N σ
  | none => nextJob N

/-- `elapsedBy` over `σ`. -/
def elapsedIn (σ : Choices) (o : HostOpts) (s : State Impl) : Impl.Math :=
  match o.seed with
  | some _ => clockElapsed (seededPickIn N σ (jobReady s)) s.hostLog
  | none => elapsed N s

/-- The host with the options `o` and the inputs `σ`: the schedule, the reads and, with a seed, the seeded choices;
the rest (`first`, `idle`, `idleEnd` among it) `hostBy`'s. -/
def hostIn (σ : Choices) (o : HostOpts) (c : Cells) : Host Impl :=
  { hostBy N o c with
    hook := hookIn N σ o c, choice := agentJobs N c (nextJobIn N σ o) (choiceIn N σ o),
    nextJob := checkElapsed (elapsedIn N σ o) (nextJobIn N σ o), elapsed := elapsedIn N σ o }


/-- `seedChoices` off the schedule and the reads is `draw`. -/
theorem seedChoices_of {n q : Nat} (h : (q == Known.pHostSelectAgent || q == Known.pChooseReadsBytesFrom) = false)
    (m i : Nat) : seedChoices n q m i = draw n q m := by
  simp only [seedChoices, h, Bool.false_eq_true, ↓reduceIte]

/-- `timeIn` at the seed's inputs is `timeAt`. -/
theorem timeIn_seedChoices (n : Nat) : timeIn (seedChoices n) = timeAt n := by
  funext k
  simp only [timeIn, timeAt, seedChoices_of (q := 0) (by decide), seedChoices_of (q := Known.pTimeNow) (by decide)]

/-- `seededNumIn` at the seed's inputs is `seededNum`. -/
theorem seededNumIn_seedChoices (n : Nat) : seededNumIn (seedChoices n) = seededNum n := by
  funext log
  simp only [seededNumIn, seededNum, seededTimeIn, seededTime, timeIn_seedChoices]
  rfl

/-- `seededRandomIn` at the seed's inputs is `seededRandom`. -/
theorem seededRandomIn_seedChoices (n : Nat) : seededRandomIn (seedChoices n) = seededRandom n := by
  funext s
  simp only [seededRandomIn, seededRandom, seedChoices_of (q := randomKey) (by decide)]

/-- `seededPickIn` at the seed's inputs is `seededPick`. -/
theorem seededPickIn_seedChoices (n : Nat) : seededPickIn N (seedChoices n) = seededPick N n := by
  funext own log
  simp only [seededPickIn, seededPick, timeIn_seedChoices, seedChoices_of (q := jobKey) (by decide)]

/-- `seededNextJobIn` at the seed's inputs is `seededNextJob`. -/
theorem seededNextJobIn_seedChoices (n : Nat) : seededNextJobIn N (seedChoices n) = seededNextJob N n := by
  funext s
  simp only [seededNextJobIn, seededNextJob, seededPickIn_seedChoices]

/-- `seededChoiceIn` at the seed's inputs is `seededChoice` off the schedule and the reads. -/
theorem seededChoiceIn_seedChoices (n : Nat) {p : PrimId}
    (h : (p == Known.pHostSelectAgent || p == Known.pChooseReadsBytesFrom) = false) :
    seededChoiceIn N (seedChoices n) p = seededChoice N n p := by
  funext vs s
  simp only [seededChoiceIn, seededChoice, seedChoices_of h, seededNumIn_seedChoices]
  rfl

/-- `selectIn` at index 0 is `selectNext`. -/
theorem selectIn_zero {M : Model} (isAgent : State M → Val M → Bool) (xs : State M → List (Val M)) {σ : Choices}
    (h : ∀ n, σ Known.pHostSelectAgent n 0 = 0) : selectIn isAgent xs σ = selectNext isAgent xs := by
  funext vs
  have key : ∀ (a : Val M) (m : M.Math), selectIn isAgent xs σ [a, .math m] = selectNext isAgent xs [a, .math m] := by
    intro a m
    funext s
    unfold selectIn selectNext
    simp only [selectable, h, Nat.zero_mod, ← List.head?_eq_getElem?, List.head?_filter]
    rfl
  rcases vs with _ | ⟨a, _ | ⟨b, _ | ⟨c, t⟩⟩⟩
  · rfl
  · rfl
  · cases b <;> first | exact key _ _ | rfl
  · cases b <;> rfl

/-- `insLatest`'s first: `ep` unless `es`'s first is after it. -/
theorem head?_insLatest {M : Model} (ep : Val M × (Nat × Nat)) (l : List (Val M × (Nat × Nat))) :
    (insLatest ep l).head? = match l.head? with
      | some q => if placeLe q.2 ep.2 then some ep else some q
      | none => some ep := by
  cases l with
  | nil => rfl
  | cons q qs => simp only [insLatest, List.head?_cons]; split <;> rfl

/-- `writesOn`'s first is `lastWrite`. -/
theorem head?_writesOn {M : Model} (isWrite : State M → Val M → Bool) (s : State M) (block : Val M) (loc : M.Math)
    (es : List (Val M × (Nat × Nat))) : (writesOn isWrite s block loc es).head? = lastWrite isWrite s block loc es := by
  suffices ∀ (l : List (Val M × (Nat × Nat))) acc, l.head? = acc →
      (es.foldl (fun acc ep => if writesByte isWrite s block loc ep.1 then insLatest ep acc else acc) l).head? =
      es.foldl (fun acc ep => if writesByte isWrite s block loc ep.1 then
        match acc with
        | some q => if placeLe q.2 ep.2 then some ep else acc
        | none => some ep
      else acc) acc from this [] none rfl
  induction es with
  | nil => intro l acc h; exact h
  | cons ep es ih =>
    intro l acc h
    simp only [List.foldl_cons]
    apply ih
    split
    · rw [head?_insLatest, h]
      cases acc <;> rfl
    · exact h

/-- `eachByteIx` of a function not of the byte's number is `eachByte`. -/
theorem eachByteIx_const {M : Model} {α : Type} (f : M.Math → Option α) (idx : M.Math) (j₀ n : Nat) :
    eachByteIx (fun _ => f) idx j₀ n = eachByte f idx j₀ n := by
  induction n generalizing j₀ with
  | zero => rfl
  | succ n ih => simp only [eachByteIx, eachByte, ih]

/-- `readsIn` at index 0 is `scWrites`. -/
theorem readsIn_zero {M : Model} (isWrite : State M → Val M → Bool) {σ : Choices}
    (h : ∀ n i, σ Known.pChooseReadsBytesFrom n i = 0) : readsIn isWrite σ = scWrites isWrite := by
  funext vs s
  simp only [readsIn, scWrites, h, Nat.zero_mod, ← List.head?_eq_getElem?, head?_writesOn, eachByteIx_const]
  rfl

/-- `σOf` picks the first of HostSelectAgent's answers. -/
theorem σOf_select (o : HostOpts) (n : Nat) : σOf o Known.pHostSelectAgent n 0 = 0 := by
  rcases o with ⟨_ | m, _, _, _, _⟩ <;> simp [σOf, seedChoices]

/-- `σOf` picks each byte's latest write. -/
theorem σOf_reads (o : HostOpts) (n i : Nat) : σOf o Known.pChooseReadsBytesFrom n i = 0 := by
  rcases o with ⟨_ | m, _, _, _, _⟩ <;> simp [σOf, seedChoices]

/-- `choiceIn` at `σOf o` is `choiceBy`. -/
theorem choiceIn_σOf (o : HostOpts) : choiceIn N (σOf o) o = choiceBy N o := by
  funext p
  have hs := selectIn_zero (M := Impl) (fun s => N.isRecordOf s "Agent Record") clusterSigs (σOf_select o)
  have hr := readsIn_zero (isWriteIn N) (σOf_reads o)
  cases h1 : p == Known.pWebBrowser
  case true => simp only [choiceIn, choiceBy, h1, ↓reduceIte]
  cases h2 : p == Known.pHostGlobalProperties
  case true => simp only [choiceIn, choiceBy, h1, h2, ↓reduceIte, Bool.false_eq_true]
  cases h3 : p == Known.pHostSelectAgent
  case true =>
    obtain rfl : p = Known.pHostSelectAgent := by simpa using h3
    rcases o with ⟨_ | n, b, cb, w, ab⟩ <;> exact hs.trans rfl
  cases h4 : p == Known.pChooseReadsBytesFrom
  case true =>
    obtain rfl : p = Known.pChooseReadsBytesFrom := by simpa using h4
    rcases o with ⟨_ | n, b, cb, w, ab⟩ <;> exact hr.trans rfl
  have h : (p == Known.pHostSelectAgent || p == Known.pChooseReadsBytesFrom) = false := by
    simp only [h3, h4, Bool.or_self]
  rcases o with ⟨_ | n, b, cb, w, ab⟩
  · simp only [choiceIn, choiceBy, h1, h2, h3, h4, Bool.false_eq_true, ↓reduceIte]
  · simp only [choiceIn, choiceBy, σOf, h1, h2, h3, h4, Bool.false_eq_true, ↓reduceIte, seededChoiceIn_seedChoices N n h]

/-- `hookIn` at `σOf o` is `hookBy`. -/
theorem hookIn_σOf (o : HostOpts) (c : Cells) : hookIn N (σOf o) o c = hookBy N o c := by
  rcases o with ⟨_ | n, b, cb, w, ab⟩ <;> funext k vs <;> simp only [hookIn, hookBy, σOf, seededRandomIn_seedChoices]

/-- `nextJobIn` at `σOf o` is `nextJobBy`. -/
theorem nextJobIn_σOf (o : HostOpts) : nextJobIn N (σOf o) o = nextJobBy N o := by
  rcases o with ⟨_ | n, b, cb, w, ab⟩ <;> simp only [nextJobIn, nextJobBy, σOf, seededNextJobIn_seedChoices]

/-- `elapsedIn` at `σOf o` is `elapsedBy`. -/
theorem elapsedIn_σOf (o : HostOpts) : elapsedIn N (σOf o) o = elapsedBy N o := by
  rcases o with ⟨_ | n, b, cb, w, ab⟩ <;> funext s <;> simp only [elapsedIn, elapsedBy, σOf, seededPickIn_seedChoices]

/-- The host with the options `o` is `hostIn` at their inputs `σOf o`. -/
theorem hostBy_eq_hostIn (o : HostOpts) (c : Cells) : hostBy N o c = hostIn N (σOf o) o c := by
  simp only [hostBy, hostIn, hookIn_σOf, nextJobIn_σOf, elapsedIn_σOf, choiceIn_σOf]

/-- info: 'Engine.Host.hostBy_eq_hostIn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms hostBy_eq_hostIn

end Engine.Host

/-! The host over its inputs at Ecma.Gen's names. -/

namespace Engine.SpecHost

open Ecma Engine

export Engine.Host (fixedPrim Choices σOf timeIn seededTimeIn seededNumIn
  seededChoiceIn selectable selectIn insLatest writesOn eachByteIx readsIn)

abbrev seededNextJobIn := Engine.Host.seededNextJobIn names
abbrev choiceIn := Engine.Host.choiceIn names
abbrev nextJobIn := Engine.Host.nextJobIn names
abbrev hostIn := Engine.Host.hostIn names

end Engine.SpecHost
