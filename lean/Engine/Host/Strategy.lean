module

public import Ecma.Prims.Strings
public import Ecma.Host.Laws
public import Ecma.Host.ForIn

@[expose] public section

/-!
# The engine host's strategies, generic in the model

The host choices' strategies that `Engine.Host` and `Engine.Proofs.Host` share: NaN's canonical
encoding (`nanCode`), the default clock (`clockNum`, `dueAt`, `nowIn`, `clockNumIn`, `dueIn`,
`clockElapsedIn`, `readClock`), agent scheduling and timeouts (`wakeTime`, `pendingIn`, `pendingAt`,
`readyFor`, `hasReadyJob`, `jobDue`, `runnable`, `jobReady`, `switchable`, `suspendedAgents`,
`earliestWake`, `agentWoken`, `agentTimeout`, `afterAgent`, `selectNext`, `suspendUntil`),
sequentially consistent reads (`lastWrite`, `eachByte`, `readArgs`, `scWrites`), PropertyOrder in
document order (`documentOrder`), `forInChoice`, the locale-sensitive defaults (`caseAsDefault`,
`compareBy`, `dateAsDefault`), `NativeFunctionSource` (`nativeNameOf`, `nativeAnswer`,
`initialNameIn`), and `SortStep`'s binary insertion sort (`BinSort`, `sortStepBy`).
-/

namespace Ecma

/-- The canonical quiet NaN's encoding, sign 0: (2^w − 1)·2^(p−1) + 2^(p−2). -/
def nanCode (w p : Nat) : Nat := (2 ^ w - 1) * 2 ^ (p - 1) + 2 ^ (p - 2)

/-- The least `k` from `lo` to `hi` with `x ≤ k` (by `M.lt`), halving `f` times; `hi` where there is none. -/
def ceilIn {M : Model} (x : M.Math) : Nat → Nat → Nat → Nat
  | 0, _, hi => hi
  | f + 1, lo, hi =>
    if lo < hi then
      if M.lt (M.ofNat ((lo + hi) / 2)) x then ceilIn x f ((lo + hi) / 2 + 1) hi else ceilIn x f lo ((lo + hi) / 2)
    else hi

/-- A Number of milliseconds rounded up, at most `maxTime + 1`; 0 where it is not finite. -/
def msCeil {M : Model} (n : M.Num) : Nat :=
  match M.numView n with
  | .finite m => ceilIn m 64 0 (maxTime + 1)
  | _ => 0

/-- The _milliseconds_ of a call that schedules a timeout job (HostEnqueueTimeoutJob's third
argument); none for a call of another shape. -/
def HostCall.timeoutMs {M : Model} : HostCall M → Option M.Num
  | .hook _ [_, _, .num n] _ _ _ => some n
  | _ => none

/-- The delay of a call that schedules a timeout job, rounded up; 0 for a call of another shape. -/
def HostCall.delay {M : Model} (e : HostCall M) : Nat := (e.timeoutMs.map msCeil).getD 0

/-- The default clock after a log prefix: the time in milliseconds, and each logged call's due time
(the time before it plus its delay). -/
structure Clock where
  now : Nat
  due : Array Nat

/-- The time in milliseconds an AgentTimeout answer moves the clock to: rounded up, at most
`maxTime + 1`; 0 for an answer of another shape. -/
def timeoutTo {M : Model} : Val M → Nat
  | .math t => ceilIn t 64 0 (maxTime + 1)
  | _ => 0

/-- A TimeNow reading and an agent's selection add 1 ms; an AgentTimeout moves the time to at least
its answer; taking a job moves the time to at least its call's due time. -/
def Clock.step {M : Model} (k : Clock) (e : HostCall M) : Clock :=
  let now := match e with
    | .choice q _ r => if q == Known.pTimeNow || q == Known.pHostSelectAgent && selects r then k.now + 1
      else if q == Known.pAgentTimeout then max k.now (timeoutTo r) else k.now
    | .next (some j) _ => max k.now (k.due[j]?.getD 0)
    | _ => k.now
  ⟨now, k.due.push (k.now + e.delay)⟩

/-- The default clock after a host log (newest first), from 0. -/
def clockOf {M : Model} (log : List (HostCall M)) : Clock := log.reverse.foldl Clock.step ⟨0, #[]⟩

/-- The due time of the call at log position `k`. -/
def dueAt {M : Model} (log : List (HostCall M)) (k : Nat) : Nat := (clockOf log).due[k]?.getD 0

/-- The default clock's reading in milliseconds: 1 more than the time, at most `maxTime`. -/
def clockAt {M : Model} (log : List (HostCall M)) : Nat := min maxTime ((clockOf log).now + 1)

/-- A time value identifying an instant (`instantTimeValue`), decided. -/
def instantB {M : Model} (n : M.Num) : Bool :=
  match M.numView n with
  | .posZero | .negZero => true
  | .finite m => M.isInt m && !M.lt m (M.neg (M.ofNat maxTime)) && !M.lt (M.ofNat maxTime) m
  | _ => false

/-- The default clock's reading: `clockAt` as a Number, else +0𝔽. -/
def clockNum {M : Model} (log : List (HostCall M)) : M.Num :=
  let n := M.numOf (M.ofNat (clockAt log))
  if instantB n then n else M.numZero false

/-- The time in milliseconds after the log `log`, from its newest TimeNow reading, AgentTimeout
answer or taken job's due time, or from 0 at no cost per call past it (`clockOf.now` up to calls
whose elapsed time the log already carries). -/
def nowIn {M : Model} : List (HostCall M) → Nat
  | [] => 0
  | e :: log => match e with
    | .choice q _ (.num n) => if q == Known.pTimeNow then match M.numView n with
      | .finite m => ceilIn m 64 0 (maxTime + 1)
      | _ => 0
      else nowIn log
    | .choice q _ (.ref _) => if q == Known.pHostSelectAgent then nowIn log + 1 else nowIn log
    | .choice q _ r => if q == Known.pAgentTimeout then max (nowIn log) (timeoutTo r) else nowIn log
    | .next (some _) t => ceilIn t 64 0 (maxTime + 1)
    | _ => nowIn log

/-- `nowIn`'s TimeNow reading: 1 more than the time, at most `maxTime`, as a Number, else +0𝔽. -/
def clockNumIn {M : Model} (log : List (HostCall M)) : M.Num :=
  let n := M.numOf (M.ofNat (min maxTime (nowIn log + 1)))
  if instantB n then n else M.numZero false

/-- The due time of the call at log position `k`: the time then (`nowIn` before it) plus its delay. -/
def dueIn {M : Model} (log : List (HostCall M)) (k : Nat) : Nat :=
  match log.drop (log.length - 1 - k) with
  | e :: rest => nowIn rest + e.delay
  | [] => 0

/-- `clockElapsed`, reading only from the log's newest `nowIn` entry. -/
def clockElapsedIn {M : Model} (pick : List (HostCall M) → Option Nat) (log : List (HostCall M)) : M.Math :=
  M.ofNat (match pick log with
    | some j => max (nowIn log) (dueIn log j)
    | none => nowIn log)

/-- SuspendAgentUntil(_waiterList_, _timeoutTime_): ~unused~; the log keeps the suspension
(`pendingAt`), and AgentWoken and AgentTimeout read it. -/
def suspendUntil {M : Model} : List (Val M) → Run M (Val M)
  | [_, .math _] | [_, .posInf] => Run.pure (.enum Known.eUnused)
  | _ => Run.stop .sortError

/-- TimeNow by a reading of the log, the state as it was. -/
def readClock {M : Model} (read : List (HostCall M) → M.Num) : Run M (Val M) := fun s => .ok (.num (read s.hostLog)) s

/-- A logged call is no `next` at an elapsed time past `now`. -/
def HostCall.notAfter {M : Model} (now : M.Math) : HostCall M → Bool
  | .next _ t => !M.lt now t
  | _ => true

/-- The elapsed time `now` at which the host takes its next job `k` after the log `log`: no less than
each elapsed time logged, and where `k` is a timeout job's call, at least its _milliseconds_ past the
elapsed time logged before that call (§9.5.6). -/
def elapsedOk {M : Model} (log : List (HostCall M)) (k : Option Nat) (now : M.Math) : Bool :=
  log.all (·.notAfter now) &&
    match k with
    | some j => match log.drop (log.length - 1 - j) with
      | e :: rest => (e.timeoutMs.map (mathAfter (lastElapsed rest) now)).getD true
      | [] => true
    | none => true

/-- The next job of `m`, taken at the elapsed time `e`, where `elapsedOk` checks it; else the
implementation limit. -/
def checkElapsed {M : Model} (e : State M → M.Math) (m : Run M (Option Nat)) : Run M (Option Nat) := fun s =>
  match m s with
  | .ok k s' => if elapsedOk s.hostLog k (e s) then .ok k s' else .stop .implLimit
  | r => r

/-- The default clock's elapsed time as the host takes the job `pick` picks: the time, moved to at
least that job's due time. -/
def clockElapsed {M : Model} (pick : List (HostCall M) → Option Nat) (log : List (HostCall M)) : M.Math :=
  M.ofNat (match pick log with
    | some j => max (clockOf log).now (dueAt log j)
    | none => (clockOf log).now)

/-- The time in milliseconds SuspendAgentUntil's arguments wake at by the timeout, rounded up; none
where it never does (+∞, or past `maxTime`). -/
def wakeTime {M : Model} : List (Val M) → Option Nat
  | [_, .math t] => if M.lt (M.ofNat maxTime) t then none else some (ceilIn t 64 0 (maxTime + 1))
  | _ => none

/-- The agent `x`'s pending suspension in a log with agents: the wake time of its newest
SuspendAgentUntil where no WakeAgent of its signifier `sig` is newer; none where there is none. -/
def pendingIn {M : Model} (x sig : Val M) : List (HostCall M × Val M) → Option (Option Nat)
  | [] => none
  | (.choice q vs _, a) :: es =>
    if q == Known.pWakeAgent && vs.any (Val.same sig) then none
    else if q == Known.pSuspendAgentUntil && Val.same a x then some (wakeTime vs)
    else pendingIn x sig es
  | _ :: es => pendingIn x sig es

/-- The agent `x`'s pending suspension after the state's log, the surrounding agent running now. -/
def pendingAt {M : Model} (s : State M) (x : Val M) : Option (Option Nat) :=
  pendingIn x (sigOf s x) (withAgents s.agent s.hostLog)

/-- The job scheduled at log position `k` is the agent `x`'s (`ags`, `jobAgents`) and due by the clock `c`. -/
def readyFor {M : Model} (s : State M) (ags : Array (Val M)) (c : Clock) (x : Val M) (k : Nat) : Bool :=
  ags[k]?.any (Val.same (sigOf s x)) && c.due[k]?.getD 0 ≤ c.now

/-- The agent `x` has a job ready (`readyFor`) that the log scheduled and has not taken. -/
def hasReadyJob {M : Model} (s : State M) (x : Val M) : Bool :=
  let ags := jobAgents s
  let c := clockOf s.hostLog
  (s.hostLog.reverse.zipIdx).any fun (e, k) => e.schedulesJob && readyFor s ags c x k && !s.hostLog.any (·.takes k)

/-- The earliest due time of the agent `x`'s jobs that the log scheduled and has not taken. -/
def jobDue {M : Model} (s : State M) (x : Val M) : Option Nat :=
  let ags := jobAgents s
  let c := clockOf s.hostLog
  (s.hostLog.reverse.zipIdx).foldl (fun t (e, k) =>
    if e.schedulesJob && ags[k]?.any (Val.same (sigOf s x)) && !s.hostLog.any (·.takes k) then
      let d := c.due[k]?.getD 0
      some ((t.map (min d)).getD d)
    else t) none

/-- The agent `x` can run: it is not suspended, or the clock has reached its wake time, or it waits
for a message or a job (`idleWait`) and has a job ready (`hasReadyJob`). -/
def runnable {M : Model} (s : State M) (x : Val M) : Bool :=
  (match pendingAt s x with
  | none => true
  | some none => false
  | some (some t) => decide (t ≤ (clockOf s.hostLog).now)) || idleWait s x && hasReadyJob s x

/-- The jobs the host may take now: with one agent in the cluster every job; else the surrounding
agent's that are due (`readyFor`). -/
def jobReady {M : Model} (s : State M) : Nat → Bool :=
  if (clusterSigs s).length ≤ 1 then fun _ => true
  else
    let ags := jobAgents s
    let c := clockOf s.hostLog
    readyFor s ags c s.agent

/-- The agent `x` can be switched to: an Agent Record (`isAgent`) whose signifier is one of the
cluster's and not the surrounding agent's, that is not the surrounding agent and can run. -/
def switchable {M : Model} (isAgent : State M → Val M → Bool) (s : State M) (x : Val M) : Bool :=
  isAgent s x && (clusterSigs s).any (Val.same (sigOf s x)) && !Val.same (sigOf s x) (sigOf s s.agent) &&
    !Val.same x s.agent && runnable s x

/-- The agents of a log with agents that ran a SuspendAgentUntil. -/
def suspendedIn {M : Model} : List (HostCall M × Val M) → List (Val M)
  | [] => []
  | (.choice q _ _, a) :: es => if q == Known.pSuspendAgentUntil then a :: suspendedIn es else suspendedIn es
  | _ :: es => suspendedIn es

/-- The Agent Records that ran a SuspendAgentUntil in the state's log. -/
def suspendedAgents {M : Model} (s : State M) : List (Val M) := suspendedIn (withAgents s.agent s.hostLog)

/-- The earliest wake time by a timeout of the agents `xs` that are suspended. -/
def earliestWake {M : Model} (s : State M) (xs : List (Val M)) : Option Nat :=
  xs.foldl (fun m x => match pendingAt s x, m with
    | some (some t), some u => some (min t u)
    | some (some t), none => some t
    | _, m => m) none

/-- AgentWoken(): whether the surrounding agent can run. -/
def agentWoken {M : Model} : Run M (Val M) := fun s => .ok (.bool (runnable s s.agent)) s

/-- AgentTimeout(): the time now where the surrounding agent can run; else the earliest wake by a
timeout of the agents `xs`, not before now; blocked where none wakes so. -/
def agentTimeout {M : Model} (xs : State M → List (Val M)) : Run M (Val M) := fun s =>
  let now := (clockOf s.hostLog).now
  if runnable s s.agent then .ok (.math (M.ofNat now)) s
  else match earliestWake s (xs s) with
    | some t => .ok (.math (M.ofNat (max t now))) s
    | none => .stop .blocked

/-- The agents `l` after the first that is the surrounding agent `a`, then all of `l`. -/
def afterAgent {M : Model} (a : Val M) (l : List (Val M)) : List (Val M) :=
  (l.dropWhile (!Val.same · a)).drop 1 ++ l

/-- HostSelectAgent(_agent_, _n_), round-robin: the first of the agents `xs` after the surrounding
agent's signifier, wrapping around, that is `switchable`; ~empty~ where there is none. -/
def selectNext {M : Model} (isAgent : State M → Val M → Bool) (xs : State M → List (Val M)) :
    List (Val M) → Run M (Val M)
  | [_, .math _] => fun s =>
    match (afterAgent (sigOf s s.agent) (xs s)).find? (switchable isAgent s) with
    | some x => .ok x s
    | none => .ok (.enum Known.eEmpty) s
  | _ => Run.stop .sortError

/-! ChooseReadsBytesFrom: sequentially consistent reads, in the interleaving order of the log's switches. -/

/-- The latest of the placed events `es` that writes byte `loc` of `block`. -/
def lastWrite {M : Model} (isWrite : State M → Val M → Bool) (s : State M) (block : Val M) (loc : M.Math)
    (es : List (Val M × (Nat × Nat))) : Option (Val M × (Nat × Nat)) :=
  es.foldl (fun acc ep => if writesByte isWrite s block loc ep.1 then
      match acc with
      | some q => if placeLe q.2 ep.2 then some ep else acc
      | none => some ep
    else acc) none

/-- `f` at `idx` + `j` for each `j` from `j₀`, `n` of them; none where one is none. -/
def eachByte {M : Model} {α : Type} (f : M.Math → Option α) (idx : M.Math) (j₀ : Nat) : Nat → Option (List α)
  | 0 => some []
  | n + 1 => (f (M.add idx (M.ofNat j₀))).bind fun w => (eachByte f idx (j₀ + 1) n).map (w :: ·)

/-- ChooseReadsBytesFrom's _execution_, _block_, _byteIndex_ and _elementSize_. -/
def readArgs {M : Model} : List (Val M) → Option (Val M × Val M × M.Math × M.Math)
  | [ex, _, block, d, e] => match d, e with
    | .math idx, .math size => some (ex, block, idx, size)
    | _, _ => none
  | _ => none

/-- ChooseReadsBytesFrom(_execution_, _eventsRecord_, _block_, _byteIndex_, _elementSize_),
sequentially consistent: a new List of each byte's latest write event (`isWrite`) in the interleaving
order (`placedEvents`); residue where a byte has none. -/
def scWrites {M : Model} (isWrite : State M → Val M → Bool) (vs : List (Val M)) : Run M (Val M) := fun s =>
  match readArgs vs with
  | some (ex, block, idx, size) =>
    let n := ceilIn size 17 0 65536
    if M.eq (M.ofNat n) size then
      match eachByte (fun loc => (lastWrite isWrite s block loc (placedEvents s (cutsOf s.hostLog) ex)).map (·.1))
          idx 0 n with
      | some ws => listOf ws s
      | none => .stop .residue
    else .stop .sortError
  | none => .stop .sortError

/-- PropertyOrder in document order: a new List of the given List's elements. -/
def documentOrder {M : Model} : List (Val M) → Run M (Val M)
  | [_, l] => fun s => match listElems s l with
    | some xs => listOf xs s
    | none => .stop .sortError
  | _ => Run.stop .sortError

/-! ForInStep: EnumerateObjectProperties as a host strategy (`Ecma.ForIn`). -/

section ForIn

variable {M : Model}

/-- The same action, by the model's equalities (keys compared as Strings). -/
def ForInAct.same : ForInAct M → ForInAct M → Bool
  | .keys a, .keys b | .proto a, .proto b => M.addrEq a b
  | .own a (.str k), .own b (.str k') => M.addrEq a b && M.strEq k k'
  | .yield k, .yield k' => M.strEq k k'
  | .done, .done => true
  | _, _ => false

/-- `CfiOk`, decided. -/
def cfiCheck : CfiSt M → List (ForInEntry M) → Bool
  | _, [] => true
  | st, e :: es => e.act.same st.next && cfiCheck (st.step e) es

/-- CreateForInIterator's next action where every action so far was its, else [[OwnPropertyKeys]]
of _obj_. -/
def forInAct (obj : M.Addr) (es : List (ForInEntry M)) : ForInAct M :=
  if cfiCheck (CfiSt.init obj) es then cfiNext obj es else .keys obj

/-- ForInStep by `forInAct`, the history read by `hist`. -/
def forInChoiceBy (hist : State M → Val M → Option (List (ForInEntry M))) : List (Val M) → Run M (Val M)
  | [.obj obj, h] => fun s => match hist s h with
    | some es => actRecord (forInAct obj es) s
    | none => .stop .sortError
  | _ => Run.stop .sortError

/-- ForInStep by `forInAct`, the history read by `forInHist`. -/
def forInChoice : List (Val M) → Run M (Val M) := forInChoiceBy forInHist

end ForIn

/-! The locale-sensitive choices, answered as the forms without a locale. -/

/-- The mathematical values of the List a value refers to. -/
def mathsOf {M : Model} (s : State M) (v : Val M) : Option (List M.Math) :=
  (listElems s v).bind (·.mapM fun | .math x => some x | _ => none)

/-- LocaleUppercase or LocaleLowercase as the case mapping `f` (toUppercase or toLowercase): a new
List of the mapped code points. -/
def caseAsDefault {M : Model} (f : M.Seq M.Math → M.Seq M.Math) : List (Val M) → Run M (Val M)
  | [l] => fun s => match mathsOf s l with
    | some cs =>
      let ys := M.seqFoldl (fun acc x => acc ++ [x]) [] (f (cs.foldl M.seqPush M.seqNil))
      if ys.all Prims.Strings.isPoint then listOf (ys.map .math) s else .stop .sortError
    | none => .stop .sortError
  | _ => Run.stop .sortError

/-- Lexicographic order of Lists of naturals. -/
def natLexLt : List Nat → List Nat → Bool
  | [], _ :: _ => true
  | a :: as, b :: bs => a < b || (a == b && natLexLt as bs)
  | _, _ => false

/-- A String's key: `g` of its code points' canonical decomposition (NFD). -/
def nfdKey {M : Model} (g : M.Seq M.Math → List Nat) (a : M.Str) : List Nat :=
  g (M.normalize .NFD (Prims.Strings.strPoints a))

/-- LocaleCompare by the keys `nfdKey g`: -1𝔽, +0𝔽 or 1𝔽 as they order the two Strings. -/
def compareBy {M : Model} (g : M.Seq M.Math → List Nat) : List (Val M) → Run M (Val M)
  | [.str a, .str b] => Run.pure (.num (
      if natLexLt (nfdKey g a) (nfdKey g b) then M.numOf (M.neg (M.ofNat 1))
      else if natLexLt (nfdKey g b) (nfdKey g a) then M.numOf (M.ofNat 1)
      else M.numZero false))
  | _ => Run.stop .sortError

/-- LocaleDateString as the forms without a locale: ~empty~ for a Date, ~throw~ for any other value. -/
def dateAsDefault {M : Model} : List (Val M) → Run M (Val M)
  | [_, v] => fun s => .ok (.enum (if dateValued s v then Known.eEmpty else Known.eThrow)) s
  | _ => Run.stop .sortError

/-! NativeFunctionSource's text (Function.prototype.toString steps 3–4). -/

/-- The name of NativeFunctionSource's answer for _func_.[[InitialName]]'s code units: none where it
has no String, the name where the law admits it, else no answer. -/
def nativeNameOf : Option (List Nat) → Option (List Char)
  | none => some []
  | some us => let cs := us.map Char.ofNat; if nativeName cs then some cs else none

/-- NativeFunctionSource's answer for _func_.[[InitialName]]'s code units: `nativeWrap` of its name, residue
where the law admits none. -/
def nativeAnswer {M : Model} (us : Option (List Nat)) : Run M (Val M) :=
  match nativeNameOf us with
  | some cs => Run.pure (.str (M.strLit (nativeWrap cs)))
  | none => Run.stop .residue

/-- _func_.[[InitialName]], where it is a String. -/
def initialNameIn {M : Model} (s : State M) : Val M → Option M.Str
  | .obj a => match slotOf s a Known.fInitialName with
    | some (.str y) => some y
    | _ => none
  | _ => none

/-! SortStep's strategy: a stable binary insertion sort, its state handed back with each call. -/

/-- A comparator result's order for the sort: by sign, ±∞ by sign, zeros and *NaN* as =C. -/
def sortOrd {M : Model} (r : M.Num) : Ordering :=
  match M.numView r with
  | .finite m => if M.lt m (M.ofNat 0) then .lt else .gt
  | .posInf => .gt
  | .negInf => .lt
  | _ => .eq

/-- A binary insertion sort's state: the indices less than `x` in their order so far (`xs`), the index `x` it
inserts, and the positions of `xs` from `lo` to before `hi` where `x` may still go. -/
structure BinSort where
  xs : List Nat
  x : Nat
  lo : Nat
  hi : Nat

/-- The position whose element `x` is compared with: the middle of the range. -/
def BinSort.mid (b : BinSort) : Nat := (b.lo + b.hi) / 2

/-- The sort of `n` elements from `b`: where the range is not empty, the call on `x` and the element at its
middle; else `x` inserted at `lo`, then the search for the next index over all of `xs`, or after the last index
the order. -/
def BinSort.settle (n : Nat) (b : BinSort) : (Nat × Nat × BinSort) ⊕ List Nat :=
  if b.lo < b.hi then .inl (b.x, b.xs.getD b.mid 0, b)
  else
    let xs := b.xs.take b.lo ++ b.x :: b.xs.drop b.lo
    if b.x + 1 < n then
      let b' : BinSort := ⟨xs, b.x + 1, 0, xs.length⟩
      .inl (b'.x, xs.getD b'.mid 0, b')
    else .inr xs

/-- The sort of `n` elements at the start: the order of none or one, else the search for 1 over « 0 ». -/
def binStart (n : Nat) : (Nat × Nat × BinSort) ⊕ List Nat :=
  if n ≤ 1 then .inr (List.range n) else BinSort.settle n ⟨[0], 1, 0, 1⟩

/-- The sort of `n` elements after the call on `x` and the middle element ordered them `o`: `x` before the middle
element where it is less (<C), else after it. -/
def BinSort.step (n : Nat) (b : BinSort) (o : Ordering) : (Nat × Nat × BinSort) ⊕ List Nat :=
  BinSort.settle n (if o = .lt then { b with hi := b.mid } else { b with lo := b.mid + 1 })

/-- A state as a value without identity: « x, lo, hi, « xs » » held together (`Val.tuple`), no cell. -/
def BinSort.val {M : Model} (b : BinSort) : Val M :=
  .tuple [.math (M.ofNat b.x), .math (M.ofNat b.lo), .math (M.ofNat b.hi), .tuple (b.xs.map fun i => .math (M.ofNat i))]

/-- The naturals of mathematical values, read by `ix`. -/
def natsOf {M : Model} (ix : M.Math → Option Nat) : List (Val M) → Option (List Nat)
  | [] => some []
  | .math i :: vs => do return (← ix i) :: (← natsOf ix vs)
  | _ :: _ => none

/-- A state read back from its value (`BinSort.val`), indices read by `ix`. -/
def binOf {M : Model} (ix : M.Math → Option Nat) : Val M → Option BinSort
  | .tuple [.math x, .math lo, .math hi, .tuple xs] => do
    return ⟨← natsOf ix xs, ← ix x, ← ix lo, ← ix hi⟩
  | _ => none

/-- The sort's next step from SortStep's _state_ `st` and _result_ `res`: at ~empty~ the start, else the step from
the state by the result's sign (`sortOrd`). -/
def binNext {M : Model} (ix : M.Math → Option Nat) (n : Nat) (st res : Val M) :
    Option ((Nat × Nat × BinSort) ⊕ List Nat) :=
  if isEmptyV st then some (binStart n)
  else match binOf ix st, res with
    | some b, .num r => some (b.step n (sortOrd r))
    | _, _ => none

/-- SortStep's answer for a step of the sort: the call and the state as a value, or the order. -/
def sortAnswer {M : Model} : (Nat × Nat × BinSort) ⊕ List Nat → Run M (Val M)
  | .inl (j, k, b) => sortCall j k b.val
  | .inr σ => sortDone σ

/-- SortStep(_n_, _state_, _result_) by the stable binary insertion sort `binNext`, indices read by `ix`. -/
def sortStepBy {M : Model} (ix : M.Math → Option Nat) : List (Val M) → Run M (Val M)
  | [.math n, st, res] => match (ix n).bind fun n => binNext ix n st res with
    | some a => sortAnswer a
    | none => Run.stop .sortError
  | _ => Run.stop .sortError

end Ecma
