module

public import Engine.Host.Core

@[expose] public section

/-!
# The host's test options

`hostBy N o c` is `host N c` with ecma-run's test-host options. A seed (`--host-seed N`) answers the
choices the host laws leave open by a pseudo-random word keyed on N and the host-call log's length:
of two values that round to one Number either, the time (non-decreasing, at least a taken timeout
job's due time), CanAllocate (an allocation
may fail), Math.random (`seededRandom` at the seed; without one, at `defaultSeed`), and the next job among those §9.5 lets the host order (promise jobs first in
first out). `resizeInPlace` (`--resize-in-place`) makes HostResizeArrayBuffer resize the Data Block
in place and answer ~handled~ (§25.1.3.8). `canBlock` (`--can-block`) makes the surrounding agent one
that can block ([[CanBlock]] *true*, §9.7; the cells' `init` reads it). `webBrowser` (`--web-browser`) makes the host a web
browser: its WebBrowser choice answers true for every feature (§B); `annexB` (`--annex-b SEC`) makes it a
host that otherwise supports the clauses named, whose "web browser or otherwise supports" choice answers
true for them; one that supports §B.3.6 gives `$262` its *"IsHTMLDDA"* (`ddaBy`). A seeded or resized
answer whose law does not check is the fixed host's; the host laws hold for every option
set (`wfBy`). `hostIn σ o` takes its open decisions from the inputs `σ`: the schedule
and the reads by index into their legal answers (0 the round-robin agent and each byte's latest write)
and, with a seed, the seeded choices; `hostBy o` is `hostIn (σOf o) o`.
-/

namespace Engine.Host

open Ecma Engine

variable (N : Names)

/-- The test-host options. -/
structure HostOpts where
  seed : Option Nat := none
  resizeInPlace : Bool := false
  /-- The surrounding agent's [[CanBlock]] (`init`), not a choice of `hostBy`. -/
  canBlock : Bool := false
  webBrowser : Bool := false
  /-- the sec-ids of the Annex B clauses the host otherwise supports -/
  annexB : List String := []
  deriving BEq, Repr

/-- The Annex B clauses whose feature a host may otherwise support (`annexB`). -/
def annexBClauses : List String :=
  ["sec-html-like-comments", "sec-regular-expressions-patterns", "sec-labelled-function-declarations",
    "sec-block-level-function-declarations-web-legacy-compatibility-semantics",
    "sec-functiondeclarations-in-ifstatement-statement-clauses", "sec-variablestatements-in-catch-blocks",
    "sec-initializers-in-forin-statement-heads", "sec-IsHTMLDDA-internal-slot",
    "sec-runtime-errors-for-function-call-assignment-targets"]

/-- `draw`'s key for the next job. -/
def jobKey : Nat := 1000001

/-- The seeded time in milliseconds at host-log length `n`: a start below 2^41, then 1000 a log entry
plus less than 1000, at most `maxTime`. -/
def timeAt (N n : Nat) : Nat :=
  min maxTime (draw N 0 0 % 2 ^ 41 + 1000 * n + draw N Known.pTimeNow n % 1000)

/-- The seeded time in milliseconds after a log: `timeAt` of its length plus the default clock's time,
which a taken timeout job moves to at least its due time; at most `maxTime`. -/
def seededTime (N : Nat) (log : List (HostCall Impl)) : Nat := min maxTime (timeAt N log.length + (clockOf log).now)

/-- The seeded reading: `seededTime` as a Number, else the default clock's. -/
def seededNum (N : Nat) (log : List (HostCall Impl)) : Impl.Num :=
  let t := Impl.numOf (Impl.ofNat (seededTime N log))
  if instantB t then t else clockNum log

/-- The seeded choices: of two values that round to one Number or of two Strings either, the time `seededNum`, an
allocation of at most 2^32 bytes failing one time in eight; else `choice`. -/
def seededChoice (n : Nat) (p : PrimId) (vs : List (Val Impl)) : Run Impl (Val Impl) := fun s =>
  let r := draw n p s.hostLog.length
  if p == Known.pHostChoice then match vs with
    | [.math a, .math b] =>
      if Engine.Model.MathVal.toNum a == Engine.Model.MathVal.toNum b then .ok (.math (if r % 2 == 0 then a else b)) s
      else .stop .residue
    | [.str a, .str b] => .ok (.str (if r % 2 == 0 then a else b)) s
    | _ => .stop .residue
  else if p == Known.pTimeNow then readClock (seededNum n) s
  else if p == Known.pCanAllocate then match vs with
    | [.math n, .bool _] => .ok (.bool (!Impl.lt (Impl.ofNat 4294967296) n && r % 8 != 0)) s
    | _ => .stop .sortError
  else choice N p vs s

/-- The jobs the seeded host may run next of those it may take (`own`): the first free promise job, the
free generic jobs and the free timeout jobs. -/
def nextJobs (own : Nat → Bool) (log : List (HostCall Impl)) : List Nat :=
  let ks := List.range log.length
  (ks.find? (free N log own [promiseJob])).toList ++ ks.filter (free N log own [genericJob]) ++
    ks.filter (free N log own [timeoutJob])

/-- The seeded next job: one of `nextJobs` whose call's due time is in the time value range from
`timeAt` at that call; one past it is never taken, the clock having no time value for it. -/
def seededPick (n : Nat) (own : Nat → Bool) (log : List (HostCall Impl)) : Option Nat :=
  let cs := (nextJobs N own log).filter fun k => timeAt n k + dueAt log k ≤ maxTime
  cs[draw n jobKey log.length % cs.length]?

/-- The seeded next job, `seededPick`'s of those ready (`jobReady`). -/
def seededNextJob (n : Nat) : Run Impl (Option Nat) := fun s => .ok (seededPick N n (jobReady s) s.hostLog) s

/-- A Data Block's bytes resized to `k`: its first `k` bytes, then zeros. -/
def resized (xs : List (Val Impl)) (k : Nat) : List (Val Impl) :=
  xs.take k ++ List.replicate (k - xs.length) (.math (Impl.ofNat 0))

/-- HostResizeArrayBuffer's requirements hold from `s` to `s'` for the buffer at `a` and the length `n`. -/
def resizeOk (s s' : State Impl) (a : Nat) (n : Impl.Math) : Bool :=
  (N.fieldsNamed "ArrayBufferData").all (fun f => match slotOf s a f, slotOf s' a f with
    | some .null, _ => true
    | _, some .null => false
    | _, _ => true) &&
  (N.fieldsNamed "ArrayBufferByteLength").all fun f => match slotOf s' a f with
    | some (.math m) => Impl.eq m n
    | _ => false

/-- `rebuild`'s step: `sl`'s field `e.1`, if it has one, put into `m`. -/
def putFrom (sl m : Model.WMap FieldId (Val Impl)) (e : FieldId × Nat) : Model.WMap FieldId (Val Impl) :=
  match sl.get e.1 with
  | some v => m.put e.1 v
  | none => m

/-- `sl`'s fields put into an empty Record in its index's order. -/
def rebuild (sl : Model.WMap FieldId (Val Impl)) : Model.WMap FieldId (Val Impl) :=
  sl.index.toList.foldl (putFrom sl) Model.WMap.empty

/-- HostResizeArrayBuffer(_buffer_, _newByteLength_) in place: the state where the Data Block keeps
its bytes up to the new length, those past the old one 0, and [[ArrayBufferByteLength]] is
_newByteLength_ in _buffer_'s slots (`rebuild`); none where _buffer_ has no Data Block. -/
def resizeCand (vs : List (Val Impl)) (s : State Impl) : Option (State Impl) :=
  match vs with
  | [.obj a, .math (.int i)] =>
    match Impl.heapGet s.heap a with
    | some (.object sl ps) =>
      match (N.fieldsNamed "ArrayBufferData").head?.bind (Impl.recGet sl ·) with
      | some (.ref d) => match Impl.heapGet s.heap d with
        | some (.block bs) =>
          let bytes := Engine.Model.bytesResize bs i.toNat
          let sl := (N.fieldsNamed "ArrayBufferByteLength").foldl (fun sl f => Impl.recSet sl f (.math (.int i)))
            (rebuild sl)
          some { s with heap := Impl.heapSet (Impl.heapSet s.heap d (.block bytes)) a (.object sl ps) }
        | _ => none
      | _ => none
    | _ => none
  | _ => none

/-- HostResizeArrayBuffer resizing in place (`resizeCand`): ~handled~ where `resizeOk` checks, else
~unhandled~ and the state as it was. -/
def resizeInPlace (vs : List (Val Impl)) : Run Impl (Val Impl) := fun s =>
  match vs, resizeCand N vs s with
  | [.obj a, .math n], some s' => if resizeOk N s s' a n then normalEnum N "handled" s' else normalEnum N "unhandled" s
  | _, _ => normalEnum N "unhandled" s

def resizeClause : String := "sec-hostresizearraybuffer"
def randomClause : String := "sec-math.random"

def hookBy (o : HostOpts) (c : Cells) (k : ClauseId) (vs : List (Val Impl)) : Run Impl (Val Impl) :=
  if o.resizeInPlace && N.clause k == some resizeClause then resizeInPlace N vs
  else match o.seed with
    | some n => if N.clause k == some randomClause then seededRandom n else hook N c k vs
    | none => hook N c k vs

/-- WebBrowser's answer with the options `o`: `o.webBrowser`, or for "or otherwise supports _c_", whether
_c_'s sec-id is in `o.annexB`. -/
def browserBy (o : HostOpts) : List (Val Impl) → Bool
  | [.choice 0, .clause c] => o.webBrowser || (N.clause c).any o.annexB.contains
  | _ => o.webBrowser

/-- §B.3.6's sec-id. -/
def ddaClause : String := "sec-IsHTMLDDA-internal-slot"

/-- The [[IsHTMLDDA]] field where the host with the options `o` is a web browser or otherwise supports §B.3.6. -/
def ddaBy (o : HostOpts) : Option FieldId :=
  if o.webBrowser || o.annexB.contains ddaClause then N.field? "IsHTMLDDA" else none

/-- The choices with the options `o`: WebBrowser `browserBy`, HostGlobalProperties with `ddaBy`'s
*"IsHTMLDDA"*, the others seeded or the fixed host's. -/
def choiceBy (o : HostOpts) (p : PrimId) : List (Val Impl) → Run Impl (Val Impl) :=
  if p == Known.pWebBrowser then fun vs => Run.pure (.bool (browserBy N o vs))
  else if p == Known.pHostGlobalProperties then globalProps (ddaBy N o)
  else match o.seed with
    | some n => seededChoice N n p
    | none => choice N p

def nextJobBy (o : HostOpts) : Run Impl (Option Nat) :=
  match o.seed with
  | some n => seededNextJob N n
  | none => nextJob N

/-- The elapsed time with the options `o`: the default clock's as the host takes its next job. -/
def elapsedBy (o : HostOpts) (s : State Impl) : Impl.Math :=
  match o.seed with
  | some n => clockElapsed (seededPick N n (jobReady s)) s.hostLog
  | none => elapsed N s

/-- The host with the options `o`. -/
def hostBy (o : HostOpts) (c : Cells) : Host Impl :=
  { hook := hookBy N o c, choice := agentJobs N c (nextJobBy N o) (choiceBy N o),
    nextJob := checkElapsed (elapsedBy N o) (nextJobBy N o), owns := jobReady, elapsed := elapsedBy N o, prepareJob := prepareJob N c, cleanupJob,
    clearsKept,
    idle := do
      if (clusterSigs (← Run.get)).length ≤ 1 then return none
      match (← readList c.realm).headD .null with
      | .null => pure ()
      | r => pushCtx N r .null
      return some idleAlg
    -- The program the driver left in the realm's cell (`Program.program`): the realm, the kind, whether an abrupt
    -- completion ends the agent's Jobs, the module's key, and the source text's code points.
    first := do
      match ← readList c.realm with
      | realm :: .math kind :: .bool stop :: key :: cps =>
        writeElems c.realm [realm, .bool stop]
        match realm with
        | .null => pure ()
        | r => pushCtx N r .null
        let text ← listOf cps
        match Model.MathVal.idx kind with
        | some 0 => return some (runScriptAlg, [text, realm])
        | some 1 => return some (runModuleAlg, [text, realm, key])
        | some 2 => return some (parseScriptAlg, [text, realm])
        | some 3 => return some (parseModuleAlg, [text, realm])
        | _ => Run.stop .sortError
      | _ => return none
    -- After the program, its completion is left in the cell; after an idle step, ~empty~ ends the Jobs.
    idleEnd := fun v => do
      cleanupJob 0
      match ← readList c.realm with
      | [realm, .bool stop] =>
        writeElems c.realm [realm, .bool stop, v]
        return if abrupt v && stop then none else some true
      | _ =>
        let empty := match v with
          | .enum e => e == Known.eEmpty
          | .comp t (.enum e) _ => t == Known.eNormal && e == Known.eEmpty
          | _ => false
        return if empty then none else some false }

/-! The host over its inputs `σ` (`hostIn`): `hostBy o` is the instance at `σOf o` . -/

end Engine.Host
