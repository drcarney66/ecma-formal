module

public import Engine.Host.Names
public import Engine.Model
public import Ecma.Host.Jobs
public import Engine.Host.Strategy

@[expose] public section

/-!
# The test host's `$262.agent` at Impl

test262's agent API (INTERPRETING.md): the host's own clauses, each answer a function of the
host-call log with the agent each call ran in (`withAgents`), and the built-in functions, AgentMain
and main's idle step as host algorithms. A new agent is an Agent Record of the surrounding agent's
cluster whose [[ParkedStack]] holds one execution context; AgentMain, its code, evaluates the source,
then takes the broadcasts addressed to it, suspended (~empty~ its waiter list) while there is none.
-/

namespace Engine.Host

open Ecma Engine

variable (N : Names)

/-- AgentBroadcast(sab, n): ~unused~; its log entry is the message. -/
def broadcastClause : ClauseId := 2000010
/-- AgentIdleAgent(): an agent of the cluster but the surrounding one waiting for a message, else ~empty~. -/
def idleAgentClause : ClauseId := 2000011
/-- AgentTakeMessage(): the surrounding agent's next message « sab, n, callback », else ~empty~. -/
def takeMessageClause : ClauseId := 2000012
/-- AgentAllTaken(): every agent of the cluster but the first has taken every message. -/
def allTakenClause : ClauseId := 2000013
/-- AgentReceive(callback): ~unused~; the surrounding agent's messages go to _callback_. -/
def receiveClause : ClauseId := 2000014
/-- AgentReport(string): ~unused~; its log entry is the report. -/
def reportClause : ClauseId := 2000015
/-- AgentTakeReport(): the oldest report not taken, else ~empty~. -/
def takeReportClause : ClauseId := 2000016
/-- AgentWakeTime(ms): the time _ms_ milliseconds from now, +∞ for +∞. -/
def wakeTimeClause : ClauseId := 2000017
/-- AgentIdleUntil(): now where another agent can run, else the earliest of another's wake and the surrounding
agent's next job's due time, else ~empty~. -/
def idleUntilClause : ClauseId := 2000018
/-- AgentJobDue(): the earliest due time of the surrounding agent's jobs not taken, else +∞. -/
def jobDueClause : ClauseId := 2000019
/-- AgentJobClause(k): the clause of the algorithm whose Abstract Closure is the job scheduled at log position _k_,
else ~empty~ (the job is not an argument: a hook call on a closure schedules it). -/
def jobClauseClause : ClauseId := 2000030

/-- One of the agent API's clauses. -/
def isAgentClause (k : ClauseId) : Bool := broadcastClause ≤ k && k ≤ jobDueClause || k == jobClauseClause

/-- The calls of the clause `c` in a log with agents (newest first): arguments, answer and agent. -/
def ownCalls (c : ClauseId) : List (HostCall Impl × Val Impl) → List (List (Val Impl) × Val Impl × Val Impl)
  | [] => []
  | (.hook k vs _ _ r, a) :: es => if k == c then (vs, r, a) :: ownCalls c es else ownCalls c es
  | _ :: es => ownCalls c es

/-- The calls of the clause `c` in the state's log. -/
def callsOf (c : ClauseId) (s : State Impl) : List (List (Val Impl) × Val Impl × Val Impl) :=
  ownCalls c (withAgents s.agent s.hostLog)

/-- The answers of `c` other than ~empty~. -/
def takenOf (cs : List (List (Val Impl) × Val Impl × Val Impl)) : Nat :=
  (cs.filter fun (_, r, _) => !isEmptyV r).length

/-- The answers of `c` other than ~empty~ in the agent `a`. -/
def takenBy (c : ClauseId) (s : State Impl) (a : Val Impl) : Nat :=
  takenOf ((callsOf c s).filter fun (_, _, b) => Val.same b a)

/-- The agent of signifier `x` waits for a message: its pending suspension's waiter list is ~empty~. -/
def idleIn (s : State Impl) (x : Val Impl) : Bool :=
  (pendingList x x (withAgents s.agent s.hostLog)).map isEmptyV == some true

/-- A Record (an Agent Record's signifier is the Record itself). -/
def isRef : Val Impl → Bool
  | .ref _ => true
  | _ => false

/-- A report's String, else ~empty~. -/
def reportOf : List (Val Impl) → Val Impl
  | [.str x] => .str x
  | _ => .enum Known.eEmpty

/-- The time `ms` milliseconds after `now`: `now` for a negative or *NaN* `ms`, +∞ for +∞. -/
def wakeAfter (now : Nat) (ms : Impl.Num) : Val Impl :=
  match Impl.numView ms with
  | .posInf => .posInf
  | .finite m => if Impl.lt m (Impl.ofNat 0) then .math (Impl.ofNat now) else .math (Impl.add (Impl.ofNat now) m)
  | _ => .math (Impl.ofNat now)

/-- AgentJobClause's answer for a scheduled job: the clause of its Abstract Closure, else ~empty~. -/
def jobClauseOf : Option (Val Impl) → Val Impl
  | some (.clo site _) => .math (Impl.ofNat site.alg.clause)
  | _ => .enum Known.eEmpty

/-- The answers of the agent API's clauses (the cluster's signifiers are its Agent Records). -/
def agentHook (k : ClauseId) (vs : List (Val Impl)) : Run Impl (Val Impl) :=
  let unused : Val Impl := .enum Known.eUnused
  let empty : Val Impl := .enum Known.eEmpty
  if k == broadcastClause then match vs with
    | [_, _] => Run.pure unused
    | _ => Run.stop .sortError
  else if k == idleAgentClause then match vs with
    | [] => fun s => .ok (((clusterSigs s).find? fun x => isRef x && !Val.same x (sigOf s s.agent) && idleIn s x).getD empty) s
    | _ => Run.stop .sortError
  else if k == takeMessageClause then match vs with
    | [] => fun s =>
      match (callsOf broadcastClause s).reverse[takenBy takeMessageClause s s.agent]? with
      | some (m, _, _) =>
        let cb := (((callsOf receiveClause s).find? fun (_, _, b) => Val.same b s.agent).bind
          fun (ws, _, _) => ws.head?).getD .undefined
        listOf [m.headD .undefined, (m.drop 1).headD .undefined, cb] s
      | none => .ok empty s
    | _ => Run.stop .sortError
  else if k == allTakenClause then match vs with
    | [] => fun s => let n := (callsOf broadcastClause s).length
      .ok (.bool (((clusterSigs s).drop 1).all fun x => n ≤ takenBy takeMessageClause s x)) s
    | _ => Run.stop .sortError
  else if k == receiveClause then match vs with
    | [_] => Run.pure unused
    | _ => Run.stop .sortError
  else if k == reportClause then match vs with
    | [.str _] => Run.pure unused
    | _ => Run.stop .sortError
  else if k == takeReportClause then match vs with
    | [] => fun s =>
      match (callsOf reportClause s).reverse[takenOf (callsOf takeReportClause s)]? with
      | some (r, _, _) => .ok (reportOf r) s
      | none => .ok empty s
    | _ => Run.stop .sortError
  else if k == wakeTimeClause then match vs with
    | [.num ms] => fun s => .ok (wakeAfter (clockOf s.hostLog).now ms) s
    | _ => Run.stop .sortError
  else if k == idleUntilClause then match vs with
    | [] => fun s =>
      let now := (clockOf s.hostLog).now
      let others := (clusterSigs s).filter (!Val.same · (sigOf s s.agent))
      if others.any (switchable (fun _ _ => true) s) then .ok (.math (Impl.ofNat now)) s
      else match (earliestWake s others).merge min (jobDue s s.agent) with
        | some t => .ok (.math (Impl.ofNat (max t now))) s
        | none => .ok empty s
    | _ => Run.stop .sortError
  else if k == jobDueClause then match vs with
    | [] => fun s => .ok ((jobDue s s.agent).elim .posInf fun t => .math (Impl.ofNat t)) s
    | _ => Run.stop .sortError
  else if k == jobClauseClause then match vs with
    | [.math j] => fun s => .ok (jobClauseOf ((Engine.Model.MathVal.idx j).bind (scheduled s.hostLog))) s
    | _ => Run.stop .sortError
  else Run.stop .residue

/-! The built-in functions and AgentMain, as host algorithms. -/

section Algs

/-- A step. -/
def st (s : Stmt) : Node := .mk [] s

/-- The algorithm of the clause with that sec-id. -/
def secCallee (sec : String) : Callee := .alg ⟨(N.clauseOf? sec).getD 0, 0⟩

/-- A call of the host's own clause `k`. -/
def ownCall (k : ClauseId) (args : List Expr) : Expr := .call (.alg ⟨k, 0⟩) args

/-- A call of a primitive. -/
def primCall (p : PrimId) (args : List Expr) : Expr := .call (.prim p) args

/-- `e` is ~empty~ (`neg`: is not). -/
def emptyC (neg : Bool) (e : Expr) : Cond := .preds e (.isVal neg .or [.enum Known.eEmpty]) []

/-- `Perform AgentInterleave().` -/
def interleaveStep : Node := st (.perform (.call (secCallee N "formal-agent-interleave") []))

/-- `Repeat, while AgentWoken() is false: Perform AgentInterleave().` -/
def wokenWait : Node :=
  st (.repeatWhile (.preds (primCall Known.pAgentWoken []) (.isVal false .or [.val .false]) []) [interleaveStep N])

/-- A built-in function's header with `n` parameters (slots 2 on). -/
def builtinHeader (n : Nat) : Header :=
  { kind := .builtin, params := (List.range n).map fun i => { x := 2 + i, ty := none, optional := false, rest := false },
    ret := none, recv := none, desc := [] }

/-- A built-in function's algorithm. -/
def builtinAlg (id : AlgId) (name : String) (n : Nat) (vars : Array String) (body : List Node) : Alg :=
  { id, name, header := builtinHeader n, vars := #["this value", "NewTarget"] ++ vars, attrs := [], indent := 0, body,
    closures := #[] }

def startAlg : AlgId := ⟨2000020, 0⟩
def broadcastAlg : AlgId := ⟨2000021, 0⟩
def getReportAlg : AlgId := ⟨2000022, 0⟩
def sleepAlg : AlgId := ⟨2000023, 0⟩
def monotonicNowAlg : AlgId := ⟨2000024, 0⟩
def receiveAlg : AlgId := ⟨2000025, 0⟩
def reportAlg : AlgId := ⟨2000026, 0⟩
def leavingAlg : AlgId := ⟨2000027, 0⟩
/-- Main's idle step (`idleBuiltin`): the host's `idle`. -/
def idleAlg : AlgId := ⟨2000028, 0⟩
/-- The global `setTimeout`. -/
def setTimeoutAlg : AlgId := ⟨2000029, 0⟩

/-- A field by name. -/
def fieldN (n : String) : FieldId := (N.field? n).getD 0

/-- A new Record of the sort of that name. -/
def recordE (sort : String) (fs : List (FieldId × Expr)) : Expr := .record .none (some ((N.sort? sort).getD Known.sRecord)) fs

def zeroE : Expr := .math .none (.num (.dec 0))

def idxE (e : Expr) (i : Nat) : Expr := .index e (.math .none (.num (.dec i)))

/-- AgentMain(source), the closure over slot 3 a new agent's execution context runs: InitializeHostDefinedRealm;
ParseScript(_source_, the current Realm Record, *undefined*), then ScriptEvaluation where it parses (the completion
ignored); then forever: its jobs (AgentNextJob() until ~empty~: AgentPrepareJob, the job's call, AgentCleanupJob,
ClearKeptObjects(), then as main's job loop an Assert that the call's completion is not abrupt, at the erratum of
the job's clause (`Names.jobErrata`, by AgentJobClause) in every mode); AgentTakeMessage(); for ~empty~,
SuspendAgentUntil(~empty~, AgentJobDue()) and the woken wait; else,
with a callback, a new SharedArrayBuffer of the message's Shared Data Block and length in this agent's realm
(AllocateSharedArrayBuffer's object), and Call(callback, *undefined*, « it, n ») (the completion ignored). -/
def agentMain : CloLit :=
  let m : Expr := .var 10
  let errors : Cond := .preds (.var 9) (.isTy true .or [.listOf "a" (.sort "" [] ((N.sort? "error").getD 0) "errors")]) []
  let sab : Expr := .var 11
  let normal : Cond := .preds (.var 14) (.isTy true .or [.sort "an" [] Known.sAbruptComp ""]) []
  let erratumAt : ClauseId × ErratumId → Node := fun (c, e) =>
    st (.if_ (.preds (ownCall jobClauseClause [.var 12]) (.isVal false .or [.math .none (.num (.dec c))]) [])
      (.inline (.assertAt (some e) normal)) [] none)
  { kind := .abstract, atomic := false, params := none, caps := [3, 6], body := [
    st (.perform (.bang (.call (secCallee N "sec-initializehostdefinedrealm") []))),
    st (.let_ 8 (primCall Known.pCurrentRealm [])),
    st (.let_ 15 (primCall Known.pRunning [])),
    st (.let_ 9 (.call (secCallee N "sec-parse-script") [.var 3, .var 8, .val .undefined])),
    st (.if_ errors (.inline (.perform (.call (secCallee N "sec-runtime-semantics-scriptevaluation") [.var 9]))) [] none),
    st (.remove (.var 15) 0),
    st (.repeat_ [
      st (.let_ 12 (primCall Known.pAgentNextJob [])),
      st (.repeatWhile (emptyC true (.var 12)) ([
        st (.remove (.var 6) 0),
        st (.let_ 13 (primCall Known.pAgentPrepareJob [.var 12])),
        st (.let_ 14 (.apply (.var 13) [])),
        st (.perform (primCall Known.pAgentCleanupJob [.var 12])),
        st (.push (.var 6) 0),
        st (.perform (.call (secCallee N "sec-clear-kept-objects") []))] ++ N.jobErrata.map erratumAt ++ [
        st (.assert normal),
        st (.set (.var 12) (primCall Known.pAgentNextJob []))])),
      st (.let_ 10 (ownCall takeMessageClause [])),
      st (.if_ (emptyC false m)
        (.block [st (.perform (primCall Known.pSuspendAgentUntil [.enum Known.eEmpty, ownCall jobDueClause []])),
          wokenWait N]) []
        (some (.mk [] none (.block [
          st (.if_ (.preds (idxE m 2) (.isVal true .or [.val .undefined]) []) (.block [
            st (.push (.var 15) 0),
            st (.let_ 11 (.bang (.call (secCallee N "sec-ordinarycreatefromconstructor")
              [.intrinsic (fieldN N "SharedArrayBuffer"), .val (.str "%SharedArrayBuffer.prototype%" ""),
               .list [.fieldName (fieldN N "ArrayBufferData"), .fieldName (fieldN N "ArrayBufferByteLength")]]))),
            st (.set (.field sab (fieldN N "ArrayBufferData")) (.field (idxE m 0) (fieldN N "ArrayBufferData"))),
            st (.set (.field sab (fieldN N "ArrayBufferByteLength")) (.field (idxE m 0) (fieldN N "ArrayBufferByteLength"))),
            st (.perform (.call (secCallee N "sec-call") [idxE m 2, .val .undefined, .list [sab, idxE m 1]])),
            st (.remove (.var 15) 0)]) [] none)]))))])] }

/-- `$262.agent.start(source)`: `? ToString(source)`; a new Agent Record of the surrounding agent's candidate
execution ([[CanBlock]] *true*, the host's choices as `newAgent`'s), its [[Signifier]] itself, its [[ParkedStack]]
« a new execution context whose code evaluation state is AgentMain »; a new Agent Events Record of it appended to
the candidate execution's [[EventsRecords]]; *undefined*. -/
def startBuiltin : Alg :=
  let f := fieldN N
  let ex : Expr := .var 4
  { builtinAlg startAlg "$262.agent.start" 1
      #["source", "src", "execution", "agent", "context", "status", "realm", "script", "message", "sab", "k", "job",
        "result", "realmCtx"] [
      st (.let_ 3 (.q (.call (secCallee N "sec-tostring") [.var 2]))),
      st (.let_ 4 (.field (primCall Known.pAgentRecord []) Known.fCandidateExecution)),
      st (.let_ 5 (recordE N "Agent Record" [(f "LittleEndian", .val .true), (f "CanBlock", .val .true),
        (f "IsLockFree1", .val .true), (f "IsLockFree2", .val .true), (f "IsLockFree8", .val .true),
        (f "KeptAlive", .list []), (f "ModuleAsyncEvaluationCount", zeroE), (f "GlobalSymbolRegistry", .list []),
        (Known.fCandidateExecution, ex)])),
      st (.set (.field (.var 5) Known.fSignifier) (.var 5)),
      st (.let_ 6 (recordE N "execution context" [])),
      st (.setCodeState (.var 6) (.closure 0)),
      st (.set (.field (.var 5) Known.fParkedStack) (.list [.var 6])),
      st (.perform (primCall Known.pAppend [recordE N "Agent Events Record" [(Known.fAgentSignifier, .var 5),
        (f "EventList", .list []), (f "AgentSynchronizesWith", .list [])], .field ex Known.fEventsRecords])),
      st (.ret (some (.val .undefined)))] with closures := #[agentMain N] }

/-- `$262.agent.broadcast(sab, n)`: `? RequireInternalSlot(sab, [[ArrayBufferData]])`, a *TypeError* for an
ArrayBuffer; AgentBroadcast(sab, n); WakeAgent of each agent waiting for a message; AgentInterleave until every
agent has taken it; *undefined*. -/
def broadcastBuiltin : Alg :=
  builtinAlg broadcastAlg "$262.agent.broadcast" 2 #["sab", "n", "idle"] [
    st (.perform (.q (.call (secCallee N "sec-requireinternalslot") [.var 2, .fieldName (fieldN N "ArrayBufferData")]))),
    st (.if_ (.preds (.call (secCallee N "sec-issharedarraybuffer") [.var 2]) (.isVal false .or [.val .false]) [])
      (.inline (.throwErr (fieldN N "TypeError"))) [] none),
    st (.perform (ownCall broadcastClause [.var 2, .var 3])),
    st (.let_ 4 (ownCall idleAgentClause [])),
    st (.repeatWhile (emptyC true (.var 4)) [st (.perform (primCall Known.pWakeAgent [.var 4])),
      st (.set (.var 4) (ownCall idleAgentClause []))]),
    st (.repeatWhile (.preds (ownCall allTakenClause []) (.isVal false .or [.val .false]) []) [interleaveStep N]),
    st (.ret (some (.val .undefined)))]

/-- `$262.agent.getReport()`: AgentInterleave; the oldest report not taken, else *null*. -/
def getReportBuiltin : Alg :=
  builtinAlg getReportAlg "$262.agent.getReport" 0 #["report"] [interleaveStep N,
    st (.let_ 2 (ownCall takeReportClause [])),
    st (.if_ (emptyC false (.var 2)) (.inline (.ret (some (.val .null)))) [] none),
    st (.ret (some (.var 2)))]

/-- `$262.agent.sleep(ms)`: SuspendAgentUntil(*undefined*, AgentWakeTime(`? ToNumber(ms)`)) and the woken wait;
*undefined*. -/
def sleepBuiltin : Alg :=
  builtinAlg sleepAlg "$262.agent.sleep" 1 #["ms", "t"] [
    st (.let_ 3 (ownCall wakeTimeClause [.q (.call (secCallee N "sec-tonumber") [.var 2])])),
    st (.perform (primCall Known.pSuspendAgentUntil [.val .undefined, .var 3])),
    wokenWait N,
    st (.ret (some (.val .undefined)))]

/-- `$262.agent.monotonicNow()`: TimeNow(). -/
def monotonicNowBuiltin : Alg :=
  builtinAlg monotonicNowAlg "$262.agent.monotonicNow" 0 #[] [st (.ret (some (primCall Known.pTimeNow [])))]

/-- `$262.agent.receiveBroadcast(callback)`: AgentReceive(callback); *undefined*. -/
def receiveBuiltin : Alg :=
  builtinAlg receiveAlg "$262.agent.receiveBroadcast" 1 #["callback"] [
    st (.perform (ownCall receiveClause [.var 2])), st (.ret (some (.val .undefined)))]

/-- `$262.agent.report(message)`: AgentReport(`? ToString(message)`); *undefined*. -/
def reportBuiltin : Alg :=
  builtinAlg reportAlg "$262.agent.report" 1 #["message", "string"] [
    st (.let_ 3 (.q (.call (secCallee N "sec-tostring") [.var 2]))),
    st (.perform (ownCall reportClause [.var 3])), st (.ret (some (.val .undefined)))]

/-- `$262.agent.leaving()`: *undefined*. -/
def leavingBuiltin : Alg :=
  builtinAlg leavingAlg "$262.agent.leaving" 0 #[] [st (.ret (some (.val .undefined)))]

/-- Main's idle step: ~empty~ where AgentIdleUntil() is ~empty~; else SuspendAgentUntil(*undefined*, it),
AgentInterleave and the woken wait; ~unused~. -/
def idleBuiltin : Alg :=
  { id := idleAlg, name := "HostIdle", header := { kind := .ao, params := [], ret := none, recv := none, desc := [] },
    vars := #["t"], attrs := [], indent := 0, closures := #[], body := [
    st (.let_ 0 (ownCall idleUntilClause [])),
    st (.if_ (emptyC false (.var 0)) (.inline (.ret (some (.enum Known.eEmpty)))) [] none),
    st (.perform (primCall Known.pSuspendAgentUntil [.val .undefined, .var 0])),
    interleaveStep N, wokenWait N,
    st (.ret (some (.enum Known.eUnused)))] }

/-- `setTimeout(callback, delay)`: `? ToIntegerOrInfinity(delay)`, 0 where it is infinite or negative; a Job
Abstract Closure that performs `? Call(callback, *undefined*)`; HostEnqueueTimeoutJob(it, the current Realm
Record, 𝔽(the delay)); *undefined*. -/
def setTimeoutBuiltin : Alg :=
  let ms : Expr := .var 4
  { builtinAlg setTimeoutAlg "setTimeout" 2 #["callback", "delay", "ms", "job"] [
      st (.let_ 4 (.q (.call (secCallee N "sec-tointegerorinfinity") [.var 3]))),
      st (.if_ (.preds ms (.isVal false .or [.math .plus .inf, .math .minus .inf]) [])
        (.inline (.set (.var 4) zeroE)) [] none),
      st (.set (.var 4) (primCall Known.pMax [ms, zeroE])),
      st (.let_ 5 (.closure 0)),
      st (.perform (.call (secCallee N "sec-hostenqueuetimeoutjob") [.var 5, primCall Known.pCurrentRealm [],
        primCall Known.pF [ms]])),
      st (.ret (some (.val .undefined)))] with
    closures := #[{ kind := .abstract, atomic := false, params := none, caps := [2], body := [
      st (.perform (.q (.call (secCallee N "sec-call") [.var 2, .val .undefined, .list []]))),
      st (.ret (some (.enum Known.eUnused)))] }] }

/-- The agent API's algorithms and `setTimeout`. -/
def agentBuiltins : List Alg :=
  [startBuiltin N, broadcastBuiltin N, getReportBuiltin N, sleepBuiltin N, monotonicNowBuiltin, receiveBuiltin,
    reportBuiltin N, leavingBuiltin, idleBuiltin N, setTimeoutBuiltin N]

/-- `$262.agent`'s members on main (the cluster's first agent): behaviour, name and length. -/
def mainMembers : List (AlgId × String × Nat) :=
  [(startAlg, "start", 1), (broadcastAlg, "broadcast", 2), (getReportAlg, "getReport", 0), (sleepAlg, "sleep", 1),
    (monotonicNowAlg, "monotonicNow", 0)]

/-- `$262.agent`'s members on another agent. -/
def agentMembers : List (AlgId × String × Nat) :=
  [(receiveAlg, "receiveBroadcast", 1), (reportAlg, "report", 1), (leavingAlg, "leaving", 0), (sleepAlg, "sleep", 1),
    (monotonicNowAlg, "monotonicNow", 0)]

end Algs

end Engine.Host
