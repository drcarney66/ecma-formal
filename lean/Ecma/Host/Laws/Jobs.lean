module

public import Ecma.Host.Laws.Basic

@[expose] public section

/-!
# The laws of jobs and agents

Which job the host takes next, its preparation and cleanup, the job callbacks, and which agent runs
(sec-jobs, sec-agents, sec-forward-progress). A job is named by the log position of the call that scheduled it.
The host takes jobs through two interfaces, `Host.nextJob`/`prepareJob`/`cleanupJob` for the surrounding agent
and the choices AgentNextJob, AgentPrepareJob and AgentCleanupJob for an agent of a cluster; one set of
requirements (`Host.mayRun`, `promisePrepared`) governs both.
-/

namespace Ecma

/-- Whether SuspendAgentUntil's timeout wakes within `maxTime`. -/
def wakeFinite {M : Model} : List (Val M) → Bool
  | [_, .math t] => !M.lt (M.ofNat maxTime) t
  | _ => false

/-- The agent `x`'s pending suspension in a log with agents: whether its wake time is finite (`wakeFinite`),
or `none` if it is not suspended or a newer WakeAgent woke its signifier `sig`. -/
def pendingFinite {M : Model} (x sig : Val M) : List (HostCall M × Val M) → Option Bool
  | [] => none
  | (.choice q vs _, a) :: es =>
    if q == Known.pWakeAgent && vs.any (Val.same sig) then none
    else if q == Known.pSuspendAgentUntil && Val.same a x then some (wakeFinite vs)
    else pendingFinite x sig es
  | _ :: es => pendingFinite x sig es

/-- Whether the agent `x` has a job scheduled in the log that has not been taken. -/
def hasScheduledJob {M : Model} (s : State M) (x : Val M) : Bool :=
  let ags := jobAgents s
  (s.hostLog.reverse.zipIdx).any fun (e, k) =>
    e.schedulesJob && ags[k]?.any (Val.same (sigOf s x)) && !s.hostLog.any (·.takes k)

/-- Whether the agent `x` can run: it is not suspended with an infinite timeout, or it waits for a
message or a job (`idleWait`) and has a scheduled job (`hasScheduledJob`). -/
def canRunAgent {M : Model} (s : State M) (x : Val M) : Bool :=
  (pendingFinite x (sigOf s x) (withAgents s.agent s.hostLog)).getD true ||
    idleWait s x && hasScheduledJob s x

variable {M : Model}

/-- A logged call is one of the host-defined operation with that sec-id. -/
def HostCall.callOf (sec : String) : HostCall M → Bool
  | .hook c _ _ _ _ => Gen.clauses[c]? == some sec
  | _ => false

/-- The call at log position `k` (counted from the first) is one of the host-defined operation `sec`. -/
def calledAt (log : List (HostCall M)) (sec : String) (k : Nat) : Prop :=
  log.reverse[k]?.any (·.callOf sec) = true

/-- The job scheduled at log position `k` has been taken to run. -/
def taken (log : List (HostCall M)) (k : Nat) : Prop := log.any (·.takes k) = true

/-- The host-defined operations that schedule a Job (sec-hostenqueuegenericjob, sec-hostenqueuepromisejob,
sec-hostenqueuetimeoutjob, sec-host-cleanup-finalization-registry). -/
def jobHooks : List String :=
  ["sec-hostenqueuegenericjob", "sec-hostenqueuepromisejob", "sec-hostenqueuetimeoutjob",
    "sec-host-cleanup-finalization-registry"]

/-- The job scheduled at log position `k` may be taken now: a HostEnqueue…Job call scheduled it, it has not
been taken, the host may take it (`Host.owns`), and a promise job only after every earlier-scheduled promise
job the host may take. -/
def Host.mayRun (H : Host M) (s : State M) (k : Nat) : Prop :=
  (∃ sec ∈ jobHooks, calledAt s.hostLog sec k) ∧ ¬taken s.hostLog k ∧ H.owns s k = true ∧
    (calledAt s.hostLog "sec-hostenqueuepromisejob" k →
      ∀ i < k, calledAt s.hostLog "sec-hostenqueuepromisejob" i → H.owns s i = true → taken s.hostLog i)

/-- An execution is prepared to evaluate ECMAScript code (sec-jobs): the execution context stack is not
empty, and the Realm component of its topmost execution context is a Realm Record. -/
def preparedToEvaluate (s : State M) : Prop :=
  M.eq (M.seqLen s.stack) (M.ofNat 0) = false ∧
    ∃ pre top r, stackList s = pre ++ [top] ∧ fieldOf s Known.fRealm top = some r ∧
      isRecordOf s "Realm Record" r = true

/-- `sm` is the active script or module (sec-jobs): GetActiveScriptOrModule() is `sm`, and if `sm` is a
Script Record or Module Record, the Realm component of the topmost execution context whose ScriptOrModule
component is `sm` is `sm`.[[Realm]]. -/
def activeIs (s : State M) (sm : Val M) : Prop :=
  activeScriptOrModule s = sm ∧
    (isRecordOf s "Script Record" sm = true ∨ isRecordOf s "Module Record" sm = true →
      ∃ pre ec post, stackList s = pre ++ ec :: post ∧ fieldOf s Known.fScriptOrModule ec = some sm ∧
        (∀ c ∈ post, fieldOf s Known.fScriptOrModule c ≠ some sm) ∧
        ∃ r, fieldOf s Known.fRealm ec = some r ∧ fieldOf s Known.fRealm sm = some r)

/-- After the preparation of the job scheduled at log position `k`, from `s` to `s'`: where a
HostEnqueuePromiseJob call whose _realm_ is not *null* scheduled it, execution is prepared to evaluate
ECMAScript code, and the script or module active at that call is active. -/
def promisePrepared (s : State M) (k : Nat) (s' : State M) : Prop :=
  ∀ c job realm xs sm rl r, s.hostLog.reverse[k]? = some (.hook c (job :: realm :: xs) sm rl r) →
    Gen.clauses[c]? = some "sec-hostenqueuepromisejob" → realm ≠ .null → preparedToEvaluate s' ∧ activeIs s' sm

/-- The laws of jobs and agents. -/
structure Host.JobLaws (H : Host M) : Prop where
  /-- sec-jobs, the requirements' first item:
  "At some future point in time, when there is no running context in the agent for which the job is scheduled and that agent's execution context stack is empty, the implementation must: … Invoke the Job Abstract Closure."
  sec-hostenqueuepromisejob: "Jobs must run in the same order as the HostEnqueuePromiseJob invocations that scheduled them."
  Reading: the job the host takes next is one it may take now (`Host.mayRun`), each taken once. -/
  nextJob : ∀ s k s', H.nextJob s = .ok (some k) s' → H.mayRun s k
  /-- sec-jobs, the requirements' first item, in an agent of a cluster:
  "At some future point in time, when there is no running context in the agent for which the job is scheduled and that agent's execution context stack is empty, the implementation must: … Invoke the Job Abstract Closure."
  Reading: AgentNextJob answers ~empty~ or a job it may take now (`Host.mayRun`), the state as it was. -/
  agentNextJob : H.asks Known.pAgentNextJob fun _ s r =>
    r = .enum Known.eEmpty ∨ ∃ k, r = .math (M.ofNat k) ∧ H.mayRun s k
  /-- sec-jobs, the requirements' first item:
  "in the agent for which the job is scheduled"
  Reading: with more than one agent in the cluster, a job the host may take is the surrounding agent's. -/
  ownsAgent : ∀ s k, H.owns s k = true → (clusterSigs s).length ≤ 1 ∨
    (jobAgents s)[k]?.any (Val.same (sigOf s s.agent)) = true
  /-- sec-jobs, the requirements' first item:
  "At some future point in time, when there is no running context in the agent for which the job is scheduled and that agent's execution context stack is empty, the implementation must:"
  Reading: with one agent in the cluster, the host may take every scheduled job, so that none is left when its
  Jobs are done (`drained`). -/
  ownsSingle : ∀ s k, (clusterSigs s).length ≤ 1 → (∃ sec ∈ jobHooks, calledAt s.hostLog sec k) →
    H.owns s k = true
  /-- sec-hostenqueuepromisejob, the requirements:
  "If realm is not null, each time job is invoked the implementation must perform implementation-defined steps such that execution is prepared to evaluate ECMAScript code at the time of job's invocation."
  "If realm is not null, each time job is invoked the implementation must perform implementation-defined steps such that scriptOrModule is the active script or module at the time of job's invocation."
  Reading: the host's preparation of a promise job whose _realm_ is not *null* does both (`promisePrepared`). -/
  promiseJobPrepared : ∀ s k s', H.prepareJob k s = .ok () s' → promisePrepared s k s'
  /-- sec-jobs, the requirements' first item, in an agent of a cluster:
  "Perform any host-defined preparation steps. Invoke the Job Abstract Closure."
  sec-hostenqueuepromisejob: "each time job is invoked the implementation must perform implementation-defined steps such that execution is prepared to evaluate ECMAScript code at the time of job's invocation"
  Reading: AgentPrepareJob(_k_) answers the job scheduled at _k_, prepared as `promisePrepared` says. -/
  agentPrepareJob : ∀ vs s r s', H.choice Known.pAgentPrepareJob vs s = .ok r s' →
    ∃ k, vs = [.math (M.ofNat k)] ∧ scheduled s.hostLog k = some r ∧ promisePrepared s k s'
  /-- sec-jobs, the requirements' first item:
  "Perform any host-defined cleanup steps, after which the execution context stack must be empty."
  Reading: after a job's cleanup the execution context stack is empty. -/
  jobCleanup : ∀ k s s', H.cleanupJob k s = .ok () s' → M.eq (M.seqLen s'.stack) (M.ofNat 0) = true
  /-- sec-jobs, the requirements' first item, in an agent of a cluster:
  "Perform any host-defined cleanup steps, after which the execution context stack must be empty."
  Reading: AgentCleanupJob answers ~unused~ and leaves the agent's execution context stack empty. -/
  agentCleanupJob : ∀ vs s r s', H.choice Known.pAgentCleanupJob vs s = .ok r s' →
    r = .enum Known.eUnused ∧ M.eq (M.seqLen s'.stack) (M.ofNat 0) = true
  /-- sec-hostmakejobcallback:
  "ECMAScript hosts that are not web browsers must use the default implementation of HostMakeJobCallback."
  sec-hostcalljobcallback: "ECMAScript hosts that are not web browsers must use the default implementation of HostCallJobCallback."
  Reading: where the host answers that it is not a web browser, HostJobCallbackData answers ~empty~ and the
  steps around the callback's call ~unused~, the state as it was. -/
  jobCallbackDefault : ∀ q vs s r s', H.choice Known.pWebBrowser [.choice 1, .absent] s = .ok (.bool false) s →
    q ∈ [Known.pHostJobCallbackData, Known.pHostPrepareCallJobCallback, Known.pHostCleanupCallJobCallback] →
    Run.boundary (H.choice q vs) s = .ok r s' →
    s' = s ∧ r = .enum (if q = Known.pHostJobCallbackData then Known.eEmpty else Known.eUnused)
  /-- sec-hostcalljobcallback, the requirements:
  "It must perform and return the result of Call(jobCallback.[[Callback]], thisValue, argList)."
  Reading: the host's steps before and after the call answer ~unused~, so the call's result is returned. -/
  callJobCallback : ∀ q vs s r s', q = Known.pHostPrepareCallJobCallback ∨ q = Known.pHostCleanupCallJobCallback →
    Run.boundary (H.choice q vs) s = .ok r s' → r = .enum Known.eUnused
  /-- sec-forward-progress:
  "in a set of agents that share an executing thread, one agent eventually makes forward progress"
  Reading: HostSelectAgent answers ~empty~ or another Agent Record of the cluster that can run (`canRunAgent`),
  the state as it was. -/
  selectAgent : H.asks Known.pHostSelectAgent fun _ s r => r = .enum Known.eEmpty ∨
    isRecordOf s "Agent Record" r = true ∧ (clusterSigs s).any (Val.same (sigOf s r)) = true ∧
      Val.same (sigOf s r) (sigOf s s.agent) = false ∧ Val.same r s.agent = false ∧ canRunAgent s r = true

end Ecma
