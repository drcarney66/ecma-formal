module

public import Ecma.Host

@[expose] public section

/-!
# Jobs, by the host-call log

The Job a logged call scheduled, whether every scheduled Job has been taken, the host's next-job answer as a log
entry, and what the host does at a job boundary (§9.5, §9.10).
-/

namespace Ecma

variable {M : Model}

/-- The Job Abstract Closure the host-call log's entry at position `k` scheduled: its first argument. -/
def scheduled (log : List (HostCall M)) (k : Nat) : Option (Val M) :=
  match log.reverse[k]? with
  | some (.hook _ (job :: _) _ _ _) => some job
  | _ => none

/-- Every Job the host-call log scheduled (`HostCall.schedulesJob`) that the host may take now (`own`)
has been taken: §9.5 requires each to be performed at some future point in time. -/
def drained (log : List (HostCall M)) (own : Nat → Bool) : Bool :=
  ((log.map HostCall.schedulesJob).reverse.zipIdx).all fun (j, k) => !j || !own k || log.any (·.takes k)

/-- The log entry of the host's next-job answer at the elapsed time `t`: `.next none` only where every
Job scheduled that the host may take now (`own`) has been taken (`drained`), else the embedding's
termination of the agent (§9.7, `.terminate`). -/
def nextCall (log : List (HostCall M)) (t : M.Math) (own : Nat → Bool) : Option Nat → HostCall M
  | none => if drained log own then .next none t else .terminate
  | some k => .next (some k) t

/-- The host's collection (`Host.collect`, §9.10.3), logged, where no suspended execution context has frames
saved (`State.frames`): what such frames hold is not among the roots the host is given. -/
def collectBoundary (H : Host M) : Run M Unit := do
  let s ← Run.get
  if s.frames.isEmpty then
    let _ ← Run.hostStep .collect H.collect

/-- The erratum of a Job `job`'s clause (`jobErratum`), if any. -/
def jobErr (D : LeafCtx M) : Option (Val M) → Option ErratumId
  | some (.clo site _) => D.jobErratum site.alg.clause
  | _ => none

/-- The stop of a Job `job` that completes abruptly (§9.5 ¶8): its clause's erratum, if any. -/
def jobStop (D : LeafCtx M) (job : Option (Val M)) : Stop := Stop.atAssert D.reading (jobErr D job)

/-- Whether the job loop checks a Job `job`'s completion: in checked mode, and at an erratum's site in every mode. -/
def jobChecked (D : LeafCtx M) (job : Option (Val M)) : Bool := D.checked || (jobErr D job).isSome

end Ecma
