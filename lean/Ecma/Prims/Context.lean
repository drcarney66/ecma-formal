module

public import Ecma.State

@[expose] public section

/-!
# Notation primitives: execution contexts and agents

The primitives `Known.pRunning` … `Known.pPassedArguments` and `Known.pSwitchToAgent`: the running execution
context (the last element of `State.stack`) and its components, the execution
context stack, the surrounding agent, which the state holds as its Agent
Record (`State.agent`), its waiter lists and critical sections, the Data Blocks it shares
(`State.shared`), the Parse Node being evaluated (`State.evalNodes`), the steps that replace a
node's Evaluation (`State.evalSteps`)
and the running built-in's arguments (`State.passed`). `prim` dispatches by id.
-/

namespace Ecma.Prims.Context

variable {M : Model}

/-- The execution context at the top of the stack, if the stack is not empty. -/
def top (s : State M) : Option (Val M) :=
  M.seqGet s.stack (M.sub (M.seqLen s.stack) (M.ofNat 1))

/-- §9.4: `the running execution context`: the execution context at the top of the stack. -/
def running : List (Val M) → Run M (Val M)
  | [] => Ecma.running
  | _ => Run.stop .sortError

/-- §9.4: `the current Realm Record`: the running execution context's Realm component. -/
def currentRealm : List (Val M) → Run M (Val M)
  | [] => do readField (← Ecma.running) Known.fRealm
  | _ => Run.stop .sortError

/-- §9.4: `the active function object`: the running execution context's Function component. -/
def activeFunction : List (Val M) → Run M (Val M)
  | [] => do readField (← Ecma.running) Known.fFunction
  | _ => Run.stop .sortError

/-- §9.6: `the Agent Record of the surrounding agent`. -/
def agentRecord : List (Val M) → Run M (Val M)
  | [] => do return (← Run.get).agent
  | _ => Run.stop .sortError

/-- §9.6: `the surrounding agent`: the agent executing the steps, identified by its Agent Record. -/
def surroundingAgent : List (Val M) → Run M (Val M)
  | [] => do return (← Run.get).agent
  | _ => Run.stop .sortError

/-- §9.4: `the execution context stack is empty`. -/
def stackEmpty : List (Val M) → Run M (Val M)
  | [] => do
    let s ← Run.get
    return .bool (M.eq (M.seqLen s.stack) (M.ofNat 0))
  | _ => Run.stop .sortError

/-- §9.4: `ctx is suspended`: the execution context is not the running execution context. -/
def isSuspended : List (Val M) → Run M (Val M)
  | [.ref c] => do
    match top (← Run.get) with
    | some t => return .bool !(Val.same t (.ref c))
    | none => return .bool true
  | _ => Run.stop .sortError

/-- WaiterListFor(block, i): the store's WaiterList Record for (block, i); the first lookup of a
pair makes it, with no waiters and no leave event. -/
def waiterListFor : List (Val M) → Run M (Val M)
  | [.ref b, .math i] => do
    match (← Run.get).waiterLists.find? (fun (b', i', _) => M.addrEq b b' && M.eq i i') with
    | some (_, _, w) => return .ref w
    | none =>
      let ws ← alloc (.list M.seqNil 0)
      let w ← alloc (.record Known.sWaiterList
        (M.recSet (M.recSet M.recEmpty Known.fWaiters (.ref ws)) Known.fMostRecentLeaveEvent (.enum Known.eEmpty)))
      let s ← Run.get
      Run.set { s with waiterLists := (b, i, w) :: s.waiterLists }
      return .ref w
  | _ => Run.stop .sortError

/-- AcquireCriticalSection(wl): enter wl's critical section; the surrounding agent is the only
agent, so where it is in it already, it would wait forever: the run stops. -/
def acquireCriticalSection : List (Val M) → Run M (Val M)
  | [.ref w] => do
    let s ← Run.get
    if s.critical.any (M.addrEq w) then Run.stop .assertFailed
    else
      Run.set { s with critical := w :: s.critical }
      return .enum Known.eUnused
  | _ => Run.stop .sortError

/-- ReleaseCriticalSection(wl): leave wl's critical section, which the surrounding agent is in. -/
def releaseCriticalSection : List (Val M) → Run M (Val M)
  | [.ref w] => do
    let s ← Run.get
    if s.critical.any (M.addrEq w) then
      Run.set { s with critical := s.critical.filter (!M.addrEq w ·) }
      return .enum Known.eUnused
    else Run.stop .assertFailed
  | _ => Run.stop .sortError

/-- EnteredCriticalSections(): a new List of the WaiterList Records whose critical section the
surrounding agent is in. -/
def enteredCriticalSections : List (Val M) → Run M (Val M)
  | [] => do listOf ((← Run.get).critical.map .ref)
  | _ => Run.stop .sortError

/-- SetEvaluationSteps(n, c): `c` the steps n's evaluation performs from now on, in place of any earlier. -/
def setEvaluationSteps : List (Val M) → Run M (Val M)
  | [.node n, c] => do
    let s ← Run.get
    Run.set { s with evalSteps := (n, c) :: s.evalSteps.filter (!M.nodeEq n ·.1) }
    return .enum Known.eUnused
  | _ => Run.stop .sortError

/-- EvaluationStepsOf(n): the steps the last SetEvaluationSteps of n gave, or ~empty~. -/
def evaluationStepsOf : List (Val M) → Run M (Val M)
  | [.node n] => do
    match (← Run.get).evalSteps.find? (M.nodeEq n ·.1) with
    | some (_, c) => return c
    | none => return .enum Known.eEmpty
  | _ => Run.stop .sortError

/-- Whether the value is a Data Block of the store, and whether it is one of the Shared Data Blocks. -/
def blockKind (v : Val M) : Run M (Option Bool) := do
  match v with
  | .ref a =>
    match ← readCell a with
    | .block _ => return some ((← Run.get).shared.any (M.addrEq a))
    | _ => return none
  | _ => return none

/-- IsDataBlock(v): v is a Data Block that is not a Shared Data Block. -/
def isDataBlock : List (Val M) → Run M (Val M)
  | [v] => do return .bool ((← blockKind v) == some false)
  | _ => Run.stop .sortError

/-- IsSharedDataBlock(v): v is a Shared Data Block. -/
def isSharedDataBlock : List (Val M) → Run M (Val M)
  | [v] => do return .bool ((← blockKind v) == some true)
  | _ => Run.stop .sortError

/-- DesignateShared(block): block, a new byte List of the store, made one of the Shared Data Blocks. -/
def designateShared : List (Val M) → Run M (Val M)
  | [v@(.ref a)] => do
    if (← blockKind v) == some false then
      let s ← Run.get
      Run.set { s with shared := a :: s.shared }
      return v
    else Run.stop .sortError
  | _ => Run.stop .sortError

/-- The execution context stack's elements, the top first. -/
def topDown (s : State M) : List (Val M) :=
  M.seqFoldl (fun acc v => v :: acc) [] s.stack

/-- ContextBelowTop(): the second to top element of the execution context stack, or ~empty~ if it
has fewer than two elements. -/
def contextBelowTop : List (Val M) → Run M (Val M)
  | [] => do
    match topDown (← Run.get) with
    | _ :: c :: _ => return c
    | _ => return .enum Known.eEmpty
  | _ => Run.stop .sortError

/-- OnContextStack(ctx): whether ctx is an element of the execution context stack. -/
def onContextStack : List (Val M) → Run M (Val M)
  | [.ref c] => do return .bool ((topDown (← Run.get)).any (Val.same · (.ref c)))
  | _ => Run.stop .sortError

/-- TopmostScriptOrModuleContext(): the topmost execution context on the stack whose ScriptOrModule
component is not *null*, or ~empty~ if there is none. -/
def topmostScriptOrModuleContext : List (Val M) → Run M (Val M)
  | [] => do
    let rec go : List (Val M) → Run M (Val M)
      | [] => return .enum Known.eEmpty
      | c :: cs => do
        match ← readField c Known.fScriptOrModule with
        | .null => go cs
        | _ => return c
    go (topDown (← Run.get))
  | _ => Run.stop .sortError

/-- CurrentProduction(): the Parse Node of the innermost running SDO (Early Errors aside). -/
def currentProduction : List (Val M) → Run M (Val M)
  | [] => do
    match (← Run.get).evalNodes with
    | nd :: _ => return .node nd
    | [] => Run.stop .assertFailed
  | _ => Run.stop .sortError

/-- PassedArguments(): the List of arguments the running built-in function was passed. -/
def passedArguments : List (Val M) → Run M (Val M)
  | [] => do
    match (← Run.get).passed with
    | l :: _ => return l
    | [] => Run.stop .assertFailed
  | _ => Run.stop .sortError

/-- SwitchToAgent(a): park the execution context stack in the surrounding agent's [[ParkedStack]]
and install the Agent Record a's, whose running context is resumed next; no critical section is held. -/
def switchToAgent : List (Val M) → Run M (Val M)
  | [.ref t] => do
    let s ← Run.get
    if !s.critical.isEmpty || Val.same s.agent (.ref t) then Run.stop .assertFailed else
    match ← readField (.ref t) Known.fParkedStack with
    | .ref l => match ← readCell l with
      | .list st _ => do
        let p ← alloc (.list s.stack 0)
        writeField s.agent Known.fParkedStack (.ref p)
        let s ← Run.get
        Run.set { s with stack := st, agent := .ref t, suspended := (top s).getD .absent }
        return .enum Known.eUnused
      | _ => Run.stop .sortError
    | _ => Run.stop .sortError
  | _ => Run.stop .sortError

/-- The primitives of execution contexts and agents, by id; `none` for any other id. -/
def prim (p : PrimId) (vs : List (Val M)) : Option (Run M (Val M)) :=
  if p == Known.pRunning then some (running vs)
  else if p == Known.pCurrentRealm then some (currentRealm vs)
  else if p == Known.pActiveFunction then some (activeFunction vs)
  else if p == Known.pAgentRecord then some (agentRecord vs)
  else if p == Known.pSurroundingAgent then some (surroundingAgent vs)
  else if p == Known.pStackEmpty then some (stackEmpty vs)
  else if p == Known.pIsSuspended then some (isSuspended vs)
  else if p == Known.pWaiterListFor then some (waiterListFor vs)
  else if p == Known.pAcquireCriticalSection then some (acquireCriticalSection vs)
  else if p == Known.pReleaseCriticalSection then some (releaseCriticalSection vs)
  else if p == Known.pEnteredCriticalSections then some (enteredCriticalSections vs)
  else if p == Known.pSetEvaluationSteps then some (setEvaluationSteps vs)
  else if p == Known.pEvaluationStepsOf then some (evaluationStepsOf vs)
  else if p == Known.pIsDataBlock then some (isDataBlock vs)
  else if p == Known.pIsSharedDataBlock then some (isSharedDataBlock vs)
  else if p == Known.pDesignateShared then some (designateShared vs)
  else if p == Known.pContextBelowTop then some (contextBelowTop vs)
  else if p == Known.pOnContextStack then some (onContextStack vs)
  else if p == Known.pTopmostScriptOrModuleContext then some (topmostScriptOrModuleContext vs)
  else if p == Known.pCurrentProduction then some (currentProduction vs)
  else if p == Known.pPassedArguments then some (passedArguments vs)
  else if p == Known.pSwitchToAgent then some (switchToAgent vs)
  else none

end Ecma.Prims.Context
