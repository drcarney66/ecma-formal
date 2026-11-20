module

public import Ecma.Machine.Frame

@[expose] public section

/-!
# The state and the result of a leaf operation

The observable state (`State`), a leaf operation's result and monad (`Res`, `Run`),
what a leaf operation reads (`LeafCtx`), environments, and the
operations on values that the machine and its primitives share.
-/

namespace Ecma

section
variable (M : Model)

/-- The observable state. -/
structure State where
  heap : M.Heap (Cell M)
  /-- the execution context stack, the running execution context last -/
  stack : M.Seq (Val M)
  /-- the Completion Record with which the running computation was last resumed -/
  resumed : Val M
  /-- the execution context whose evaluation a transfer suspends: the running one before the
  execution context stack last changed -/
  suspended : Val M := .absent
  /-- the surrounding agent's Agent Record (§9.7) -/
  agent : Val M
  /-- parser invocations so far -/
  parses : Nat := 0
  /-- the parser invocations of source text that is strict mode code from outside (§11.2.2) -/
  strictParses : List Nat := []
  /-- the parser invocations for ParseJSON (§25.5.1) -/
  jsonParses : List Nat := []
  /-- the parser invocations of eval code processed by a direct eval (§19.2.1.1) -/
  directParses : List Nat := []
  /-- the parser invocations with the goal symbol |Module|, and the reparses within them (B.1.1) -/
  moduleParses : List Nat := []
  /-- the root Parse Node of each parser invocation that gave one, by its stamp -/
  roots : Std.ExtTreeMap Nat M.Node := ∅
  /-- each cover's reparse (§5.1.5), by its invocation: the covering Parse Node it was a reparse of -/
  covers : List (Nat × M.Node) := []
  /-- each cover's reparse that gave a Parse Node (§5.1.5): the covering node, the covered nonterminal, the root -/
  covered : List (M.Node × NtId × M.Node) := []
  /-- Symbols created so far -/
  syms : Nat := 0
  /-- the agent cluster's store of WaiterList Records: each Record by its Shared Data Block and byte offset -/
  waiterLists : List (M.Addr × M.Math × M.Addr) := []
  /-- the WaiterList Records whose critical section the surrounding agent is in -/
  critical : List M.Addr := []
  /-- the Shared Data Blocks: the byte Lists of the store that are shared -/
  shared : List M.Addr := []
  /-- the Parse Nodes whose SDOs are running (Early Errors aside), innermost first -/
  evalNodes : List M.Node := []
  /-- the steps that replace a Parse Node's Evaluation (B.3.2), by the node, the latest first -/
  evalSteps : List (M.Node × Val M) := []
  /-- the arguments Lists the running built-in function calls were passed, innermost first -/
  passed : List (Val M) := []
  /-- the host's calls so far, the latest first; the position of a call counts from the first -/
  hostLog : List (HostCall M) := []
  /-- the shape changes of objects so far, the latest first (EnumerateObjectProperties ¶3) -/
  shapeLog : List (ShapeChange M) := []
  /-- the frames of each suspended execution context (its code evaluation state, §9.4), the latest first -/
  frames : List (M.Addr × List (Machine.Frame M)) := []

inductive Res (α : Type) where
  | ok (a : α) (s : State M)
  /-- leaving the algorithm with an abrupt completion -/
  | esc (c : Val M) (s : State M)
  | stop (r : Stop)

def Run (α : Type) : Type := State M → Res M α
end

/-- The number of host calls before a shape change. -/
abbrev ShapeChange.stamp {M : Model} (c : ShapeChange M) : Nat := c.before.length

/-- The stop of a check at a site of erratum `e`: the erratum under its literal reading, else `r`. -/
def Stop.at (rd : ErratumId → Reading) (e : ErratumId) (r : Stop) : Stop :=
  if rd e == .literal then .erratum e else r

/-- The stop of a false Assert at a site of erratum `r` (`Stmt.assertAt`): `Stop.at`, else a failed Assert. -/
def Stop.atAssert (rd : ErratumId → Reading) : Option ErratumId → Stop
  | some e => Stop.at rd e .assertFailed
  | none => .assertFailed

namespace Run
variable {M : Model} {α β : Type}

@[inline] def pure (a : α) : Run M α := fun s => .ok a s
/-- Sequencing; a transfer carries the rest of the computation with it. -/
def Res.bind : Res M α → (α → State M → Res M β) → Res M β
  | .ok a s, f => f a s
  | .esc c s, _ => .esc c s
  | .stop r, _ => .stop r

@[inline] def bind (m : Run M α) (f : α → Run M β) : Run M β := fun s => Res.bind (m s) f
@[inline] def stop (r : Stop) : Run M α := fun _ => .stop r
@[inline] def get : Run M (State M) := fun s => .ok s s
@[inline] def set (s : State M) : Run M Unit := fun _ => .ok () s
@[inline] def esc (c : Val M) : Run M α := fun s => .esc c s

instance : Monad (Run M) where
  pure := Run.pure
  bind := Run.bind

/-- The algorithm boundary: an escaping completion becomes the return value. -/
def Res.boundary : Res M (Val M) → Res M (Val M)
  | .esc c s => .ok c s
  | r => r

@[inline] def boundary (m : Run M (Val M)) : Run M (Val M) := fun s => Res.boundary (m s)

/-- `r` with a state component `set` to `outer` when control leaves it, and to `inner` again when
a transfer resumes it; a call runs, and resumes it, in the inner state. -/
def Res.within {γ : Type} (set : State M → γ → State M) (outer inner : γ) : Res M α → Res M α
  | .ok a s => .ok a (set s outer)
  | .esc c s => .esc c (set s outer)
  | .stop r => .stop r

/-- `m` run with the state component `get`/`set` changed by `f`, and restored when control leaves
it, also by a transfer: a dynamically scoped binding. -/
def within {γ : Type} (get : State M → γ) (set : State M → γ → State M) (f : γ → γ) (m : Run M α) :
    Run M α := fun s =>
  let i := f (get s)
  Res.within set (get s) i (m (set s i))

/-- The elements first to last folded by a step that runs, each step run on the last one's result:
`M.seqFoldl (fun acc x => bind acc (f · x)) (pure b) xs` without a nested run per element. -/
def seqFold {γ : Type} (f : β → γ → Run M β) (b : β) (xs : M.Seq γ) : Run M β := fun s =>
  M.seqFoldl (fun r x => Res.bind r fun b => f b x) (.ok b s) xs

end Run

/-- What a leaf operation reads of the program and of the run: it makes no call. -/
structure LeafCtx (M : Model) where
  /-- `k` is `s` or a subsort of it -/
  sub : SortId → SortId → Bool
  /-- the sole nonterminal of a unit production -/
  unit : ProdId → Option NtId
  /-- the terminals of a production's present right-hand side, by position -/
  terms : ProdId → List (Nat × String)
  /-- whether a phrase's meaning spreads its list hole (`PhraseArg.spread`) -/
  spread : PhraseId → Bool
  /-- the clause of each Annex B overlay section, where the program has it -/
  overlayClause : Grammar.AnnexB → Option ClauseId
  /-- the Annex B overlay sections the host supports (B.1, B.3): its logged choices -/
  annexB : Run M Grammar.AnnexB.Set
  /-- the reading chosen for each erratum -/
  reading : ErratumId → Reading
  /-- checked mode: the Asserts that cost an evaluation are evaluated -/
  checked : Bool
  /-- whether the host's resources run out at pushing an execution context in a state (`Host.exhausts`) -/
  exhausts : State M → Bool
  /-- the erratum whose text stops at the job loop's check for a Job the clause makes -/
  jobErratum : ClauseId → Option ErratumId

/-! Environments: one value per slot, as nested pairs. -/

@[reducible] def Env (M : Model) (n : Nat) : Type :=
  Nat.rec (motive := fun _ => Type) Unit (fun _ E => Val M × E) n

section
variable {M : Model}

/-- A logged call schedules a Job (§9.5): a hook whose first argument is an Abstract Closure, as
HostEnqueueGenericJob's, HostEnqueuePromiseJob's and HostEnqueueTimeoutJob's are (a cleanup job's
is its FinalizationRegistry). -/
def HostCall.schedulesJob : HostCall M → Bool
  | .hook _ (.clo .. :: _) _ _ _ => true
  | _ => false

/-- A logged call takes the job scheduled at log position `k` to run: the job loop's `next`, or an
agent's AgentNextJob. -/
def HostCall.takes (k : Nat) : HostCall M → Bool
  | .next (some j) _ => j == k
  | .choice q _ (.math j) => q == Known.pAgentNextJob && M.eq j (M.ofNat k)
  | _ => false

/-- `n` variables from `env`: its first `n`, the rest unbound (a table step's, `Env.init n env`'s values). -/
def cutVars (n : Nat) (env : List (Val M)) : List (Val M) :=
  env.take n ++ List.replicate (n - env.length) .unbound

/-- Arguments to `p` parameters, a parameter not passed `.absent`. -/
def padArgs : Nat → List (Val M) → List (Val M)
  | 0, vs => vs
  | p + 1, [] => .absent :: padArgs p []
  | p + 1, v :: vs => v :: padArgs p vs

/-! The store. -/

def readCell (a : M.Addr) : Run M (Cell M) := fun s =>
  match M.heapGet s.heap a with
  | some c => .ok c s
  | none => .stop .sortError

def writeCell (a : M.Addr) (c : Cell M) : Run M Unit := fun s =>
  .ok () { s with heap := M.heapSet s.heap a c }

/-- Write a List cell's elements, keeping its origin. -/
def writeList (a : M.Addr) (xs : M.Seq (Val M)) : Run M Unit := fun s =>
  let o := match M.heapGet s.heap a with
    | some (.list _ o) => o
    | _ => 0
  .ok () { s with heap := M.heapSet s.heap a (.list xs o) }

/-- Modify a Data Block cell in place, clearing its heap slot before updating so `Impl`'s ByteArray keeps
reference count 1. -/
def modifyBlock (a : M.Addr) (f : M.Bytes → M.Bytes) : Run M Unit := fun s =>
  match M.heapGet s.heap a with
  | some (.block bs) =>
    let h := M.heapSet s.heap a (.block (M.bytesZero (M.ofNat 0)))
    .ok () { s with heap := M.heapSet h a (.block (f bs)) }
  | _ => .stop .sortError

def alloc (c : Cell M) : Run M M.Addr := fun s =>
  let (a, h) := M.heapAlloc s.heap c
  .ok a { s with heap := h }

def optOr {α : Type} (r : Stop) : Option α → Run M α
  | some a => Run.pure a
  | none => Run.stop r

/-- `v.[[F]]`, and an execution context's components. -/
def readField (v : Val M) (f : FieldId) : Run M (Val M) :=
  match v with
  | .ref a => do
    match ← readCell a with
    | .record _ fs | .env _ fs _ => optOr .sortError (M.recGet fs f)
    | _ => Run.stop .sortError
  | .obj a => do
    match ← readCell a with
    | .object sl _ => optOr .sortError (M.recGet sl f)
    | _ => Run.stop .sortError
  | .comp t x y =>
    if f == Known.fType then Run.pure (.enum t)
    else if f == Known.fValue then Run.pure x
    else if f == Known.fTarget then Run.pure y
    else Run.stop .sortError
  | .sym s =>
    if f == Known.fDescription then Run.pure (match M.symDesc s with
      | some d => .str d
      | none => .undefined)
    else Run.stop .sortError
  | _ => Run.stop .sortError

/-- Record a shape change of the object at `a`. -/
def logShape (a : M.Addr) (added : Bool) : Run M Unit := fun s =>
  .ok () { s with shapeLog := ⟨a, added, s.hostLog⟩ :: s.shapeLog }

/-- A [[Prototype]] that was an Object or *null* is set to another value. -/
def protoChanged : Option (Val M) → Val M → Bool
  | some (.obj p), .obj q => !M.addrEq p q
  | some (.obj _), _ => true
  | some .null, .null => false
  | some .null, _ => true
  | _, _ => false

def writeField (v : Val M) (f : FieldId) (x : Val M) : Run M Unit :=
  match v with
  | .ref a => do
    match ← readCell a with
    | .record k fs => writeCell a (.record k (M.recSet fs f x))
    | .env k fs b => writeCell a (.env k (M.recSet fs f x) b)
    | _ => Run.stop .sortError
  | .obj a => do
    match ← readCell a with
    | .object sl ps =>
      if f == Known.fPrototype && protoChanged (M.recGet sl f) x then logShape a false
      writeCell a (.object (M.recSet sl f x) ps)
    | _ => Run.stop .sortError
  | _ => Run.stop .sortError

/-- The running execution context. -/
def running : Run M (Val M) := do
  let s ← Run.get
  optOr .sortError (M.seqGet s.stack (M.sub (M.seqLen s.stack) (M.ofNat 1)))

/-- `%name%`: the current Realm's intrinsic. -/
def intrinsic (i : FieldId) : Run M (Val M) := do
  let realm ← readField (← running) Known.fRealm
  readField (← readField realm Known.fIntrinsics) i

/-! Values. -/

def mathOf : Sign → Mag → Val M
  | _, .inf => .absent
  | .minus, .num n => .math (M.neg (numeral n))
  | _, .num n => .math (numeral n)
where
  numeral : Numeral → M.Math
    | .dec n => M.ofNat n
    | .hex n _ => M.ofNat n
    | .frac w f k => M.add (M.ofNat w) (M.div (M.ofNat f) (M.pow (M.ofNat 10) (M.ofNat k)))

/-- A value literal `*…*`. -/
def valOf : ValLit → Run M (Val M)
  | .undefined => Run.pure .undefined
  | .null => Run.pure .null
  | .true => Run.pure (.bool true)
  | .false => Run.pure (.bool false)
  | .str s _ => Run.pure (.str (M.strLit s))
  | .nan _ => Run.pure (.num M.numNaN)
  | .num sg .inf .f => Run.pure (.num (M.numInf (sg == .minus)))
  | .num sg (.num (.dec 0)) .f => Run.pure (.num (M.numZero (sg == .minus)))
  | .num sg m .f => match mathOf sg m with
    | .math x => Run.pure (.num (M.numOf x))
    | _ => Run.stop .sortError
  | .num sg m .z => match mathOf sg m with
    | .math x => Run.pure (.big (M.bigOf x))
    | _ => Run.stop .sortError
  | .num _ _ .none => Run.stop .sortError
  | .this => Run.stop .residue
  | .err i => Run.pure (.field i)
  | .bigN n => match mathOf .none (.num n) with
    | .math x => Run.pure (.big (M.bigOf x))
    | _ => Run.stop .sortError

/-- "x is y": the same value. -/
def Val.same : Val M → Val M → Bool
  | .undefined, .undefined => true
  | .null, .null => true
  | .bool a, .bool b => a == b
  | .str a, .str b => M.strEq a b
  | .sym a, .sym b => M.symEq a b
  | .num a, .num b => match M.numView a, M.numView b with
    | .nan, .nan => true
    | .posInf, .posInf => true
    | .negInf, .negInf => true
    | .posZero, .posZero => true
    | .negZero, .negZero => true
    | .finite x, .finite y => M.eq x y
    | _, _ => false
  | .big a, .big b => M.eq (M.bigVal a) (M.bigVal b)
  | .obj a, .obj b => M.addrEq a b
  | .ref a, .ref b => M.addrEq a b
  | .comp t v g, .comp u w h => t == u && Val.same v w && Val.same g h
  | .math a, .math b => M.eq a b
  | .posInf, .posInf => true
  | .negInf, .negInf => true
  | .enum a, .enum b => a == b
  | .field a, .field b => a == b
  | .nt a as, .nt b bs => a == b && as == bs
  | .param a, .param b => a == b
  | .prod a, .prod b => a == b
  | .node a, .node b => M.nodeEq a b
  | .leaf a i _, .leaf b j _ => M.nodeStamp a == M.nodeStamp b && M.nodeSpan a == M.nodeSpan b &&
    M.nodeNt a == M.nodeNt b && i == j
  | .term a, .term b => a == b
  | .node n, .prod ps => ps.contains (M.nodeProd n)
  | .prod ps, .node n => ps.contains (M.nodeProd n)
  | .absent, .absent => true
  | .missing, .missing => true
  | .clause a, .clause b => a == b
  | .alg a, .alg b => a == b
  | .sort a, .sort b => a == b
  | .table a, .table b => a == b
  | .choice a, .choice b => a == b
  | _, _ => false

/-- Two values whose identity "is" cannot compare: Abstract Closures (`.clo` is not a closure's
identity), type holes, conditions. -/
def Val.incomparable : Val M → Val M → Bool
  | .clo .., .clo .. | .ty .., .ty .. | .cond .., .cond .. => true
  | _, _ => false

/-- Membership of a value in a sort of the `Known` prelude; a data sort's test is the program's
(the machine's), and without one it is residue. -/
def Val.hasSort (v : Val M) (s : SortId) : Run M Bool :=
  if s == Known.sNumber then Run.pure (v matches .num _)
  else if s == Known.sString then Run.pure (v matches .str _)
  else if s == Known.sBoolean then Run.pure (v matches .bool _)
  else if s == Known.sSymbol then Run.pure (v matches .sym _)
  else if s == Known.sBigInt then Run.pure (v matches .big _)
  else if s == Known.sObject then Run.pure (v matches .obj _)
  else if s == Known.sUndefined then Run.pure (v matches .undefined)
  else if s == Known.sNull then Run.pure (v matches .null)
  else if s == Known.sMath then Run.pure (v matches .math _)
  else if s == Known.sXMath then Run.pure (v matches .math _ | .posInf | .negInf)
  else if s == Known.sInteger then Run.pure (match v with | .math m => M.isInt m | _ => false)
  else if s == Known.sNonNegInt then
    Run.pure (match v with | .math m => M.isInt m && !M.lt m (M.ofNat 0) | _ => false)
  else if s == Known.sNode then Run.pure (v matches .node _)
  else if s == Known.sClosure then Run.pure (v matches .clo _ _)
  else if s == Known.sComp then Run.pure (v matches .comp _ _ _)
  else if s == Known.sNormalComp then Run.pure (match v with | .comp t _ _ => t == Known.eNormal | _ => false)
  else if s == Known.sAbruptComp then Run.pure (match v with | .comp t _ _ => t != Known.eNormal | _ => false)
  else if s == Known.sThrowComp then Run.pure (match v with | .comp t _ _ => t == Known.eThrow | _ => false)
  else if s == Known.sReturnComp then Run.pure (match v with | .comp t _ _ => t == Known.eReturn | _ => false)
  else if s == Known.sLangValue then
    Run.pure (v matches .undefined | .null | .bool _ | .str _ | .sym _ | .num _ | .big _ | .obj _)
  else if s == Known.sPropKey then Run.pure (v matches .str _ | .sym _)
  else match v with
    | .ref a => do
      match ← readCell a with
      | .record k _ | .env k _ _ =>
        if k == s || s == Known.sRecord then Run.pure true
        else if s < Known.sorts.size then Run.pure false else Run.stop .residue
      | .list .. | .block .. => Run.pure (s == Known.sList)
      | .charSet .. => Run.pure (s == Known.sCharSet)
      | _ => Run.pure false
    | _ => if s < Known.sorts.size then Run.pure false else Run.stop .residue

/-- Unary minus, by the operand's type (§5.2.6). -/
def unOp : UnOp → Val M → Run M (Val M)
  | .neg, .math x => Run.pure (.math (M.neg x))
  | .neg, .posInf => Run.pure .negInf
  | .neg, .negInf => Run.pure .posInf
  | .neg, .num x => Run.pure (.num (M.numNeg x))
  | .neg, .big x => Run.pure (.big (M.bigOf (M.neg (M.bigVal x))))
  | .not, .bool b => Run.pure (.bool !b)
  | _, _ => Run.stop .sortError

/-- ℤ(x) for an integer x (§5.2.6): a residue where the model does not hold the BigInt
(ℝ(ℤ(x)) ≠ x); a sort error for a non-integer. -/
def bigFor (x : M.Math) : Run M (Val M) :=
  if !M.isInt x then Run.stop .sortError
  else
    let b := M.bigOf x
    if M.eq (M.bigVal b) x then Run.pure (.big b) else Run.stop .residue

/-- An arithmetic operation on mathematical values; none outside its domain (x / 0, x modulo 0,
x<sup>y</sup> unless x > 0, or y an integer and x ≠ 0 or y ≥ 0). -/
def mathOp (o : BinOp) (x y : M.Math) : Option M.Math :=
  let zero := M.ofNat 0
  match o with
  | .add => some (M.add x y)
  | .plus => some (M.add x y)
  | .sub => some (M.sub x y)
  | .mul => some (M.mul x y)
  | .times => some (M.mul x y)
  | .div => if M.eq y zero then none else some (M.div x y)
  | .modulo => if M.eq y zero then none else some (M.sub x (M.mul y (M.floor (M.div x y))))
  | .pow =>
    if M.lt zero x || (M.isInt y && (!M.eq x zero || !M.lt y zero)) then some (M.pow x y) else none

/-- Arithmetic by the operands' type (§5.2.6): mathematical values, the extended reals (an
indeterminate form stops), IEEE 754-2019 on Numbers, and BigInts by their mathematical values (a
result that is not an integer stops). -/
def binOp (o : BinOp) (a b : Val M) : Run M (Val M) :=
  match a, b with
  | .math x, .math y => match mathOp o x y with
    | some z => Run.pure (.math z)
    | none => Run.stop .sortError
  | .num x, .num y => match o with
    | .add => Run.pure (.num (M.numAdd x y))
    | .plus => Run.pure (.num (M.numAdd x y))
    | .times => Run.pure (.num (M.numMul x y))
    | .sub => Run.pure (.num (M.numSub x y))
    | .mul => Run.pure (.num (M.numMul x y))
    | .div => Run.pure (.num (M.numDiv x y))
    | _ => Run.stop .sortError
  | .big x, .big y => match mathOp o (M.bigVal x) (M.bigVal y) with
    | some z => bigFor z
    | none => Run.stop .sortError
  | x, y => xOp o x y
where
  /-- The extended reals, where an operand is ±∞. -/
  xOp : BinOp → Val M → Val M → Run M (Val M)
    | .add, .posInf, .posInf => Run.pure .posInf
    | .add, .negInf, .negInf => Run.pure .negInf
    | .add, .posInf, .math _ => Run.pure .posInf
    | .add, .negInf, .math _ => Run.pure .negInf
    | .add, .math _, .posInf => Run.pure .posInf
    | .add, .math _, .negInf => Run.pure .negInf
    | .sub, .posInf, .negInf => Run.pure .posInf
    | .sub, .negInf, .posInf => Run.pure .negInf
    | .sub, .posInf, .math _ => Run.pure .posInf
    | .sub, .negInf, .math _ => Run.pure .negInf
    | .sub, .math _, .posInf => Run.pure .negInf
    | .sub, .math _, .negInf => Run.pure .posInf
    | _, _, _ => Run.stop .sortError

/-- Comparison by the operands' type (§5.2.6): the extended reals, IEEE 754-2019 on Numbers,
BigInts by their mathematical values; an operand the model does not hold, or a comparison it does
not decide, is a residue. -/
def relOp : RelOp → Val M → Val M → Run M Bool
  | .lt, a, b => lt a b
  | .le, a, b => do return (← lt a b) || (← eq a b)
  | .gt, a, b => lt b a
  | .ge, a, b => do return (← lt b a) || (← eq a b)
  | .eq, a, b => eq a b
  | .ne, a, b => do return !(← eq a b)
where
  lt : Val M → Val M → Run M Bool
    | .num x, .num y => Run.pure (M.numLt x y)
    | .big x, .big y => Run.pure (M.lt (M.bigVal x) (M.bigVal y))
    | .math x, .math y => Run.pure (M.lt x y)
    | .negInf, .negInf => Run.pure false
    | .negInf, .math _ => Run.pure true
    | .negInf, .posInf => Run.pure true
    | .math _, .posInf => Run.pure true
    | .math _, .negInf => Run.pure false
    | .posInf, .math _ => Run.pure false
    | .posInf, .posInf => Run.pure false
    | .posInf, .negInf => Run.pure false
    | _, _ => Run.stop .sortError
  eq : Val M → Val M → Run M Bool
    | .num x, .num y => Run.pure (M.numEq x y)
    | .big x, .big y => Run.pure (M.eq (M.bigVal x) (M.bigVal y))
    | .math x, .math y => Run.pure (M.eq x y)
    | .posInf, .posInf => Run.pure true
    | .negInf, .negInf => Run.pure true
    | .math _, .posInf => Run.pure false
    | .math _, .negInf => Run.pure false
    | .posInf, .math _ => Run.pure false
    | .negInf, .math _ => Run.pure false
    | .posInf, .negInf => Run.pure false
    | .negInf, .posInf => Run.pure false
    | _, _ => Run.stop .sortError

/-- `? v` (§5.2.3.4): a normal completion's value; an abrupt one leaves the algorithm. -/
def question (chk : Bool) : Val M → Run M (Val M)
  | .comp t x y => if t == Known.eNormal then Run.pure x else Run.esc (.comp t x y)
  | v => if chk then Run.stop .assertFailed else Run.pure v

/-- `! v`: a normal completion's value; an abrupt one is an assertion failure. In checked mode
a value that is not a Completion Record fails the Assert of the expansion (§5.2.3.4). -/
def bang (chk : Bool) : Val M → Run M (Val M)
  | .comp t x _ => if t == Known.eNormal then Run.pure x else Run.stop .assertFailed
  | v => if chk then Run.stop .assertFailed else Run.pure v

/-- `! v` at a site of an erratum: as `bang`, an abrupt completion stops with `r`. -/
def bangAt (chk : Bool) (r : Stop) : Val M → Run M (Val M)
  | .comp t x _ => if t == Known.eNormal then Run.pure x else Run.stop r
  | v => if chk then Run.stop .assertFailed else Run.pure v

def bool : Val M → Run M Bool
  | .bool b => Run.pure b
  | _ => Run.stop .sortError

def listOf (vs : List (Val M)) : Run M (Val M) := do
  return .ref (← alloc (.list (vs.foldl M.seqPush M.seqNil) 0))

/-! The Object sort's primitives (the overlay's `<emu-primitive>`s): own properties as
attribute Records, in creation order. -/

/-- A property key. -/
def keyOf : Val M → Option (M.Str ⊕ M.Sym)
  | .str s => some (.inl s)
  | .sym s => some (.inr s)
  | _ => none

def objCell (o : Val M) : Run M (M.Addr × M.Rec (Val M) × M.Props (Val M)) :=
  match o with
  | .obj a => do
    match ← readCell a with
    | .object sl ps => Run.pure (a, sl, ps)
    | _ => Run.stop .sortError
  | _ => Run.stop .sortError

def recOf (r : Val M) : Run M (M.Addr × SortId × M.Rec (Val M)) :=
  match r with
  | .ref a => do
    match ← readCell a with
    | .record k fs | .env k fs _ => Run.pure (a, k, fs)
    | _ => Run.stop .sortError
  | _ => Run.stop .sortError

/-- A Record's field names, ascending: a function of its fields alone, not of the model's order. -/
def recFieldNames {α : Type} (r : M.Rec α) : List FieldId :=
  (M.seqFoldl (fun acc f => f :: acc) [] (M.recKeys r)).mergeSort fun a b => decide (a ≤ b)

/-- Whether a Record has no fields. -/
def recIsEmpty {α : Type} (r : M.Rec α) : Bool :=
  M.eq (M.seqLen (M.recKeys r)) (M.ofNat 0)

/-- `r` with each field of `desc` set to `desc`'s value. -/
def recSetAll {α : Type} (r desc : M.Rec α) : M.Rec α :=
  M.seqFoldl (fun r f => match M.recGet desc f with
    | some v => M.recSet r f v
    | none => r) r (M.recKeys desc)

/-- Table 4: an attribute's default value. -/
def attrDefault (f : FieldId) : Val M :=
  if f == Known.fValue || f == Known.fGetter || f == Known.fSetter then .undefined else .bool false

/-- The attributes of a data or an accessor property. -/
def attrsOf (kind : EnumId) : List FieldId :=
  if kind == Known.eAccessor then [Known.fGetter, Known.fSetter, Known.fEnumerable, Known.fConfigurable]
  else [Known.fValue, Known.fWritable, Known.fEnumerable, Known.fConfigurable]

/-- A property of `kind` whose attributes are `desc`'s fields where present, else `given`'s, else
the defaults. -/
def newAttrs (kind : EnumId) (desc : M.Rec (Val M)) (given0 : List (FieldId × Val M)) : M.Rec (Val M) :=
  (attrsOf kind).foldl (fun r f => M.recSet r f (match M.recGet desc f with
    | some v => v
    | none => (look' f given0).getD (attrDefault f))) M.recEmpty
where
  look' (f : FieldId) : List (FieldId × Val M) → Option (Val M)
    | [] => none
    | (g, v) :: r => if g == f then some v else look' f r

/-- OwnPropertyLookup(O, P): O's own property whose key is P. -/
def ownLookup (o p : Val M) : Run M (Val M) := do
  let (_, _, ps) ← objCell o
  match keyOf p with
  | some k => optOr .assertFailed (M.propsGet ps k)
  | none => Run.stop .sortError

/-- OwnPropertyCreate(O, P, Desc, kind) (`create`: O has no own property P) and
OwnPropertyReplace(O, P, Desc, kind, …) (O has one): the property last in creation order, or in
place. -/
def ownPut (create : Bool) (o p d : Val M) (kind : EnumId) (given0 : List (FieldId × Val M)) :
    Run M (Val M) := do
  let (a, sl, ps) ← objCell o
  let (_, _, desc) ← recOf d
  match keyOf p with
  | some k => do
    if create != (M.propsGet ps k).isNone then Run.stop .sortError else
    let r ← alloc (.record Known.sRecord (newAttrs kind desc given0))
    logShape a create
    writeCell a (.object sl (M.propsPut ps k (.ref r)))
    return .enum Known.eUnused
  | none => Run.stop .sortError

/-- An [[Enumerable]] attribute's value is the Boolean `e`. -/
def valSame : Option (Val M) → Val M → Bool
  | some (.bool a), .bool b => a == b
  | _, _ => false

/-- OwnPropertySetAttribute(O, P, Desc): each of Desc's fields into the attribute of that name. -/
def ownSetAttrs (o p d : Val M) : Run M (Val M) := do
  let prop ← ownLookup o p
  let (pa, pk, pfs) ← recOf prop
  let (_, _, desc) ← recOf d
  let fs := recSetAll pfs desc
  match M.recGet desc Known.fEnumerable with
  | some e => if !valSame (M.recGet pfs Known.fEnumerable) e then
      let (a, _, _) ← objCell o
      logShape a false
  | none => pure ()
  writeCell pa (.record pk fs)
  return .enum Known.eUnused

/-- OwnPropertyHas(O, P): whether O has an own property whose key is P. -/
def ownHas (o p : Val M) : Run M (Val M) := do
  let (_, _, ps) ← objCell o
  match keyOf p with
  | some k => return .bool (M.propsGet ps k).isSome
  | none => Run.stop .sortError

/-- A key's numeric index, for a String of decimal digits without a leading zero. -/
def indexOf (k : M.Str ⊕ M.Sym) : Option M.Math :=
  match k with
  | .inl s =>
    let us := M.strUnits s
    if M.eq (M.seqLen us) (M.ofNat 0) then none
    else if M.lt (M.ofNat 1) (M.seqLen us) && (M.seqGet us (M.ofNat 0)).any (M.eq · (M.ofNat 48)) then none
    else M.seqFoldl (fun acc u => acc.bind fun a =>
      if !M.lt u (M.ofNat 48) && M.lt u (M.ofNat 58) then some (M.add (M.mul a (M.ofNat 10)) (M.sub u (M.ofNat 48)))
      else none) (some (M.ofNat 0)) us
  | .inr _ => none

/-- An object's own property keys as a List: order 1 in creation order; 0 (2) the numeric
indices ascending (descending), then the other keys in creation order. -/
def keysOrdered (o : Val M) (order : M.Math) : Run M (Val M) := do
  let (_, _, ps) ← objCell o
  let ks := M.seqFoldl (fun l k => l ++ [k]) [] (M.propsKeys ps)
  let ks := if M.eq order (M.ofNat 1) then ks else
    let idx := (ks.filterMap fun k => (indexOf k).map (·, k)).mergeSort fun a b => !M.lt b.1 a.1
    let idx := if M.eq order (M.ofNat 2) then idx.reverse else idx
    idx.map (·.2) ++ ks.filter fun k => (indexOf k).isNone
  listOf (ks.map fun | .inl s => .str s | .inr s => .sym s)

/-- OwnPropertyRemove(O, P). -/
def ownRemove (o p : Val M) : Run M (Val M) := do
  let (a, sl, ps) ← objCell o
  match keyOf p with
  | some k => do
    logShape a false
    writeCell a (.object sl (M.propsDel ps k))
    return .enum Known.eUnused
  | none => Run.stop .sortError

end

end Ecma
