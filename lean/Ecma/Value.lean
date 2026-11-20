module

public import Ecma.Model
public import Ecma.Notation.Repr
public import Std.Data.ExtTreeMap.Basic

@[expose] public section

/-!
# Values

The values algorithms compute with (`Val`), a cell of the store (`Cell`: a Record, a List, an object, an
Environment Record), a call of the host as the host-call log records it (`HostCall`), and why a run stops without a result (`Stop`).
-/

namespace Ecma


section
variable (M : Model)

/-- An Abstract Closure literal: its algorithm and its index there. -/
structure CloSite where
  alg : AlgId
  idx : Nat
  deriving Repr, BEq, Inhabited

/-- The values algorithms compute with, by sort. -/
inductive Val where
  /-- an optional parameter not passed; an absent optional child -/
  | absent
  /-- a built-in function's parameter not passed: *undefined* to every use but `is present` (§18) -/
  | missing
  | undefined
  | null
  | bool (b : Bool)
  | str (s : M.Str)
  | sym (s : M.Sym)
  | num (n : M.Num)
  | big (b : M.Big)
  | obj (a : M.Addr)
  | math (m : M.Math)
  | posInf
  | negInf
  | enum (e : EnumId)
  /-- a Record or a List, by identity -/
  | ref (a : M.Addr)
  /-- a Completion Record -/
  | comp (type : EnumId) (value : Val) (target : Val)
  | clo (site : CloSite) (caps : List Val)
  /-- an algorithm: an internal method or a function's behaviour -/
  | alg (a : AlgId)
  | node (n : M.Node)
  /-- the Parse Node of the terminal `t`, at position `i` of `n`'s present right-hand side -/
  | leaf (n : M.Node) (i : Nat) (t : String)
  /-- a terminal symbol, by its text -/
  | term (t : String)
  /-- a type hole's value: the type, with the algorithm, Parse Node and variables it is written in -/
  | ty (t : TyExpr) (self : AlgId) (node : Option M.Node) (env : List Val)
  /-- a condition over bound variables: the condition, the slots it binds, and the algorithm, Parse
  Node and variables it is written in; applied to values, it holds of them or not -/
  | cond (c : Cond) (xs : List Slot) (self : AlgId) (node : Option M.Node) (env : List Val)
  | field (f : FieldId)
  /-- a grammar symbol and its parameters (`true`: `+`) -/
  | nt (n : NtId) (args : List (ParamId × Bool))
  /-- a grammar parameter -/
  | param (p : ParamId)
  /-- a written production: its GL productions (one per presence of its optional symbols) -/
  | prod (ps : List ProdId)
  | sort (s : SortId)
  /-- a phrase's choice of words -/
  | choice (i : Nat)
  /-- a clause, as an `emu-xref` names it -/
  | clause (c : ClauseId)
  /-- an `emu-table`, as an `emu-xref` names it -/
  | table (t : TableId)
  /-- a variable not yet bound: a read of it stops -/
  | unbound
  /-- values held together, without identity: a rule's early errors, before they are a List -/
  | tuple (vs : List Val)

instance : Inhabited (Val M) := ⟨.absent⟩

/-- A value as a use sees it: a parameter not passed is *undefined* (§18). -/
@[inline] def Val.used {M : Model} : Val M → Val M
  | .missing => .undefined
  | v => v

/-- A store cell. -/
inductive Cell where
  | record (kind : SortId) (fs : M.Rec (Val M))
  /-- a List; `origin` is its first index ("indexed 1 through N") -/
  | list (xs : M.Seq (Val M)) (origin : Nat)
  /-- a Data Block (§6.2.9): a sequence of byte values (integers 0 to 255) -/
  | block (bs : M.Bytes)
  /-- a CharSet (§22.2.2.1): a mathematical set of CharSetElements -/
  | charSet (cs : M.CharSet)
  /-- internal slots, and own properties: each an attribute Record of the store -/
  | object (slots : M.Rec (Val M)) (props : M.Props (Val M))
  /-- an Environment Record: its fields, and its bindings by name, each a binding Record of the store -/
  | env (kind : SortId) (fs : M.Rec (Val M)) (binds : M.Props (Val M))

/-- A call of the host, as the host-call log records it. -/
inductive HostCall where
  /-- a host-defined operation: its clause, its arguments, the active script or module at the call
  (§9.4.1), the running execution context's Realm (§9.4), and its answer -/
  | hook (c : ClauseId) (args : List (Val M)) (active : Val M) (realm : Val M) (answer : Val M)
  /-- a choice at a primitive the host decides: its arguments and answer -/
  | choice (q : PrimId) (args : List (Val M)) (answer : Val M)
  /-- the next job the host runs (§9.5): the log position of the call that scheduled it, or none; and
  the milliseconds elapsed by the host's own clock as it takes it -/
  | next (answer : Option Nat) (elapsed : M.Math)
  /-- the host ends its jobs with a promise, generic or timeout job scheduled and not taken: the
  embedding terminates the agent (§9.7) -/
  | terminate
  /-- the host-defined preparation steps of the job scheduled at that log position (§9.5) -/
  | prepare (job : Nat)
  /-- the host-defined cleanup steps of the job scheduled at that log position (§9.5) -/
  | cleanup (job : Nat)
  /-- whether the host performs ClearKeptObjects now (§9.10) -/
  | kept (answer : Bool)
  /-- the objects and symbols whose WeakRefs and cells the host emptied at a job boundary (§9.10.3) -/
  | collect (answer : List (Val M))

/-- A change to an object's shape, as the shape log records it: a property added (`added`), or a
property removed, replaced or its [[Enumerable]] changed, or its [[Prototype]] changed; `before`
is the host's calls before it. -/
structure ShapeChange where
  obj : M.Addr
  added : Bool
  before : List (HostCall M)

/-- Why a run stops without a result. -/
inductive Stop where
  /-- every agent waits and none will be woken -/
  | blocked
  /-- a value of the wrong sort -/
  | sortError
  /-- an Assert, or `!` on an abrupt completion -/
  | assertFailed
  /-- residual prose without an assigned meaning -/
  | residue
  /-- the end of an algorithm without `Return` -/
  | noReturn
  /-- an implementation limit of the host -/
  | implLimit
  /-- the literal text of erratum `e` failing at one of its sites (readings.emu `stops=`) -/
  | erratum (e : ErratumId)
  deriving Repr, BEq, Inhabited

end

end Ecma
