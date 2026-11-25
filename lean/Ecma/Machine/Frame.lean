module

public import Ecma.Machine.Code

@[expose] public section

/-!
# Frames

A frame of the machine: the algorithm, its Parse Node, slots, step path and continuations. Each call is a frame;
each pending part of an operand tree or an instruction is a continuation on its frame (`Kont`). A suspended
execution context's frames are part of the state.
-/

namespace Ecma.Machine
open Ecma

variable {M : Model}

/-- A call on a checked receiver, awaiting its arguments. -/
inductive Target (M : Model) where
  | sdo (s : SdoId) (nd : M.Node)
  | alg (a : AlgId) (pre : List (Val M))
  | cmethod (m : MethodId) (r : Val M)
  | clo (site : CloSite) (caps : List (Val M))

/-- What an evaluated operand list is for. -/
inductive Fin (M : Model) where
  | leaf (k : Leaf)
  | call (k : CallK)
  /-- the receiver of `k`, checked; then the arguments `args` -/
  | recv (k : OnK) (args : List Op)
  | target (t : Target M)
  /-- the subject bound while `body` runs -/
  | bind (body : Op)
  /-- every element of the List passes `t` -/
  | all (t : Op)
  /-- the value as a Completion Record (`retConv true`) -/
  | retC
  | let_ (x : Slot)
  | drop
  | ret
  | throw
  | setField (f : FieldId)
  /-- the List or Data Block and index checked, then `e` -/
  | setIndex (e : Op)
  | setIndexVal (a : M.Addr) (xs : M.Seq (Val M)) (j : M.Math)
  | setBlockVal (a : M.Addr) (j : M.Math)
  | br (t e : Code)
  | assert
  | assertAlways
  /-- `Assert: If c, then d.`: `c`'s answer, then `d` asserted -/
  | assertIf (d : Op)
  | ctxPush
  | ctxRemove
  | ctxTopIs
  /-- the iterator's operands, then its first state: a loop at step path `p`, binding `x` each round -/
  | loopInit (x : Option Slot) (it : Iter) (p : List Nat) (body : Code)
  /-- the context and the value: a transfer passing the value; resumed, its Completion Record to `x` -/
  | transfer (x : Option Slot)
  /-- the Completion Record the run is resumed with: to `x`, or to the state's `resumed` -/
  | resumed (x : Option Slot)
  /-- a tuple, added to the tuple in slot `acc` -/
  | tupInto (acc : Slot)
  /-- the Parse Node `p must cover k` reparses -/
  | cover (acc : Slot) (k : NtId) (err : Op)
  /-- the completion of the Job the host took at log position `k` (§9.5): then its cleanup -/
  | jobRan (clear : Option AlgId) (k : Nat) (job : Val M)
  /-- ClearKeptObjects' result, where the host performed it after a Job that completed with `v`: then the next Job -/
  | jobKept (clear : Option AlgId) (v : Val M) (job : Val M)
  /-- an algorithm of the host's own has run as a Job (`Host.first`, `Host.idle`): its cleanup (`Host.idleEnd`),
  then the agent's Jobs again unless the host ends them -/
  | idleRan (clear : Option AlgId)

/-- A state component a call binds while it runs: the Parse Nodes being evaluated, the
arguments Lists passed. -/
inductive Scope (M : Model) where
  | nodes (outer inner : List M.Node)
  | passed (outer inner : List (Val M))

/-- A loop's iterator state: where the next round is. -/
inductive IterSt (M : Model) where
  /-- `Repeat` and its `while`/`until` forms -/
  | plain
  /-- the List at `a`, its next index, from its end when `rev` -/
  | each (a : M.Addr) (i : M.Math) (rev : Bool)
  /-- the next integer, the bounds as included -/
  | range (i lo hi : M.Math) (desc : Bool)
  /-- the keys' List at `a`, its next index -/
  | keys (a : M.Addr) (i : M.Math)
  /-- the next index, the List's length at the start -/
  | idx (i n : M.Math)
  /-- the Parse Node, its next symbol's position, its next child's index -/
  | kids (nd : M.Node) (i : Nat) (j : M.Math)
  /-- the next round's number, the count -/
  | times (i n : M.Math)

/-- A running loop: the slot each round binds, the iterator, the loop step's path, the body, the iterator's
state and the rounds begun. -/
structure Loop (M : Model) where
  x : Option Slot
  it : Iter
  p : List Nat
  body : Code
  st : IterSt M
  r : Nat

/-- A loop's control point: the rounds' count set (`rounds`), a round begun
(`spend`; `back`: then the jump to the loop's head), the jump (`jmp`), the head (a `*Round`, a `while` test or
the body). -/
inductive Phase where
  | rounds
  | spend (back : Bool)
  | jmp
  | round

/-- A continuation: what the frame does with the next value. -/
inductive Kont (M : Model) where
  /-- the code after the running instruction -/
  | seq (rest : Code)
  /-- the operands evaluated (`done`, innermost first) and left (`todo`), then `f` -/
  | args (f : Fin M) (done : List (Val M)) (todo : List Op)
  /-- a conjunction's (`conj`) or disjunction's operands left, each a Boolean -/
  | junct (conj : Bool) (cs : List Op)
  /-- an `andT`'s operands left, each a Boolean, then its tail `t` -/
  | juncT (cs : List Op) (t : Op)
  /-- the List's elements left, each passing `t` -/
  | all (t : Op) (xs : List (Val M))
  /-- the subject `v`, bound while the operand above runs -/
  | bind (v : Val M)
  /-- a scoped call's return: the scope's component back to its outer value -/
  | scope (sc : Scope M)
  /-- the loop's body running: then the next round (an `until` loop's test) -/
  | loop (l : Loop M)
  /-- the loop's test (`while`, `until`) or filter, a Boolean -/
  | test (l : Loop M)
  /-- a table step's row whose key cell is a type: its answer for `key`; true, its result cell `res` (step code
  `rc`) in the variables `env`, else the rows `rs` -/
  | tstep (a : AlgId) (nd : Option M.Node) (tb : Table) (key : Val M) (env : List (Val M)) (res : CellBody)
      (rc : RowCode) (rs : List (List (Option CellBody) × RowCode))

/-- A frame's kind. -/
inductive Kind where
  | steps (rc boundary used : Bool)
  | eval

/-- A frame: the algorithm (an SDO row's id, a closure's owner), its Parse Node, slots, step path and
continuations (innermost first), and for an Abstract Closure's steps the closure literal's index. -/
structure Frame (M : Model) where
  alg : AlgId
  node : Option M.Node
  slots : Array (Val M)
  kind : Kind
  path : List Nat
  konts : List (Kont M)
  clo : Option Nat

end Ecma.Machine
