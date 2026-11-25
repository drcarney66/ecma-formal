module

public import Ecma.Value
public import Ecma.Notation.Tables
public import Ecma.Notation.Early

@[expose] public section

/-!
# The machine's code

The machine's program: per unit (an algorithm, an SDO row, an Abstract Closure literal, a table step's rows) a
linear statement list with site markers, over operand trees. `lin` (`Ecma.Lower.Lin`) writes it from the expanded
program (`Src.expanded`).

- Operand trees (`Op`) keep the steps' evaluation order: a leaf's or a call's operands left to right, then the
  operation; a receiver (`Op.on`: an SDO's Parse Node, an internal method's object, a method's receiver, an
  applied closure) is evaluated and checked before the arguments. Conditions, predicates and types are Boolean
  trees: `and`/`or` short-circuit, each operand checked a Boolean; a predicate's or a type's subject is bound
  by `bind` and read by `bound`, the innermost binding.
- One leaf form (`Op.leaf`): `Leaf` names the shared leaf function; calls (`Op.call`, `Op.on`) re-enter the
  machine.
- Statements (`Ins`): `site p` where the machine enters a step (`.node`) or an `Else if`/`Else` step (`.arm`) at
  path `p`; `If` as `br`; every loop form as `loop` over one iterator (`Iter`); an erratum's readings with
  their steps as the reading oracle's key; a definition reading (the overlay's one reading of prose steps) as its
  steps' code, with no choice.
- What the machine stops at as residue is `residue form` with the form's name: the program's own residue, and the
  forms the code has none of (phrase calls, binding conditions, choices).
-/

namespace Ecma.Machine
open Ecma

/-- A constant operand. -/
inductive Const where
  | val (v : ValLit)
  | math (sg : Sign) (m : Mag)
  | enum (e : EnumId)
  | param (p : ParamId)
  | fieldName (f : FieldId)
  | nt (k : NtId) (as : List (ParamId × Bool))
  | prod (ps : List ProdId)
  /-- a code unit or code point, a mathematical value -/
  | nat (n : Nat)
  | str (s : String)
  | term (s : String)
  | clause (c : ClauseId)
  | table (t : TableId)
  | alg (a : AlgId)
  | data (d : DataLit)
  deriving BEq, Inhabited

/-- A leaf operation: a shared leaf function of its operands' values, run once. -/
inductive Leaf where
  /-- `readField` -/
  | field (f : FieldId)
  | q
  | bang
  | un (o : UnOp)
  | bin (o : BinOp)
  /-- `relOp`, a Boolean -/
  | rel (o : RelOp)
  /-- two Booleans' conjunction: an interval's bounds -/
  | both
  | index
  | list
  | record (k : Option SortId) (fs : List FieldId)
  /-- the subject, `used`, is (`neg`: is not; `nei`: is neither) one of the rest -/
  | isVal (neg nei : Bool)
  /-- a membership's answer under `is`, `is not` (`neg`) or `is neither` (`nei`) -/
  | isTy (neg nei : Bool)
  /-- `Val.used` -/
  | used
  | childOf (nt : NtId)
  /-- a Boolean, else a sort error -/
  | toBool
  | intrinsic (i : IntrinsicId)
  | tyNt (k : NtId)
  /-- the operands held together (`Val.tuple`) -/
  | tuple
  /-- two tuples' values, in order -/
  | tupCat
  /-- whether a tuple holds no value -/
  | tupEmpty
  /-- a new List of a tuple's values -/
  | tupList
  /-- whether the first operand is a Parse Node, and the same one as the second -/
  | sameNode
  /-- whether the operand is a nonterminal's Parse Node (not a terminal's) -/
  | isNode
  /-- the first operand where the second is *true*, else a sort error -/
  | guard
  deriving BEq, Inhabited

/-- A call after its operands. -/
inductive CallK where
  | alg (a : AlgId)
  | prim (p : PrimId)
  /-- an algorithm at the frame's Parse Node -/
  | callAt (a : AlgId)
  /-- the operand's membership in a sort -/
  | sort (s : SortId)
  /-- the subject (second) against a value (first): a sort's test where it is a sort, else sameness -/
  | tyEq
  /-- a table step's row for the key, in the frame's variables -/
  | tstep (t : TableId)
  /-- the early errors of rule row `i` of production `prod`, at the frame's Parse Node -/
  | earlyRow (prod : ProdId) (i : Nat)
  /-- the early errors of the rules of the productions `ps`, at the frame's Parse Node -/
  | earlyOwn (ps : List ProdId)
  /-- whether a rule of the frame's Parse Node's production says the operand, a child, must cover a nonterminal -/
  | covered
  deriving BEq, Inhabited

/-- A call on a receiver, evaluated and checked before the arguments. -/
inductive OnK where
  /-- SDO `s` at the receiver, a Parse Node -/
  | sdo (s : SdoId)
  /-- the receiver's `[[m]]`, an algorithm, on the receiver and the arguments -/
  | imethod (m : FieldId)
  /-- concrete method `m` of the receiver's kind -/
  | cmethod (m : MethodId)
  /-- the receiver, a closure or an algorithm, applied -/
  | apply
  /-- the early errors of the receiver, a Parse Node, and of its descendants -/
  | earlyTree
  deriving BEq, Inhabited

/-- An operand tree. -/
inductive Op where
  | const (c : Const)
  /-- the slot's value, read: an unbound slot stops -/
  | var (x : Slot)
  /-- the slot's value as a binder: an unbound slot is absent -/
  | bnd (x : Slot)
  /-- the frame's Parse Node -/
  | node
  /-- a child of the frame's Parse Node (`evChild`) -/
  | child (k : Nat) (nt : NtId)
  /-- the Completion Record the running computation was resumed with -/
  | resumed
  /-- the frame's closure literal `site`, capturing slots `caps` -/
  | closure (site : Nat) (caps : List Slot)
  /-- the value the innermost `bind` holds -/
  | bound
  | leaf (k : Leaf) (args : List Op)
  | call (k : CallK) (args : List Op)
  | on (k : OnK) (recv : Op) (args : List Op)
  /-- `e`'s value bound while `body` runs -/
  | bind (e body : Op)
  | and (cs : List Op)
  | or (cs : List Op)
  /-- `cs`, each a Boolean, all true, then `t` in tail position, its value the answer: a sort's adjectives,
  then the sort -/
  | andT (cs : List Op) (t : Op)
  /-- every element of the List `l` (bound in turn) passes `t`; false for a value that is no List -/
  | all (l t : Op)
  | stop (r : Stop)
  | residue (form : String)
  deriving BEq, Inhabited

/-- A loop's iterator: what each round binds, and when the loop ends. -/
inductive Iter where
  /-- `Repeat` -/
  | rep
  /-- `Repeat, while c` -/
  | while_ (c : Op)
  /-- `Repeat, until c`: the test after each round -/
  | until_ (c : Op)
  /-- a List's elements, from its end when `rev` -/
  | each (l : Op) (rev : Bool)
  /-- the integers between the bounds -/
  | range (lo hi : Op) (loIncl hiIncl desc : Bool)
  /-- an object's own property keys in order `order`, those passing `filter` -/
  | keys (o : Op) (order : Nat) (filter : Op)
  /-- a List's indices -/
  | idx (l : Op)
  /-- a Parse Node's children: the frame's, or `e`'s -/
  | kids (e : Option Op)
  /-- `Repeat n times` -/
  | times (n : Op)
  deriving Inhabited

/-- A statement. -/
inductive Ins where
  /-- the machine enters the step at path `p` -/
  | site (p : List Nat)
  | let_ (x : Slot) (e : Op)
  | eval (e : Op)
  | setField (f : FieldId) (o e : Op)
  /-- `Set l[i] to e`: the List and index checked before `e` -/
  | setIndex (l i e : Op)
  /-- `Return e`, a Completion Record where the frame declares one -/
  | ret (e : Op)
  /-- `Return.` -/
  | retUnused
  | throw (e : Op)
  | br (c : Op) (t e : List Ins)
  /-- `Assert: c`, in checked mode -/
  | assert (c : Op)
  /-- `Assert: c`, checked in every mode -/
  | assertAlways (c : Op)
  /-- `Assert: If c, then d.`, in checked mode -/
  | assertIf (c d : Op)
  /-- a loop at step path `p`, its iterator binding `x` -/
  | loop (x : Option Slot) (it : Iter) (p : List Nat) (body : List Ins)
  | ctxPush (e : Op)
  | ctxRemove (e : Op)
  /-- the running execution context is `e`'s value -/
  | ctxTopIs (e : Op)
  /-- a transfer passing `v` from context `ctx`, the resumption's Completion Record to `x` -/
  | transfer (x : Option Slot) (ctx v : Op)
  /-- `p must cover k`: `p`'s value, a Parse Node, reparsed as `k`; the reparse's early errors, or `err`'s value
  where it has no parse, added to the tuple in slot `acc` -/
  | cover (acc : Slot) (p : Op) (k : NtId) (err : Op)
  | stop (r : Stop)
  | residue (form : String)
  deriving Inhabited

abbrev Code := List Ins

/-- A table cell as the values it holds: an expression's, a name's String, the operation it names, a field
(`vals`); each line's of a cell of lines; a cell inside markup (`<dfn>`, code, a link); or none (a step, a type,
a signature, prose). -/
inductive CellCode where
  | vals (os : List Op)
  | lines (cs : List CellCode)
  | wrap (c : CellCode)
  | other
  deriving Inhabited

/-- A sort's adjectives' memberships of the bound subject in turn, then the sort's in tail position. -/
def sortsOp (mods : List SortId) (s : SortId) : Op :=
  match mods with
  | [] => .call (.sort s) [.bound]
  | ms => .andT (ms.map fun m => .call (.sort m) [.bound]) (.call (.sort s) [.bound])

/-- A table step's row: its key's type test (a type cell, the key bound) and its result step (a step cell);
the machine reads the other cells as data. -/
structure RowCode where
  key : Option Op := none
  res : Option Code := none
  /-- the row's cells by column, as the values they hold -/
  cells : List (Option CellCode) := []
  deriving Inhabited

end Ecma.Machine
