module

public import Ecma.Ops.ProgPrim
public import Ecma.Lower.PhraseCalls

@[expose] public section

/-!
# A program with its phrases as calls

`Prog.calls`: the program with its algorithms', SDO rows', early-error rules' and tables' (by id and by clause) phrases as calls
(`CallsCfg.sites` over the program's phrase meanings): an SDO row's steps at a Parse Node, every closure and table
step off one; a phrase of an algorithm that reads its node is its call at the node (`Expr.callAt`) there, and stays
off one. A subject-first call lifts out of a type one of whose sorts' tests rejects a non-Object first
(`Prog.undefOut`).
-/

namespace Ecma

variable (P : Prog)

/-- Whether sort `k`'s test is an algorithm whose first step is `If v is not an Object, return false`, Object a
value sort. -/
def Prog.objTest (k : SortId) : Bool :=
  (P.sortDef Known.sObject).isNone && match P.sortDef k with
  | some d => !d.record && match d.test with
    | .alg a => match (P.alg a).bind (·.body.head?) with
      | some (.mk _ (.if_ (.preds (.var 0) (.isTy true f [.sort _ [] s _]) [])
          (.inline (.ret (some (.val .false)))) [] none)) => s == Known.sObject && f != .neither
      | _ => false
    | _ => false
  | none => false

/-- The types `a mods s` whose test is false on *undefined*: one of their sorts' tests rejects a non-Object. -/
def Prog.undefOut (mods : List SortId) (s : SortId) : Bool := (mods ++ [s]).any P.objTest

/-- An algorithm of `P` whose steps read no Parse Node, nor do its phrases' algorithms' to depth `d`; a missing
one reads none; `false` where unsure. -/
def Prog.algNodeFree : Nat → AlgId → Bool
  | 0, a => (P.alg a).isNone
  | d + 1, a => match P.alg a with
    | some g => g.nodeFree P.phrase (Prog.algNodeFree d)
    | none => true

/-- An algorithm of `P` whose steps may read their Parse Node (not `Prog.algNodeFree` to depth 4). -/
def Prog.nodeAlg (a : AlgId) : Bool := !P.algNodeFree 4 a

/-- The rewrite's configuration over `P`'s phrase meanings, at a Parse Node or not; a phrase of a node-reading
algorithm runs it at the node. -/
def Prog.callsCfg (atNode : Bool) : CallsCfg := ⟨P.phrase, atNode, P.nodeAlg, P.undefOut⟩

/-- An SDO row with its phrases as calls: its steps at a Parse Node, its closures off one. -/
def SdoRow.calls (r : SdoRow) : SdoRow :=
  { r with body := Node.rwL (Prog.callsCfg P true).sites r.body,
           closures := r.closures.map (CloLit.rw (Prog.callsCfg P false).sites) }

/-- The program with its algorithms', SDO rows', early rules' and tables' phrases as calls. -/
def Prog.calls : Prog :=
  { P with
    alg := fun a => (P.alg a).map (Alg.rw (Prog.callsCfg P false).sites)
    row := fun s k => (P.row s k).map (SdoRow.calls P)
    rowOf := fun a => (P.rowOf a).map (SdoRow.calls P)
    early := fun k => (P.early k).map (EarlyRow.rw (Prog.callsCfg P true).sites)
    table := fun t => (P.table t).map (Table.rw (Prog.callsCfg P false).sites)
    clauseTables := fun c => (P.clauseTables c).map (Table.rw (Prog.callsCfg P false).sites) }

end Ecma
