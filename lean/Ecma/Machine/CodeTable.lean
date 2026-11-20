module

public import Ecma.Machine.Code
public import Ecma.Ops.ProgPrim

@[expose] public section

/-!
# The code table

The program as the machine runs it (`Prog'`): the code of each unit (an algorithm, an SDO row, an Abstract Closure
literal, a table's rows, the early-error rules), beside the program's lookups.
-/

namespace Ecma.Machine
open Ecma

/-- The machine's program: the expanded program's static fields, and its units' code. -/
structure Prog' where
  P : Prog
  alg : AlgId → Option Code
  row : SdoId → ProdId → Option Code
  /-- a closure literal's steps, and the step path they are numbered under -/
  clo : CloSite → Option (List Nat × Code)
  /-- a table's rows after its header, for a table step -/
  tstep : TableId → Option (List RowCode)
  /-- the early errors of rule row `i` of a production (`linRow`), and the slots its frame has -/
  earlyRow : ProdId → Nat → Option (Nat × Code)
  /-- the early errors of the rules of some productions (`linOwn`) -/
  earlyOwn : List ProdId → Code
  /-- the early errors of a node of a production and of its descendants (`linTree`) -/
  earlyTree : ProdId → Code
  /-- whether a rule of a production says the bound subject, a child, must cover a nonterminal (`linCovered`) -/
  covered : ProdId → Op
  /-- the tables of a clause, each as its rows after its header -/
  clauseRows : ClauseId → List (List RowCode)

end Ecma.Machine
