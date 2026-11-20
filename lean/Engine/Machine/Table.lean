module

public import Ecma.Machine.Step
public import Engine.Model
public import Engine.Accel.Rows

@[expose] public section

/-!
# The machine's context from an accelerator table

`Ctx.ofTable tab Q H rd chk`: the machine's context over `lin`'s program `Q` whose oracles are the table's lookups by
kind: `lin` keeps algorithm ids, SDO keys, reading keys and loop sites (a loop's condition
and body), so the table's keys need no map.
-/

namespace Engine.Machine
open Ecma Ecma.Machine Engine.Accel.Rows

abbrev F := Engine.Impl

/-- `sl` with the writes `ws`, in order. -/
def writeSlots {M : Model} : List (Slot × Val M) → Array (Val M) → Array (Val M)
  | [], sl => sl
  | (x, v) :: ws, sl => writeSlots ws (sl.setIfInBounds x v)

/-- The engine's shortcuts, consulted before the machine's own transition: an algorithm's call (a run from the
arguments, which may decline), an SDO's and a primitive's (a result from the arguments), and a `Repeat, while` loop's rounds from its head
(the rounds skipped and the slots' writes). -/
structure Accel where
  alg : AlgId → List (Val F) → Option (Run F (Option (Val F))) := fun _ _ => none
  sdo : SdoId → F.Node → List (Val F) → Option (Run F (Val F)) := fun _ _ _ => none
  prim : PrimId → List (Val F) → Option (Run F (Val F)) := fun _ _ => none
  loop : List Nat → Op → Code → Option Nat → Array (Val F) → State F → Option (Run F (Nat × List (Slot × Val F))) :=
    fun _ _ _ _ _ _ => none

/-- The engine's machine: the specification's context, and the shortcuts. -/
structure Setup where
  X : Ctx F
  A : Accel := {}
  /-- the store's ceiling, in cells: a run whose store is past it stops with an implementation limit -/
  maxCells : Option Nat := none

/-- Total payload bytes across all Data Block cells in `h`. -/
def heapBlockBytes (h : @& Array (Cell F)) : Nat :=
  h.foldl (fun acc cell => match cell with | .block b => acc + b.size | _ => acc) 0

/-- The store of `c` is past the set-up's ceiling. -/
@[inline] def Setup.full (E : @& Setup) (c : @& Cfg F) : Bool :=
  match E.maxCells with
  | some n => n < c.s.heap.size
  | none => false

/-- The set-up with a table's entries. -/
def Setup.ofTable (tab : Engine.Accel.Rows.Table F) (Q : Prog') (H : Host F) (rd : ErratumId → Reading) (chk : Bool) : Setup :=
  { X := { prog := Q, H, rd, chk }
    A := { alg := tab.alg, sdo := tab.sdo, prim := tab.prim, loop := tab.loop } }

/-- A power too large to form: its operands' exact power is past `Engine.Model.MathVal.maxBits` bits
(`MathVal.powSize`). -/
def powTooBig (x y : @& Val F) : Bool :=
  let m : Val F → Option Engine.Model.MathVal := fun
    | .math m => some m
    | .big i => some (Engine.Impl.bigVal i)
    | _ => none
  match m x, m y with
  | some a, some e => decide (Engine.Model.MathVal.maxBits < Engine.Model.MathVal.powSize a e)
  | _, _ => false

/-- A Data Block allocation (`NewDataBlock(n)`) whose payload would push the heap past the ceiling. -/
def blockTooBig (E : @& Setup) (c : @& Cfg F) : Bool :=
  match E.maxCells, c.ctl with
  | some n, .invoke (.prim q [.math sz]) =>
    if q == Known.pNewDataBlock then match Engine.Model.MathVal.idx sz with
      | some k => n * 241 < c.s.heap.size * 241 + heapBlockBytes c.s.heap + k
      | none => false
    else false
  | _, _ => false

/-- Whether the stopped parser step at `c` hit the parser's fuel or depth ceiling. -/
def parseExhausted (X : Ctx F) (c : Cfg F) : Bool :=
  match c.ctl with
  | .invoke (.prim q xs) =>
    let annexB := match (hostSections X) c.s with | .ok b _ => b | _ => {}
    if q == Known.pParseGoal then
      let args := match xs.map Val.used with
        | [l, g] => [l, g, .bool false, .bool false, .bool false]
        | [l, g, s, j] => [l, g, s, j, .bool false]
        | us => us
      match args with
      | [.ref a, .nt k ps, .bool strict, .bool json, .bool _] => match F.heapGet c.s.heap a with
        | some (.list cps _) => match cps.mapM (fun | .math m => some m | _ => none) with
          | some src =>
            Engine.isParseExhausted X.rd ⟨annexB, strict, json, k == Ecma.Grammar.NT.Module.ctorIdx⟩ src k ps
          | none => false
        | _ => false
      | _ => false
    else if q == Known.pIsJSONText then match xs with
      | [.ref a] => match F.heapGet c.s.heap a with
        | some (.list cps _) =>
          match cps.mapM (fun | .math m => if Prims.Strings.isPoint (M := F) m then some m else none | _ => none) with
          | some src =>
            Engine.isParseExhausted (fun _ => .literal) ⟨{}, false, false, false⟩ src Ecma.Grammar.NT.JSONText.ctorIdx []
          | none => false
        | _ => false
      | _ => false
    else if q == Known.pCoveredBy then match xs with
      | [.nt k _, .node n] => match (parseCxOf (M := F) annexB n) c.s with
        | .ok cx _ =>
          let src := if k == F.nodeNt n then asIfSource (M := F) n else F.nodeSource n
          Engine.isParseExhausted X.rd cx src k (coverArgs (X.P.params k) n)
        | _ => false
      | _ => false
    else false
  | _ => false

/-- Replace a stopped step outcome with `.implLimit` when `b ()` holds (used for parser exhaustion). -/
@[inline] def orParseLimit (b : Unit → Bool) : Out F → Out F
  | .inr (.stop r) => if b () then .inr (.stop .implLimit) else .inr (.stop r)
  | o => o

/-- One transition of the engine: a stop at a power or Data Block too large to form (an implementation limit); a shortcut
where one answers; else the machine's own (`Ecma.Machine.step`), mapping parser fuel/depth exhaustion to `.implLimit`. An
algorithm's shortcut that declines leaves the state it reached, and the machine's transition goes on from it. A loop's shortcut ends at the test of the
round after those it skips. -/
def stepA (E : Setup) (c : Cfg F) : Out F :=
  let X := E.X
  let alg := fun (a : AlgId) (vs : List (Val F)) => match E.A.alg a vs with
    | some r => bindR c r fun o c => match o with
      | some v => c.to (.val v)
      | none => step X c
    | none => step X c
  let tooBig := match c.ctl, c.frames with
    | .val y, f :: _ => match f.konts with
      | .args (.leaf (.bin .pow)) [x] [] :: _ => powTooBig x y
      | _ => false
    | _, _ => false
  if tooBig || blockTooBig E c then .inr (.stop .implLimit) else
  match c.ctl with
  | .invoke (.alg a vs) => alg a vs
  | .invoke (.phrase p nd vs) => match X.P.phrase p with
    | .alg a => match nd, X.P.alg a with
      | some _, some _ => alg a vs
      | _, _ => step X c
    | _ => step X c
  | .invoke (.sdo s nd vs) =>
    if s == Known.sdoEarlyErrors then step X c else
    match E.A.sdo s nd vs with
    | none => step X c
    | some r => leafV c r
  | .invoke (.prim q xs) => match E.A.prim q xs with
    | some r => leafV c r
    | none =>
      if q == Known.pParseGoal || q == Known.pIsJSONText || q == Known.pCoveredBy then
        orParseLimit (fun _ => parseExhausted X c) (step X c)
      else step X c
  | .loop (.spend back) l => match l.it with
    | .while_ t => match E.A.loop l.p t l.body none c.top.slots c.s with
      | some run => bindR c run fun (g, ws) c =>
        loopTest (c.mapTop fun f => { f with slots := writeSlots ws f.slots }) { l with r := l.r + g + 1 } t
      | none => step X c
    | _ => step X c
  | _ => step X c

end Engine.Machine
