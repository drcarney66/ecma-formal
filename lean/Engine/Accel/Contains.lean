module

public import Ecma.Program

@[expose] public section

/-!
# Contains and ComputedPropertyContains, natively: the walk

`accelSdo` answers the SDOs Contains (§8.5.1) and ComputedPropertyContains (§8.5.2) by a walk of the
Parse Node: each row by what its body does (`behs`), Contains' default definition under the
ContainsAwaitCover readings (`dfltShape`), a chain production's child. The answer is a Boolean in the
same state, as the knot's: its walk allocates nothing and `atSdo` restores the Parse Nodes being
evaluated. The walk declines (`none`) at a cover's reparse, a body it does not recognize, a missing
child, a symbol other than a nonterminal without arguments or a terminal, and beyond `depthMax`
nested calls or children. `behs` and `dfltShape` are the classification of the program's rows
(`Spec.Accel.Contains`, which TestContains checks equal), as data, so that the walk does not read the program.
-/

namespace Engine.Accel.Contains

open Ecma

variable {M : Model}

/-- A grammar symbol the walk compares: a nonterminal without arguments, or a terminal. -/
inductive Sym where
  | nt (k : NtId)
  | term (t : String)
  deriving BEq, DecidableEq, Repr

/-- The symbol a value is. -/
def symOf : Val M → Option Sym
  | .nt k [] => some (.nt k)
  | .term t => some (.term t)
  | _ => none

/-- What a row's body does, for the symbol at the row's Parse Node. -/
inductive Beh where
  /-- returns `b` -/
  | ret (b : Bool)
  /-- not recognized (a cover's reparse among them) -/
  | decline
  /-- SDO `s` of child `k` for each `(s, k)` in turn: *true* at the first *true*, else *false* -/
  | any (cs : List (SdoId × NtId))
  /-- *false* unless the symbol is one of `ss`, else `b` -/
  | arrow (ss : List Sym) (b : Beh)
  /-- *true* if the symbol is `v`, else `b` -/
  | isSym (v : Sym) (b : Beh)
  /-- `ClassTail : ClassHeritage? { ClassBody }`: the heritage `h`, the body `b`, CPC's SDO `s` -/
  | classTail (h b : NtId) (s : SdoId)
  deriving BEq, DecidableEq, Repr

/-- The SDO Contains. -/
def sdoC : SdoId := 23

/-- The SDO ComputedPropertyContains. -/
def sdoCPC : SdoId := 24

/-- The symbols of the arrow functions' rows' `If symbol is not one of …`. -/
def arrowSyms : List Sym := [.nt 140, .nt 138, .nt 144, .term "super", .term "this"]

/-- What each row of Contains and ComputedPropertyContains does, by id. -/
def behs : List (AlgId × Beh) :=
  [(⟨322, 1⟩, .ret false), (⟨322, 2⟩, .classTail 269 270 24), (⟨322, 3⟩, .ret false),
   (⟨322, 4⟩, .arrow arrowSyms (.any [(23, 251), (23, 252)])), (⟨322, 5⟩, .decline),
   (⟨322, 6⟩, .arrow arrowSyms (.any [(23, 284)])), (⟨322, 7⟩, .arrow arrowSyms .decline),
   (⟨322, 8⟩, .isSym (.nt 255) (.any [(24, 255)])), (⟨322, 9⟩, .ret false), (⟨322, 10⟩, .any [(23, 137)]),
   (⟨322, 11⟩, .isSym (.term "super") (.ret false)), (⟨322, 12⟩, .any [(23, 143)]), (⟨322, 13⟩, .ret false),
   (⟨322, 14⟩, .any [(23, 149)]),
   (⟨323, 0⟩, .ret false), (⟨323, 1⟩, .any [(23, 130)]), (⟨323, 2⟩, .any [(24, 274)]),
   (⟨323, 3⟩, .any [(24, 274)]), (⟨323, 4⟩, .any [(24, 274)]), (⟨323, 5⟩, .any [(24, 271), (24, 272)]),
   (⟨323, 6⟩, .ret false), (⟨323, 7⟩, .ret false), (⟨323, 8⟩, .any [(24, 274)]), (⟨323, 9⟩, .any [(24, 274)])]

/-- Contains' default definition: its id, the ContainsAwaitCover production `[672]` and nonterminal `|AwaitExpression|`. -/
def dfltShape : Option (AlgId × List ProdId × NtId) := some (⟨322, 0⟩, [672], 282)

/-- What the walk reads of a program: an SDO's row at a production (its id), an SDO's default
algorithm when it has a meaning, a production's terminals by position and its chain nonterminal. -/
structure Tab where
  row : SdoId → ProdId → Option AlgId
  dflt : SdoId → Option AlgId
  terms : ProdId → List (Nat × String)
  chain : ProdId → Option NtId

/-- The nested calls, and the children of a node, the walk follows before it declines. -/
def depthMax : Nat := 2 ^ 14

section Walk
variable (T : Tab) (sym : Sym) (rec : SdoId → M.Node → Option Bool) (nd : M.Node)

/-- SDO `s` at child `k` of `nd` (`|k|` in a row: absent, a sort error). -/
def atChild (s : SdoId) (k : NtId) : Option Bool :=
  match M.nodeChild nd k 0 with
  | some (some c) => rec s c
  | _ => none

/-- The calls `cs` at `nd`'s children in turn: *true* at the first *true*. -/
def anyAt : List (SdoId × NtId) → Option Bool
  | [] => some false
  | (s, k) :: cs => match atChild rec nd s k with
    | some true => some true
    | some false => anyAt cs
    | none => none

/-- A row's body at `nd`. -/
def runBeh : Beh → Option Bool
  | .ret b => some b
  | .decline => none
  | .any cs => anyAt rec nd cs
  | .arrow ss b => if ss.contains sym then runBeh b else some false
  | .isSym v b => if v == sym then some true else runBeh b
  | .classTail h b s =>
    let present := match M.nodeChild nd h 0 with
      | some (some _) => true
      | _ => false
    if sym == .nt b then some true
    else if sym == .nt h then some present
    else
      let inH := if present then atChild rec nd sdoC h else some false
      match inH with
      | some true => some true
      | some false => atChild rec nd s b
      | none => none

/-- Contains' default definition at `nd`: each child in turn (a terminal's text at its position, else
the next child node), *true* if it is an instance of the symbol, or (`aw`, the productions and
nonterminal of the test262 and proposed readings) if the symbol is that nonterminal and `nd` one of those productions,
else, for a child node, if it Contains the symbol; past `depthMax` children, `none`. -/
def dfltAt (aw : Option (List ProdId × NtId)) : Option Bool :=
  let ts := T.terms (M.nodeProd nd)
  let await := match aw with
    | some (ps, k) => sym == .nt k && ps.contains (M.nodeProd nd)
    | none => false
  let rec go : Nat → Nat → List M.Node → Option Bool
    | 0, _, _ => none
    | f + 1, i, ks => match ts.lookup i, ks with
      | some t, _ => if sym == .term t || await then some true else go f (i + 1) ks
      | none, c :: ks =>
        if sym == .nt (M.nodeNt c) || await then some true
        else match rec sdoC c with
          | some true => some true
          | some false => go f (i + 1) ks
          | none => none
      | none, [] => some false
  let ks := (M.seqFoldl (fun acc c => c :: acc) [] (M.nodeKids nd)).reverse
  go depthMax 0 ks

/-- SDO `s` at `nd`, its nested calls by `rec`: its row, else its default, else at the child of a
chain production (`knotSdo`). -/
def step (s : SdoId) : Option Bool :=
  if !(s == sdoC || s == sdoCPC) then none else
  match T.row s (M.nodeProd nd) with
  | some a => match behs.lookup a with
    | some b => runBeh sym rec nd b
    | none => none
  | none => match T.dflt s with
    | some a => match dfltShape with
      | some (d, ps, k) =>
        if a == d then
          dfltAt T sym rec nd (some (ps, k))
        else none
      | none => none
    | none => match T.chain (M.nodeProd nd) with
      | some k => match M.nodeChild nd k 0 with
        | some (some c) => rec s c
        | _ => none
      | none => none

end Walk

/-- The walk, at most `n` nested calls deep. -/
def walk (T : Tab) (sym : Sym) : Nat → SdoId → M.Node → Option Bool
  | 0, _, _ => none
  | n + 1, s, nd => step T sym (walk T sym n) nd s

/-- The program's tables for `AccelContains`: its rows' ids, its defaults that have a meaning, its
terminals and chain productions. -/
def tabOf (P : Prog) : Tab :=
  { row := fun s p => (P.row s p).map (·.id)
    dflt := fun s => (P.sdoDefault s).filter fun a => (P.alg a).isSome
    terms := P.terms
    chain := P.chain }

/-- Contains and ComputedPropertyContains of a symbol at a Parse Node, over `T`:
a Boolean in the same state, or `none`. -/
def accelSdo (T : Tab) (s : SdoId) (nd : M.Node) (vs : List (Val M)) :
    Option (Run M (Val M)) :=
  match vs with
  | [v] => (symOf v).bind fun sym => (walk T sym depthMax s nd).map fun b => Run.pure (.bool b)
  | _ => none

end Engine.Accel.Contains
