module

public import Engine.Parse.Keys
public import Ecma.Grammar.Notation
public import Ecma.Grammar.Gen.Readings
public import Std.Data.HashMap
public import Std.Data.HashSet

@[expose] public section

/-!
# The parser's interface: the caller's Parse Nodes, its code point classes, the outcomes

`Builder N` is how the parser makes the caller's Parse Nodes (GL's production id with its
presence mask, the nonterminal, the parameters, the code point span, one child entry per written
nonterminal item, the span's code points) and reads them back, with the code point classes the caller's
instance gives the grammar's primitives. GL's rules and production ids are looked up through
tables built on first use. The alternatives in effect follow the parse context (`Ctx`): Annex B's
overlays and their conditions.
-/

namespace Engine.Parse

open Ecma.Grammar

deriving instance DecidableEq for NT

/-- The caller's Parse Nodes and code point classes. -/
structure Builder (N : Type) where
  node : (stamp lo hi prod nt : Nat) → List Param → Array (Nat × Option N) → Subarray Nat → N
  prod : N → Nat
  nt : N → Nat
  args : N → List Param
  span : N → Nat × Nat
  kids : N → Array (Nat × Option N)
  stamp : N → Nat
  text : N → Array Nat
  /-- `<USP>`: general category Space_Separator -/
  usp : Nat → Bool
  /-- ID_Start, ID_Continue; none where the instance does not give them -/
  idStart : Option (Nat → Bool)
  idContinue : Option (Nat → Bool)

/-- Why a parse gave neither a Parse Node nor a complete "no parse". -/
inductive Stop where
  | fuel
  | depth
  | unimplemented (what : String)
  | nonAsciiId
  | check (what : String)
  | ambiguous (what : String)
  deriving Repr, BEq, Inhabited

/-- A Parse Node, no parse (after a complete decision of the grammar), or a stop. -/
inductive Outcome (N : Type) where
  | ok (n : N)
  | noParse
  | stop (s : Stop)

/-- The parameters in declaration order. -/
def allParams : List Param :=
  [.Sep, .Yield, .Await, .In, .Tagged, .Return, .Default, .Pattern, .Using, .Extended,
   .UnicodeMode, .UnicodeSetsMode, .NamedCaptureGroups]

/-- A goal's parameters: those its arguments set, in declaration order. -/
def paramsOfArgs (args : List (Nat × Bool)) : List Param :=
  allParams.filter fun p => args.contains (p.ctorIdx, true)

/-- A parameter set as a bit mask. -/
def paramBits (ps : List Param) : Nat := ps.foldl (fun b p => b ||| (1 <<< p.ctorIdx)) 0

/-- GL's rules by grammar and left-hand side. -/
@[irreducible] def ruleTable : Thunk (Std.HashMap (Nat × Nat) Rule) := Thunk.mk fun _ =>
  Gen.grammars.foldl (init := {}) fun m (g, rs) =>
    rs.foldl (init := m) fun m r => m.insert (g.ctorIdx, r.lhs.ctorIdx) r

/-- GL's production ids by grammar, left-hand side, written alternative and presence mask. -/
@[irreducible] def prodTable : Thunk (Std.HashMap (Nat × Nat × Nat × List Bool) Nat) := Thunk.mk fun _ =>
  prods.zipIdx.foldl (init := {}) fun m (o, i) => match o with
    | some p => m.insert (p.grammar.ctorIdx, p.rule.lhs.ctorIdx, p.alt, p.mask) i
    | none => m

/-- The pinned definition of nonterminal `n` in grammar `g`: `g`'s, or its base grammar's, with the
grammar it is written in. -/
def pinnedIn (g : GrammarId) (n : Nat) : Option (GrammarId × Rule) :=
  match ruleTable.get[(g.ctorIdx, n)]? with
  | some r => some (g, r)
  | none => baseGrammar g >>= fun b => (ruleTable.get[(b.ctorIdx, n)]?).map ((b, ·))

/-- The Annex B overlays' definitions by grammar overlaid and left-hand side, in spec order, with
their sections, modes and conditions. -/
@[irreducible] def overlayTable : Thunk (Std.HashMap (Nat × Nat) (List (Rule × AnnexB × OverlayMode × OverlayCond))) :=
  Thunk.mk fun _ => Gen.blocks.foldl (init := {}) fun m b => match b.kind with
    | .overlay s md c => b.rules.foldl (init := m) fun m r =>
      let k := ((overlayGrammar s).ctorIdx, r.lhs.ctorIdx)
      m.insert k (m.getD k [] ++ [(r, s, md, c)])
    | _ => m

/-- A definition of nonterminal `n` in grammar `g`: the pinned one, or an Annex B overlay's (whether
or not it is in effect). -/
def ruleIn (g : GrammarId) (n : Nat) : Option (GrammarId × Rule) :=
  match pinnedIn g n with
  | some x => some x
  | none => ((overlayTable.get[(g.ctorIdx, n)]?).bind List.head?).map fun (r, _) => (.annexB, r)

/-- The overlays' definitions of `n` in effect on grammar `g` in context `cx` (`GL.overlays`), with
their modes. -/
def overlaysIn (cx : Ctx) (g : GrammarId) (n : Nat) : List (Rule × OverlayMode) :=
  if !cx.annexB.any then []
  else ((overlayTable.get[(g.ctorIdx, n)]?).getD []).filterMap fun (r, s, m, c) =>
    if cx.annexB.has s && condHolds cx c then some (r, m) else none

/-- B.1.2's restated nonterminals by grammar overlaid, with the overlay's condition. -/
@[irreducible] def orderedTable : Thunk (Std.HashMap Nat (List (Nat × OverlayCond))) :=
  Thunk.mk fun _ => Gen.blocks.foldl (init := {}) fun m b => match b.kind with
    | .overlay .regExpPatterns _ c => b.rules.foldl (init := m) fun m r =>
      let g := (overlayGrammar .regExpPatterns).ctorIdx
      m.insert g (m.getD g [] ++ [(r.lhs.ctorIdx, c)])
    | _ => m

/-- The nonterminals whose alternatives B.1.2 orders on grammar `g` in context `cx` (`GL.orderedNts`). -/
def orderedIn (cx : Ctx) (g : GrammarId) : List Nat :=
  if !cx.annexB.any || !cx.annexB.has .regExpPatterns then []
  else ((orderedTable.get[g.ctorIdx]?).getD []).filterMap fun (n, c) => if condHolds cx c then some n else none

/-- The production ids of a left-capturing parenthesis (`GL.capturingIds`). -/
@[irreducible] def capturingTable : Thunk (Std.HashSet Nat) := Thunk.mk fun _ =>
  prods.zipIdx.foldl (init := {}) fun m (o, id) => match o with
    | some p =>
      if (p.rule.lhs == .Atom || p.rule.lhs == .ExtendedAtom) && (p.altOf.map (capturingRhs ·.rhs)).getD false
      then m.insert id else m
    | none => m

/-- An alternative in effect: written alternative `idx` of `rule` in grammar `wg`; `fresh` for a
reading's alternative GL does not have. -/
structure Eff where
  alt : Alt
  wg : GrammarId
  rule : Rule
  idx : Nat
  fresh : Bool

/-- An overlay rule's alternatives in effect. -/
def overlayEffs (r : Rule) : List Eff := (writtenAlts r).zipIdx.map fun (a, i) => Eff.mk a .annexB r i false

/-- The alternatives of `n` in effect in grammar `g` under the readings `rd` in context `cx`
(`GL.alts`): a reading's definition, its alternatives equal to pinned ones being those and one
that differs from a pinned one only in lookahead restrictions that production with the reading's,
else the pinned one; then the overlays in effect, `extend` adding the alternatives it does not
restate and `replace` replacing the definition. -/
def effAlts (g : GrammarId) (rd : List RuleReading) (cx : Ctx) (n : Nat) : Option (List Eff) := do
  let _ ← ruleIn g n
  let base := match pinnedIn g n with
    | none => []
    | some (wg, r) =>
      let pinned := (writtenAlts r).zipIdx.map fun (a, i) => Eff.mk a wg r i false
      match rd.find? (fun x => x.grammar == g && x.rule.lhs.ctorIdx == n) with
      | some x => (writtenAlts x.rule).zipIdx.map fun (a, i) => match pinned.find? (·.alt == a) with
        | some e => e
        | none => match pinned.find? (·.alt.bare == a.bare) with
          | some e => { e with alt := a }
          | none => ⟨a, g, x.rule, i, true⟩
      | none => pinned
  pure ((overlaysIn cx g n).foldl (fun acc (r, m) => match m with
    | .extend => acc ++ (overlayEffs r).filter fun e => !acc.any (·.alt == e.alt)
    | .replace => overlayEffs r) base)

/-- The readings' right-hand sides, numbered past GL's numbers (`GL.prodId`). -/
def readingProds (rd : List RuleReading) : Array Prod := (prodsOf (rd.map fun x => (x.grammar, [x.rule]))).toArray

/-- Production id `p` is past GL's numbers: a reading's own right-hand side. -/
@[irreducible] def isFresh (p : Nat) : Bool := prods.size ≤ p

/-- Right-hand side `p`: GL's, or past GL's numbers a reading's; none at a retired number. -/
def prodOf (rd : List RuleReading) (p : Nat) : Option Prod :=
  if p < prods.size then prods[p]?.join else (readingProds rd)[p - prods.size]?

/-- The production id of written alternative `alt` of `r` (in grammar `g`) with presences `mask`. -/
def prodId (g : GrammarId) (r : Rule) (alt : Nat) (mask : List Bool) : Option Nat :=
  prodTable.get[(g.ctorIdx, r.lhs.ctorIdx, alt, mask)]?

/-- The production id of an alternative in effect with presences `mask`. -/
def effId (rd : List RuleReading) (e : Eff) (mask : List Bool) : Option Nat :=
  if e.fresh then
    ((readingProds rd).findIdx? fun p => p.grammar == e.wg && p.rule.lhs == e.rule.lhs && p.alt == e.idx && p.mask == mask).map
      (prods.size + ·)
  else prodId e.wg e.rule e.idx mask

/-- The code points `lo` to `hi`. -/
def points (cs : Array Nat) (lo hi : Nat) : Array Nat := cs.extract lo hi

/-- The code points `lo` to `hi`, unmaterialized: a view of `cs`. -/
def view (cs : Array Nat) (lo hi : Nat) : Subarray Nat := cs[lo...hi]

end Engine.Parse
