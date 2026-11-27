module

public import Engine.Parse.Keys
public import Ecma.Grammar.Notation
public import Std.Data.HashMap
public import Std.Data.HashSet

@[expose] public section

/-!
# The parser's interface: the caller's Parse Nodes, its code point classes, the outcomes, and GL tables

`Builder N` is how the parser makes the caller's Parse Nodes (GL's production id with its
presence mask, the nonterminal, the parameters, the code point span, one child entry per written
nonterminal item, the span's code points) and reads them back, with the code point classes the caller's
instance gives the grammar's primitives. GL's rules, alternatives in effect, production ids and
semicolon sites are looked up in `Array` tables built once from `glData` and verified at run time
(`parseTablesOk`).
-/

namespace Engine.Parse

open Ecma.Grammar

/-- The specification's grammar data (`Ecma.Spec.gl`). -/
def glData : GL :=
  ⟨Gen.grammars, Gen.prodIds, Gen.prodNext, Gen.blocks, Gen.semis.map fun s => (s.prod.ctorIdx, s.pos, s.semi)⟩

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
  /-- Unicode ID_Start and ID_Continue -/
  idStart : Nat → Bool
  idContinue : Nat → Bool

/-- Why a parse gave neither a Parse Node nor a complete "no parse". -/
inductive Stop where
  | fuel
  | depth
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

/-- All 6 `GrammarId` values in `ctorIdx` order. -/
def allGrammarIds : List GrammarId := [.numericString, .lexical, .syntactic, .regExp, .annexB, .json]

/-- The 5-bit index (`0..31`) of a parse context `Ctx`. -/
def cxIdx (cx : Ctx) : Nat :=
  (if cx.module then 1 else 0) +
  (if cx.annexB.html then 2 else 0) +
  (if cx.annexB.regExp then 4 else 0) +
  (if cx.annexB.ifFunctions then 8 else 0) +
  (if cx.annexB.forInInit then 16 else 0)

/-- The `Ctx` of 5-bit index `i`. -/
def cxOfIdx (i : Nat) : Ctx :=
  ⟨i &&& 1 != 0, ⟨i &&& 2 != 0, i &&& 4 != 0, i &&& 8 != 0, i &&& 16 != 0⟩⟩

/-- Count of `NT` constructors. -/
def numNTs : Nat := NT.names.length

/-- Every nonterminal defined in `glData.grammars` or `glData.blocks`, deduplicated. -/
def definedNTs : List NT :=
  let raw := (glData.grammars.flatMap fun (_, rs) => rs.map (·.lhs)) ++
             (glData.blocks.flatMap fun b => b.rules.map (·.lhs))
  raw.foldl (fun acc n => if acc.contains n then acc else acc ++ [n]) []

/-- `6 × numNTs` lookup of a grammar's own rule left-hand side (`glData.rulesOf g`). -/
def ruleNtTable : Thunk (Array (Array (Option NT))) := Thunk.mk fun _ =>
  allGrammarIds.toArray.map fun g =>
    (glData.rulesOf g).foldl (init := Array.replicate numNTs none) fun arr r =>
      arr.setIfInBounds r.lhs.ctorIdx (some r.lhs)

/-- The `NT` with `ctorIdx == ntIdx` defined directly in `glData.rulesOf g`, if any. -/
@[irreducible] def ruleNt (g : GrammarId) (ntIdx : Nat) : Option NT :=
  ((ruleNtTable.get[g.ctorIdx]?).bind (·[ntIdx]?)).join

/-- Whether `glData.rulesOf g` defines a nonterminal with `ctorIdx == ntIdx`. -/
def hasRule (g : GrammarId) (ntIdx : Nat) : Bool := (ruleNt g ntIdx).isSome

/-- Per-context `Thunk` of `6 × numNTs` `(NT × glData.alts)` entries (`O(1)` lookup, computed only for contexts used). -/
def altsTable : Array (Thunk (Array (Array (Option (NT × List Src))))) :=
  (List.range 32).toArray.map fun ci => Thunk.mk fun _ =>
    let cx := cxOfIdx ci
    allGrammarIds.toArray.map fun g =>
      definedNTs.foldl (init := Array.replicate numNTs none) fun arr n =>
        arr.setIfInBounds n.ctorIdx (some (n, glData.alts cx g n))

/-- The alternatives of `n` in effect in grammar `g` in context `cx` (`GL.alts`). -/
@[irreducible] def altsOf (cx : Ctx) (g : GrammarId) (n : NT) : List Src :=
  match ((altsTable[cxIdx cx]?.map Thunk.get).bind fun gt => (gt[g.ctorIdx]?).bind (·[n.ctorIdx]?)).join with
  | some (n', as) => if n' == n then as else []
  | none => []

/-- `32 × 6` table of `glData.ordered` and `glData.orderedNts`. -/
def orderedTable : Thunk (Array (Array (Bool × List NT))) := Thunk.mk fun _ =>
  (List.range 32).toArray.map fun ci =>
    let cx := cxOfIdx ci
    allGrammarIds.toArray.map fun g => (glData.ordered cx g, glData.orderedNts cx g)

/-- Whether B.1.2 orders grammar `g` in context `cx` (`GL.ordered`). -/
@[irreducible] def orderedBy (cx : Ctx) (g : GrammarId) : Bool :=
  (((orderedTable.get[cxIdx cx]?).bind (·[g.ctorIdx]?)).map (·.1)).getD false

/-- The nonterminals B.1.2 orders on grammar `g` in context `cx` (`GL.orderedNts`). -/
@[irreducible] def orderedNtsBy (cx : Ctx) (g : GrammarId) : List NT :=
  (((orderedTable.get[cxIdx cx]?).bind (·[g.ctorIdx]?)).map (·.2)).getD []

/-- Right-hand side `p`; none at a retired number. -/
@[irreducible] def prodOf (p : Nat) : Option Prod :=
  prods[p]?.join

/-- `6 × numNTs` table of `(altIdx, mask, prodId)` entries from `prods`. -/
def prodIdTable : Thunk (Array (Array (List (Nat × List Bool × Nat)))) := Thunk.mk fun _ =>
  let empty := allGrammarIds.toArray.map fun _ => Array.replicate numNTs ([] : List (Nat × List Bool × Nat))
  prods.zipIdx.foldl (init := empty) fun tbl (o, id) => match o with
    | none => tbl
    | some p =>
      let gi := p.grammar.ctorIdx
      let ni := p.rule.lhs.ctorIdx
      match tbl[gi]? with
      | none => tbl
      | some row =>
        let cur := (row[ni]?).getD []
        tbl.setIfInBounds gi (row.setIfInBounds ni (cur ++ [(p.alt, p.mask, id)]))

/-- Production id by `(g, lhs, alt, mask)`. -/
@[irreducible] def prodIdBy (g : GrammarId) (lhs : NT) (alt : Nat) (mask : List Bool) : Option Nat :=
  let entries := (((prodIdTable.get[g.ctorIdx]?).bind (·[lhs.ctorIdx]?)).getD [])
  (entries.find? fun (a, m, _) => a == alt && m == mask).map (·.2.2)

/-- Production id of an alternative `s` with presences `mask` (`GL.prodId`). -/
@[irreducible] def prodIdOf (s : Src) (mask : List Bool) : Option Nat :=
  prodIdBy s.grammar s.rule.lhs s.idx mask

/-- Boolean array of left-capturing parenthesis production ids (`GL.capturingIds`). -/
def capturingArr : Thunk (Array Bool) := Thunk.mk fun _ =>
  let ids := glData.capturingIds
  (List.range prods.size).toArray.map fun id => ids.contains id

/-- Whether production `id` is a left-capturing parenthesis (`GL.capturingIds`). -/
@[irreducible] def isCapturing (id : Nat) : Bool := (capturingArr.get[id]?).getD false

/-- Boolean array of non-strict Annex B production ids (`GL.sloppyIds`). -/
def sloppyArr : Thunk (Array Bool) := Thunk.mk fun _ =>
  let ids := glData.sloppyIds
  (List.range prods.size).toArray.map fun id => ids.contains id

/-- Whether production `id` is a non-strict Annex B overlay production (`GL.sloppyIds`). -/
@[irreducible] def isSloppy (id : Nat) : Bool := (sloppyArr.get[id]?).getD false

/-- `6 × numNTs` table of `(altIdx, ctor)` from `prodsOf glData.grammars`, for `GL.ctorOf`. -/
def ctorTable : Thunk (Array (Array (List (Nat × Nat)))) := Thunk.mk fun _ =>
  let empty := allGrammarIds.toArray.map fun _ => Array.replicate numNTs ([] : List (Nat × Nat))
  (prodsOf glData.grammars).foldl (init := empty) fun tbl p =>
    let gi := p.grammar.ctorIdx
    let ni := p.rule.lhs.ctorIdx
    match tbl[gi]? with
    | none => tbl
    | some row =>
      let cur := (row[ni]?).getD []
      if cur.any (·.1 == p.alt) then tbl
      else tbl.setIfInBounds gi (row.setIfInBounds ni (cur ++ [(p.alt, p.ctor)]))

/-- Written production `ctor` of `s` (`GL.ctorOf`). -/
@[irreducible] def ctorOfSrc (s : Src) : Option Nat :=
  let entries := (((ctorTable.get[s.grammar.ctorIdx]?).bind (·[s.rule.lhs.ctorIdx]?)).getD [])
  (entries.find? (·.1 == s.idx)).map (·.2)

/-- Semicolon site check at item `k` of written production `ctor?` (`paren`: inserted after `)`). -/
@[irreducible] def semiAllowedAt (ctor? : Option Nat) (k : Nat) (paren : Bool) : Bool :=
  match ctor? with
  | none => false
  | some c => glData.semis.any fun (c', k', cls) => c' == c && k' == k && match cls with
    | .insertable | .forHeaderIfDeclaration => !paren
    | .doWhile => true
    | .emptyStatement | .forHeader => false

/-- Semicolon site classification directly over `glData` (`Ecma.Grammar.semiAllowed`). -/
def semiAllowedSpec (s : Src) (k : Nat) (paren : Bool) : Bool :=
  semiAllowedAt (glData.ctorOf s) k paren

/-- Fast semicolon check at item `k` of `s` (`paren`: inserted after `)`). -/
def virtualOk (s : Src) (k : Nat) (paren : Bool) : Bool :=
  semiAllowedAt (ctorOfSrc s) k paren

/-- The code points `lo` to `hi`. -/
def points (cs : Array Nat) (lo hi : Nat) : Array Nat := cs.extract lo hi

/-- The code points `lo` to `hi`, unmaterialized: a view of `cs`. -/
def view (cs : Array Nat) (lo hi : Nat) : Subarray Nat := cs[lo...hi]

/-! ## Runtime verification of finite grammar invariants (`parseTablesOk`) -/

/-- Whether nonterminal `n` in `(cx, g)` unfolds within `fuel` steps using only positive items without conditions. -/
def posBounded (cx : Ctx) (g : GrammarId) : Nat → NT → Bool
  | 0, _ => false
  | f + 1, n => (glData.alts cx g n).all fun s => s.alt.rhs.all fun
    | .sym (.t _) _ | .phrase _ | .empty | .noLT => true
    | .sym (.nt m _) _ => posBounded cx g f m
    | _ => false

/-- Whether terminal `x` in a syntactic lookahead is non-empty text not starting with `/` or `}`. -/
def synLookTermOk : Terminal → Bool
  | .text str _ => match str.toList with
    | [] => false
    | c :: _ => c != '/' && c != '}'
  | .cp _ => false

/-- Whether terminal `x` in a code-point lookahead is non-empty. -/
def codeLookTermOk : Terminal → Bool
  | .text str _ => !str.isEmpty
  | .cp _ => true

/-- Whether all terminals in `qs` satisfy `ok`. -/
def lookSeqsOk (ok : Terminal → Bool) (qs : List (List LookItem)) : Bool :=
  qs.all fun q => q.all fun
    | .noLT => true
    | .t x => ok x

/-- Structural invariants of syntactic alternatives in `(cx, .syntactic)`. -/
def synItemOk (cx : Ctx) : Item → Bool
  | .phrase _ | .onlyIf _ => false
  | .lookahead l => match l with
    | .eq q | .ne q => lookSeqsOk synLookTermOk [q]
    | .mem qs | .notMem qs => lookSeqsOk synLookTermOk qs
    | .notMemNT _ => false
  | .butNot base ex =>
    let baseOk := match base with
      | .t _ => true
      | .nt m _ => (glData.alts cx .syntactic m).isEmpty
    let symOk : Sym → Bool
      | .t _ => true
      | .nt m _ => (glData.alts cx .syntactic m).isEmpty
    let exOk := match ex with
      | .sym y => symOk y
      | .oneOf ys _ => ys.all symOk
    baseOk && exOk
  | .sym (.nt m _) _ =>
    (glData.alts cx .syntactic m).isEmpty || (glData.rulesOf .syntactic).any (·.lhs == m)
  | _ => true

/-- Structural invariants of code-point alternatives in `(cx, g)`. -/
def codeItemOk (cx : Ctx) (g : GrammarId) : Item → Bool
  | .onlyIf p => match p with
    | .mvAbove10FFFF | .mvAtMost10FFFF | .mvLead | .mvTrail | .mvNonSurrogate => true
    | .groupNumberAtMostCount => glData.ordered cx g
    | _ => false
  | .phrase p => match p with
    | .anyCodePoint | .idStart | .idContinue | .leadSurrogate | .trailSurrogate => true
    | _ => false
  | .lookahead l => match l with
    | .eq q | .ne q => lookSeqsOk codeLookTermOk [q]
    | .mem qs | .notMem qs => lookSeqsOk codeLookTermOk qs
    | .notMemNT m =>
      !(glData.alts cx g m).isEmpty && (glData.alts cx g m).all fun e =>
        e.alt.guard.isEmpty && match e.alt.rhs with
          | [.sym (.t x) false] => codeLookTermOk x
          | _ => false
  | .butNot _ ex =>
    let symOk : Sym → Bool
      | .t _ => true
      | .nt m _ => posBounded cx g 16 m
    match ex with
    | .sym y => symOk y
    | .oneOf ys _ => ys.all symOk
  | _ => true

/-- Every `Src` from `glData.grammars` and `glData.blocks`'s overlays. -/
def allSrcs : List Src :=
  (glData.grammars.flatMap fun (g, rs) => rs.flatMap (srcsOf g)) ++
  (glData.blocks.flatMap fun b =>
    if b.kind matches .overlay .. then b.rules.flatMap (srcsOf .annexB) else [])

/-- Lazy `prodsOf glData.grammars` list for `ctorSpecFrom`. -/
def allProdsThunk : Thunk (List Prod) := Thunk.mk fun _ => prodsOf glData.grammars

/-- `GL.prodId` evaluated against a precomputed `byId` array (`prods = glData.byId`). -/
def prodIdSpecFrom (byId : Array (Option Prod)) (s : Src) (m : List Bool) : Option Nat :=
  let hit := fun (p : Prod) => p.grammar == s.grammar && p.rule.lhs == s.rule.lhs && p.alt == s.idx && p.mask == m
  byId.findIdx? (·.any hit)

/-- `GL.ctorOf` evaluated against a precomputed `prodsOf` list. -/
def ctorSpecFrom (ps : List Prod) (s : Src) : Option Nat :=
  (ps.find? fun p => p.grammar == s.grammar && p.rule.lhs == s.rule.lhs && p.alt == s.idx).map (·.ctor)

/-- Whether every terminal matched by `it` is non-empty (`codeLookTermOk`). -/
def srcItemTermOk : Item → Bool
  | .sym (.t x) _ | .butNot (.t x) _ => codeLookTermOk x
  | _ => true

def srcsCheck : Bool :=
  allSrcs.all fun s =>
    s.alt.rhs.all srcItemTermOk &&
    decide (ctorOfSrc s = ctorSpecFrom allProdsThunk.get s) &&
    decide (s.alt.opts = (s.alt.rhs.filter fun | .sym _ true => true | _ => false).length) &&
    (masks s.alt.opts).all fun m =>
      let pid := prodIdSpecFrom prods s m
      decide (prodIdOf s m = pid) && pid.isSome &&
      match pid >>= prodOf with
      | some P => decide (P.grammar = s.grammar ∧ P.rule = s.rule ∧ P.alt = s.idx ∧ P.mask = m)
      | none => false

def cxsCheck : Bool :=
  (List.range 32).all fun ci =>
    let cx := cxOfIdx ci
    decide (cxIdx cx = ci) &&
    allGrammarIds.all fun g =>
      decide (orderedBy cx g = glData.ordered cx g) &&
      decide (orderedNtsBy cx g = glData.orderedNts cx g) &&
      definedNTs.all fun n =>
        let as := glData.alts cx g n
        decide (altsOf cx g n = as) &&
        decide ((ruleNt g n.ctorIdx = some n) = ((glData.rulesOf g).any (·.lhs == n) = true)) &&
        as.all fun s =>
          s.rule.lhs == n &&
          (masks s.alt.opts).all fun m =>
            match prodIdOf s m >>= prodOf with
            | some P =>
              decide ((as.find? fun ef => ef.grammar == P.grammar && ef.idx == P.alt && ef.rule == P.rule) = some s)
            | none => false

def ruleNoneCheck : Bool :=
  allGrammarIds.all fun g =>
    (List.range numNTs).all fun idx => match ruleNt g idx with
      | none => !(glData.rulesOf g).any (·.lhs.ctorIdx == idx)
      | some n => n.ctorIdx == idx && (glData.rulesOf g).any (·.lhs == n)

def synCheck : Bool :=
  (List.range 32).all fun ci =>
    let cx := cxOfIdx ci
    !orderedBy cx .syntactic &&
    definedNTs.all fun n =>
      let as := altsOf cx .syntactic n
      (as.isEmpty || (glData.rulesOf .syntactic).any (·.lhs == n)) &&
      as.all fun s => s.alt.rhs.all (synItemOk cx)

def codeCheck : Bool :=
  (List.range 32).all fun ci =>
    let cx := cxOfIdx ci
    codeGrammars.all fun g =>
      definedNTs.all fun n =>
        (altsOf cx g n).all fun s => s.alt.rhs.all (codeItemOk cx g)

def fastCheck : Bool :=
  decide (ruleNt .syntactic NT.StringLiteral.ctorIdx = none) &&
  decide ((codeGrammars.filterMap fun g => (ruleNt g NT.StringLiteral.ctorIdx).map ((g, ·))) =
    [(.lexical, .StringLiteral)]) &&
  decide (ruleNt .syntactic NT.JSONText.ctorIdx = none) &&
  decide ((codeGrammars.filterMap fun g => (ruleNt g NT.JSONText.ctorIdx).map ((g, ·))) =
    [(.json, .JSONText)]) &&
  ((List.range 32).all fun ci =>
    let cx := cxOfIdx ci
    !orderedBy cx .lexical && !orderedBy cx .numericString && !orderedBy cx .json &&
    ((altsOf cx .lexical .StringLiteral).all fun s => match s.alt.rhs with
      | .sym (.t (.text "\"" _)) false :: _ | .sym (.t (.text "'" _)) false :: _ => true
      | _ => false) &&
    definedNTs.all fun n => decide (altsOf cx .json n = glData.pinned .json n))

/-- Runtime verification that all fast lookup tables match `glData` (`Ecma.Spec.gl`) and all finite
grammar invariants hold across every `Ctx` and `GrammarId`. Takes `Unit` so module initialization
does no work until `parseTablesOkThunk.get` is forced. -/
@[irreducible] def checkParseTables (_ : Unit) : Bool :=
  definedNTs.all (·.ctorIdx < numNTs) &&
  srcsCheck && cxsCheck && ruleNoneCheck && synCheck && codeCheck && fastCheck

/-- Specification alias for `checkParseTables ()` (not evaluated at module init). -/
abbrev parseTablesOk : Bool := checkParseTables ()

/-- Process-wide lazy check of `checkParseTables`. -/
def parseTablesOkThunk : Thunk Bool := Thunk.mk checkParseTables

end Engine.Parse
