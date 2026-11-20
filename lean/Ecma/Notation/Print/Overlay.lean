module

public import Ecma.Notation.Print.Early

/-!
# Ecma print: the readings and declarations of the overlay (spec/formal) as its text

What the data holds of the overlay besides its algorithms and rows, each printed as the overlay
writes it: a step with readings as its line of spec.html and each reading's steps
(`<emu-reading>`), an early-error rule with readings as its sentences and each reading's
(`<p reading=…>`), an algorithm's parameters (`<emu-params>`), a primitive's signature and
meaning (`<emu-primitive>`), a phrase's pattern and meaning (`<emu-phrase>`), a sort's
declaration (`<emu-sort>`). `scripts/bijection.py` compares each with its element.
-/

@[expose] public section

namespace Ecma.Print.Overlay

open Ecma Ecma.Print

/-- A reading's name, as the overlay writes it. -/
def readingName : Reading → String
  | .literal => "literal"
  | .test262 => "test262"
  | .proposed => "proposed"
  | .definition => "definition"

/-- A step with readings: its erratum, its own statement, the readings' steps. -/
abbrev Site := ErratumId × Stmt × List (Reading × List Node)

mutual
/-- The steps with readings in a statement, a later erratum's inside an earlier's. -/
def stmtSites : Stmt → List Site
  | .readings e lit alts => (e, lit, alts) :: stmtSites lit
  | .if_ _ b arms els => bodySites b ++ armsSites arms ++ optArmSites els
  | .ifElse _ a b => stmtSites a ++ stmtSites b
  | .repeat_ ns => nodesSites ns
  | .repeatWhile _ ns => nodesSites ns
  | .repeatUntil _ ns => nodesSites ns
  | .repeatN _ ns => nodesSites ns
  | .forEach _ _ _ _ b => bodySites b
  | .forEachRec _ _ _ b => bodySites b
  | .forRange _ _ _ _ _ _ b => bodySites b
  | .forSuchThat _ _ _ _ b => bodySites b
  | .forKeys _ _ _ _ b => bodySites b
  | .forIndex _ _ b => bodySites b
  | .forChildren _ b => bodySites b
  | .forChildrenOf _ _ b => bodySites b
  | .findSuchThat _ _ _ _ f => stmtSites f
  | .withSteps s ns => stmtSites s ++ nodesSites ns
  | .expanded _ _ ns => nodesSites ns
  | _ => []

def bodySites : Body → List Site
  | .inline s => stmtSites s
  | .block ns => nodesSites ns

def nodesSites : List Node → List Site
  | [] => []
  | .mk _ s :: r => stmtSites s ++ nodesSites r

def armsSites : List Arm → List Site
  | [] => []
  | .mk _ _ b :: r => bodySites b ++ armsSites r

def optArmSites : Option Arm → List Site
  | some (.mk _ _ b) => bodySites b
  | none => []
end

/-- A step with readings as text: its erratum, the step's line as spec.html has it (without its
marker and attributes), and each reading's name and steps, the steps from column 0. -/
structure StepReading where
  erratum : ErratumId
  line : String
  alts : List (String × String)

/-- The steps with readings of an algorithm body and of its closure literals' bodies. -/
def stepReadings (d : Decls) (vars : Array String) (cl : Array CloLit) (ns : List Node) : List StepReading :=
  let c := ctxOf d vars cl
  (nodesSites ns ++ cl.toList.flatMap (nodesSites ·.body)).map fun (e, lit, alts) =>
    { erratum := e, line := join (stmt c lit).1, alts := alts.map fun (r, ns) => (readingName r, nodes c ns) }

/-- The steps with readings of an SDO row: none in a row an erratum adds, whose one step is that
reading (printed as the row's body). -/
def rowReadings (d : Decls) (r : SdoRow) : List StepReading :=
  match r.form with
  | .alg as => if as.any (·.key == "reading") then [] else stepReadings d r.vars r.closures r.body
  | .equation => stepReadings d r.vars r.closures r.body

/-- An early-error rule with readings as text: its erratum, the rule's sentences as spec.html has
them on one line (none: a copy of another rule's readings for further productions), and each
reading's name and sentences. -/
def ruleReadings (d : Decls) (r : EarlyRow) : List StepReading :=
  let c := Early.rowCtx d r
  r.body.filterMap fun
    | .readings e lit alts =>
      some { erratum := e, line := Early.text c lit, alts := alts.map fun (rd, ss) => (readingName rd, Early.text c ss) }
    | _ => none

/-- An algorithm's parameters as `<emu-params>` writes them: `_x_: T, _y_: U`, or `_x_` with no type. -/
def paramsText (d : Decls) (a : Alg) : String :=
  let c := ctxOf d a.vars a.closures
  ", ".intercalate (a.header.params.map fun p =>
    "_" ++ name a.vars p.x ++ "_" ++ (match p.ty with | some t => ": " ++ join (ty c t).1 | none => ""))

/-- A hole of a template, by its number in the template: `_3_` (an expression), or with its kind. -/
def holeText (kind k : Nat) : String :=
  "_" ++ toString k ++ (match kind with
    | 0 => ""
    | 1 => ":condition"
    | 2 => ":type"
    | 3 => ":binder"
    | 4 => ":steps"
    | 5 => ":list"
    | _ => ":words") ++ "_"

mutual
/-- A template's parts, from the pending glue flag `g` and the number `k` of holes before it: its
words, each hole by its number, a choice as `⟨a | b⟩`. -/
def templateParts (g : Bool) (k : Nat) : List Piece → List P × Nat
  | [] => ([], k)
  | .word s :: r =>
    let (ps, k') := templateParts false k r
    (.t s g :: ps, k')
  | .glue :: r => templateParts true k r
  | .hole h :: r =>
    let (ps, k') := templateParts false (k + 1) r
    (.t (holeText h (k + 1)) g :: ps, k')
  | .choice alts :: r =>
    let (as, k1) := altsParts k alts
    let (ps, k') := templateParts false k1 r
    (.t "⟨" g :: as ++ .t "⟩" false :: ps, k')

/-- A choice's alternatives, separated by `|`. -/
def altsParts (k : Nat) : List (List Piece) → List P × Nat
  | [] => ([], k)
  | a :: r =>
    let (ps, k1) := templateParts false k a
    let (qs, k') := altsParts k1 r
    (ps ++ (if r.isEmpty then [] else [.t "|" false]) ++ qs, k')
end

/-- A phrase's template as the overlay's `<emu-pattern>` writes it, its holes numbered. -/
def templateText (t : List Piece) : String := join (templateParts false 0 t).1

/-- An argument of a phrase's meaning: a hole by its number, as `templateText` numbers it. -/
def argText (d : Decls) : PhraseArg → String
  | .hole i => "_" ++ toString (i + 1) ++ "_"
  | .spread i => "..._" ++ toString (i + 1) ++ "_"
  | .enum e => "~" ++ name d.enums e ++ "~"
  | .subject => "subject"
  | .thisNode => "this Parse Node"
  | .sort s => name d.sorts s
  | .field f => "[[" ++ name d.fields f ++ "]]"
  | .choice k => "choice " ++ toString k

/-- A meaning: `steps ID` (an algorithm of the overlay, by its clause id, or an operation's clause),
`[not ]Prim(args)` as the overlay's `meaning=` and `test=` write it, or nothing. -/
def meaningText (d : Decls) : PhraseMeaning → String
  | .alg a => "steps " ++ name d.clauses a.clause
  | .prim p args neg => (if neg then "not " else "") ++ name d.prims p ++ "(" ++ ", ".intercalate (args.map (argText d)) ++ ")"
  | .none => ""

/-- A sort's declaration, one line: `record` if its values are the Records of its kind, its
supersorts, its test, the operation its test names (if it names one), its context's algorithm. -/
def sortText (d : Decls) (s : SortDef) : String :=
  let test := match s.test with
    | .alg a => " test: " ++ meaningText d s.test ++ (let op := name d.ops a.clause; if op.isEmpty then "" else " (" ++ op ++ ")")
    | .none => ""
    | m => " test: " ++ meaningText d m
  let ctx := match s.context.bind (d.phrases[·]?) with
    | some p => " context: " ++ meaningText d p.meaning
    | none => ""
  (if s.record then "record" else "sort") ++
    (if s.super.isEmpty then "" else " super: " ++ ", ".intercalate (s.super.map (name d.sorts))) ++ test ++ ctx

end Ecma.Print.Overlay
