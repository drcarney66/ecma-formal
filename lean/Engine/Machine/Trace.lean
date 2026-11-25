module

public import Ecma.Machine.Step
public import Ecma.Lower.Lin
public import Engine.Machine.CloPath
public import Ecma.Notation.Print
public import Std.Data.HashMap

@[expose] public section

/-!
# The steps a run enters

The machine enters a step at its `site` instruction. A run's records are kept from its configurations
only: each step's trace line (the algorithm's sec-id and the step's number, `sec-toboolean 2.a.ii.`, then
the start of the step's text), a stop's frames, and the steps entered. A step of an erratum's reading is
numbered under the reading's overlay id (`readingKey`) from 1. The step's text is found in the program by
the frame's unit and the step's path (`unitOf`, numbered as `lin` numbers them).

A transition that stops keeps its configuration's frames (algorithm and step path, innermost first); each
run the stop passes through, a sub-run's caller's, adds its frames after them. The site is the first
frame, the callers the algorithms after it.
-/

namespace Engine.Machine
open Ecma Ecma.Machine

variable {M : Model}

/-- `n` in lower-case Roman numerals. -/
def roman (n : Nat) : String :=
  let ds := [(1000, "m"), (900, "cm"), (500, "d"), (400, "cd"), (100, "c"), (90, "xc"), (50, "l"),
    (40, "xl"), (10, "x"), (9, "ix"), (5, "v"), (4, "iv"), (1, "i")]
  (ds.foldl (fun (acc, n) (v, s) => (acc ++ String.join (List.replicate (n / v) s), n % v)) ("", n)).1

/-- `n` in lower-case letters: a … z, aa, ab, …. -/
def alpha (n : Nat) : String :=
  let rec go : Nat → Nat → List Char → List Char
    | 0, _, acc => acc
    | f + 1, n, acc => if n == 0 then acc
      else go f ((n - 1) / 26) (Char.ofNat ('a'.toNat + (n - 1) % 26) :: acc)
  String.ofList (go (n + 1) n [])

/-- A step number at depth `d`: decimal, then lower-alpha, then lower-roman, cycling. -/
def levelText (d n : Nat) : String :=
  match d % 3 with
  | 0 => toString n
  | 1 => alpha n
  | _ => roman n

/-- A step path (innermost first) as written: `2.a.ii`. -/
def pathText (p : List Nat) : String :=
  ".".intercalate (p.reverse.zipIdx.map fun (n, d) => levelText d n)

/-- A step's section and number: the algorithm's (by `clauses`) and the step's path (`pathText`). -/
def stepLabel (clauses : Array String) (a : AlgId) (p : List Nat) : String × String :=
  (clauses.getD a.clause "?", pathText p)

/-- A trace line: the step's section and number (`stepLabel`). -/
def traceLine (clauses : Array String) (a : AlgId) (p : List Nat) : String :=
  let (sec, n) := stepLabel clauses a p
  s!"{sec} {n}."

/-- Text without markup: tags, and the `_`, `*` and `~` around names and values, dropped. -/
def plainText (s : String) : String :=
  String.ofList (go s.toList false [])
where
  go : List Char → Bool → List Char → List Char
    | [], _, acc => acc.reverse
    | '<' :: r, _, acc => go r true acc
    | '>' :: r, true, acc => go r false acc
    | _ :: r, true, acc => go r true acc
    | c :: r, false, acc => go r false (if c == '_' || c == '*' || c == '~' then acc else c :: acc)

/-- A printed step's own line: its text after the marker and attributes. -/
def ownLine (t : String) : String :=
  let l := (((t.splitOn "\n").filter (·.any (· != ' '))).headD "").toList.dropWhile (· == ' ')
  let l := if l.take 3 == ['1', '.', ' '] then l.drop 3 else l
  String.ofList (if l.head? == some '[' then (l.dropWhile (· != ']')).drop 2 else l)

/-- What a run keeps beside itself: each step's line (`trace`), a stop's frames (`sites`), the
steps entered (`cover`). -/
structure Obs where
  trace : Bool := false
  sites : Bool := false
  cover : Bool := false

/-- The frames of the stop being passed on, innermost first. -/
initialize stopFrames : IO.Ref (Option (Array (AlgId × List Nat))) ← IO.mkRef none

/-- The steps entered, by (clause, index, path): whether each is an Assert. -/
initialize coverSteps : IO.Ref (Std.HashMap (Nat × Nat × List Nat) Bool) ← IO.mkRef {}

/-- An `Assert:` step. -/
def assertStep : Stmt → Bool
  | .assert _ | .assertAlways _ | .assertIf .. => true
  | _ => false

mutual
/-- The steps a statement at path `p` holds, each with its path. -/
partial def sitesS (p : List Nat) : Stmt → List (List Nat × (Stmt ⊕ Arm))
  | .if_ _ b arms els => sitesBody p b ++ sitesArms p 0 (arms ++ els.toList)
  | .ifElse _ s1 s2 => sitesS p s1 ++ sitesS p s2
  | .repeat_ b | .repeatWhile _ b | .repeatUntil _ b | .repeatN _ b | .block b => sitesNodes b 1 p
  | .forEach _ _ _ _ b | .forEachRec _ _ _ b | .forRange _ _ _ _ _ _ b | .forKeys _ _ _ _ b | .forIndex _ _ b
  | .forChildren _ b | .forChildrenOf _ _ b => sitesBody p b
  | _ => []

/-- StepList from number `i` under `up` (`linNodes`). -/
partial def sitesNodes : List Stmt → Nat → List Nat → List (List Nat × (Stmt ⊕ Arm))
  | [], _, _ => []
  | s :: ns, i, up => (i :: up, .inl s) :: sitesS (i :: up) s ++ sitesNodes ns (i + width s) up

partial def sitesBody (p : List Nat) : Body → List (List Nat × (Stmt ⊕ Arm))
  | .inline s => sitesS p s
  | .block ns => sitesNodes ns 1 p

/-- The `Else if` and `Else` steps from the `j`th after the step at `p` (`linArms`). -/
partial def sitesArms (p : List Nat) (j : Nat) : List Arm → List (List Nat × (Stmt ⊕ Arm))
  | [] => []
  | a@(.mk _ b) :: as => (armPath p j, .inr a) :: sitesBody (armPath p j) b ++ sitesArms p (j + 1) as
end

/-- A unit's steps with their paths. -/
abbrev StepList := List (List Nat × (Stmt ⊕ Arm))

/-- An algorithm or SDO row as the records read it: its variables and closure literals, its own steps with their
paths, and each closure literal's steps under the literal's step, found on first use. -/
structure UnitSteps where
  vars : Array String := #[]
  cls : Array CloLit := #[]
  steps : StepList := []
  closSteps : Array (Thunk StepList) := #[]

/-- A frame's owner: the SDO row of `a` at production `prod` (several rows may share an id; `rows` finds one by
its production), else algorithm `a`, else the row `a` names. -/
def unitOf (P : Prog) (rows : AlgId → ProdId → Option SdoRow) (a : AlgId)
    (prod : Option ProdId) : UnitSteps :=
  let own : Option (Array String × Array CloLit × List Stmt) := match prod.bind (rows a) with
    | some r => some (r.vars, r.closures, r.body)
    | none => match P.alg a with
      | some g => some (g.vars, g.closures, g.body)
      | none => (P.rowOf a).map fun r => (r.vars, r.closures, r.body)
  match own with
  | some (vars, cls, body) =>
    { vars, cls, steps := sitesNodes body 1 []
      closSteps := cls.mapIdx fun k cl => Thunk.mk fun _ => sitesNodes cl.body 1 (cloPath P ⟨a, k⟩) }
  | none => {}

/-- The step a configuration enters: its frame's unit (algorithm, closure literal, production) and the step's path. -/
def entered (c : Cfg M) : Option (AlgId × Option Nat × Option ProdId × List Nat) :=
  match c.ctl, c.frames with
  | .code (.site p :: _), f :: _ => some (f.alg, f.clo, f.node.map M.nodeProd, p)
  | _, _ => none

/-- The step at path `p` of a unit: its own, or its closure literal `clo`'s. -/
def UnitSteps.at (u : UnitSteps) (clo : Option Nat) (p : List Nat) : Option (Stmt ⊕ Arm) :=
  let steps : StepList := match clo with
    | none => u.steps
    | some k => match u.closSteps[k]? with
      | some th => th.get
      | none => []
  (steps.find? (·.1 == p)).map (·.2)

/-- A step's own text, in its unit's variables. -/
def UnitSteps.text (d : Decls) (u : UnitSteps) (s : Stmt ⊕ Arm) : String :=
  let pc : Print.Ctx := { d, vars := u.vars, cl := u.cls, clos := u.cls.map fun _ => "", depth := 0 }
  match s with
  | .inl n => plainText (ownLine (Print.node pc n))
  | .inr arm => plainText (ownLine (Print.arm pc arm))

/-- The units of a program, by frame. -/
structure Units where
  /-- an algorithm's or row's unit, by its id -/
  own : Std.HashMap (Nat × Nat) (Thunk UnitSteps) := {}
  /-- an SDO row's unit, by its id and production -/
  ownAt : Std.HashMap (Nat × Nat × ProdId) (Thunk UnitSteps) := {}
  /-- any other frame's -/
  other : AlgId → Option ProdId → UnitSteps := fun _ _ => {}

/-- A frame's unit: the row at its production, else its algorithm's or row's by id. -/
def Units.of (u : Units) (a : AlgId) (prod : Option ProdId) : UnitSteps :=
  match prod.bind fun k => u.ownAt[(a.clause, a.idx, k)]? with
  | some t => t.get
  | none => match u.own[(a.clause, a.idx)]? with
    | some t => t.get
    | none => u.other a prod

/-- A configuration's trace line with the first 40 characters of its step's text. -/
def stepLine (d : Decls) (units : Thunk Units) (clauses : Array String) (c : Cfg M) :
    Option String :=
  (entered c).map fun (a, clo, prod, p) =>
    let u := units.get.of a prod
    let text := ((u.at clo p).map (u.text d)).getD ""
    traceLine clauses a p ++ " " ++ String.ofList (text.toList.take 40)

/-- Both records, as kept. -/
structure ObsRecords where
  frames : Option (Array (AlgId × List Nat)) := none
  cover : Std.HashMap (Nat × Nat × List Nat) Bool := {}

def getObs : IO ObsRecords := return { frames := ← stopFrames.get, cover := ← coverSteps.get }

/-- The records `k` restored. -/
def setObs (k : ObsRecords) : IO Unit := do
  stopFrames.set k.frames
  coverSteps.set k.cover

/-- Both records emptied. -/
def resetObs : IO Unit := setObs {}

/-- The frame a configuration without frames is given for a continuation (`⟨0, 0⟩`, no step). -/
def placeholderFrame (f : AlgId × List Nat) : Bool := f.1 == ⟨0, 0⟩ && f.2.isEmpty

/-- A stop's site and callers from its frames, placeholders left out: the first frame, then the
algorithms after it, each run of one algorithm once, at most `k`. -/
def siteOfFrames (k : Nat) (fs : List (AlgId × List Nat)) : Option ((AlgId × List Nat) × List AlgId) :=
  match fs.filter (!placeholderFrame ·) with
  | [] => none
  | (a, p) :: r => some ((a, p), ((r.map (·.1)).foldl (fun (l, acc) b => if b == l then (l, acc) else (b, b :: acc)) (a, [])).2.reverse.take k)

/-- The kept stop's site and at most `k` callers. -/
def stopSite (k : Nat) : IO (Option ((AlgId × List Nat) × List AlgId)) := do
  return (← stopFrames.get).bind fun fs => siteOfFrames k fs.toList

/-- A site as written: `sec-id#idx path` (`?` for no step). -/
def siteText (clauses : Array String) (a : AlgId) (p : List Nat) : String :=
  s!"{clauses.getD a.clause "?"}#{a.idx} {if p.isEmpty then "?" else pathText p}"

/-- The steps entered: `cover<TAB>sec-id#idx path A|S` (`A` an Assert), sorted. -/
def coverRecords (clauses : Array String) : IO (List String) := do
  let ls := (← coverSteps.get).toList.map fun ((cl, i, p), a) =>
    s!"cover\t{siteText clauses ⟨cl, i⟩ p} {if a then "A" else "S"}"
  return (ls.toArray.qsort (· < ·)).toList

end Engine.Machine
