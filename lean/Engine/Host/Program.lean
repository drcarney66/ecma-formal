module

public import Engine.Host.Core
public import Engine.Host.Opts
public import Engine.Accel.Algs

@[expose] public section

/-!
# A whole program at Impl

ParseScript and ScriptEvaluation as one job and the queued jobs after it, all under one `drive`
(`program`), over a dispatcher `D`, the host's cells and the names `N`; the outcome shown as
`normal: v` or `throw: e`, or the stop (`outcome`). The driver every tier runs: the realm's set-up
(`setup`), then the program (`runFrom`, `run`), at the names `N`.
-/

namespace Engine.Host

open Ecma Engine

variable (N : Names)

/-- A field by its name; 0 where there is none. -/
def field (n : String) : FieldId := (N.field? n).getD 0

def str (s : String) : Val Impl := .str (Impl.strLit s)

/-- A component of an execution context; *null* where it has none. -/
def component (ctx : Val Impl) (f : FieldId) : Run Impl (Val Impl) :=
  match ctx with
  | .ref a => do
    match ← readCell a with
    | .record _ fs => Run.pure ((Impl.recGet fs f).getD .null)
    | _ => Run.pure .null
  | _ => Run.pure .null

/-- The running context's Realm, the stack then left empty. -/
def takeRealm : Run Impl (Val Impl) := do
  let s ← Run.get
  let r ← match (elems s.stack).getLast? with
    | some ctx => component ctx Known.fRealm
    | none => Run.pure .null
  fun s => .ok r { s with stack := Impl.seqNil }

/-- A promise's outcome: a normal completion of *undefined* where it is fulfilled, a throw completion
of its reason where it is rejected; none while it is pending. -/
def promiseOutcome (p : Val Impl) : Run Impl (Option (Val Impl)) := do
  match ← readField p (field N "PromiseState") with
  | .enum e =>
    if some e == N.enum? "fulfilled" then return some (normal .undefined)
    else if some e == N.enum? "rejected" then
      return some (.comp Known.eThrow (← readField p (field N "PromiseResult")) (.enum Known.eEmpty))
    else return none
  | _ => Run.stop .sortError

/-- A Module's completion from Evaluate's promise `v` after the jobs (`promiseOutcome`); a pending
promise, or an abrupt completion, as itself. -/
def settled (v : Val Impl) : Run Impl (Val Impl) := do
  if abrupt v then return v
  match v with
  | .obj _ => return (← promiseOutcome N v).getD v
  | _ => Run.stop .sortError

/-- What a program's source is: a Script, a Module (its specifier in the module map), or either one
only parsed. -/
inductive Source where
  | script
  | module (key : String)
  | parsed (asModule : Bool)
  deriving BEq, Repr

/-- The file `path` as `--module` and `--parse-only` have it; a Module's specifier is `./NAME`. -/
def sourceFor (asModule parseOnly : Bool) (path : String) : Source :=
  if parseOnly then .parsed asModule
  else if asModule then .module ("./" ++ ((System.FilePath.mk path).fileName.getD path))
  else .script

/-- What follows an abrupt completion of the script (§9.5's job policies). -/
inductive JobPolicy where
  /-- RunScriptInNewRealm: the program ends with it, the queued jobs not run. -/
  | inNewRealm
  /-- RunScriptAndJobs: the queued jobs run, and the program's completion is the script's. -/
  | andJobs
  deriving BEq, Repr

/-- The program, one run of the agent's Jobs (`Call.jobs`): the source left for the host's `first`, which runs it
as a Job of its own (`firstBuiltins`), ClearKeptObjects where the host performs it, then
main's Jobs, the other agents' turns among them (the machine's job loop, `Call.jobs`, with the host's `idle`;
`afterScript`); a Module's
completion is its Evaluate promise's then (`settled`). -/
def program (D : Engine.Host.Runner) (_H : Host Impl) (c : Cells)
    (src : Array Nat) (jp : JobPolicy := .inNewRealm) (sr : Source := .script) : Run Impl (Val Impl) := do
  let realm := (← readList c.realm).headD .null
  let (kind, key) : Nat × Val Impl := match sr with
    | .script => (0, .null)
    | .module key => (1, str key)
    | .parsed false => (2, .null)
    | .parsed true => (3, .null)
  writeElems c.realm ([realm, .math (Impl.ofNat kind), .bool (jp == .inNewRealm), key] ++
    src.toList.map fun p => .math (Impl.ofNat p))
  let j ← D.jobs ((N.clauseOf? clearKeptSec).map (⟨·, 0⟩))
  let v ← match ← readList c.realm with
    | [_, _, v] => pure v
    | _ => Run.stop .assertFailed
  writeElems c.realm [realm]
  let v := if abrupt v then v else if abrupt j then j else v
  if sr matches .module _ then settled N v else return v

/-! Showing the outcome. -/

def hex4 (n : Nat) : String :=
  let h := String.ofList (Nat.toDigits 16 n)
  String.ofList (List.replicate (4 - h.length) '0') ++ h

/-- One code unit outside a surrogate pair. -/
def escapeUnit (u : UInt16) : String :=
  let n := u.toNat
  let c := Char.ofNat n
  if 0xD800 ≤ n ∧ n < 0xE000 then "\\u" ++ hex4 n
  else if c == '"' then "\\\""
  else if c == '\\' then "\\\\"
  else if c == '\n' then "\\n"
  else if n < 0x20 then "\\u" ++ hex4 n
  else String.singleton c

/-- Code units as text, lone surrogates and controls escaped. -/
def escapeUnits : List UInt16 → String
  | [] => ""
  | [u] => escapeUnit u
  | u :: tl@(l :: rest) =>
    if 0xD800 ≤ u.toNat ∧ u.toNat < 0xDC00 ∧ 0xDC00 ≤ l.toNat ∧ l.toNat < 0xE000 then
      String.singleton (Char.ofNat (0x10000 + (u.toNat - 0xD800) * 0x400 + (l.toNat - 0xDC00))) ++ escapeUnits rest
    else escapeUnit u ++ escapeUnits tl

/-- Code units as text (`print`'s lines), a lone surrogate as U+FFFD. -/
def displayUnits : List UInt16 → List Char
  | [] => []
  | u :: tl@(l :: rest) =>
    if 0xD800 ≤ u.toNat ∧ u.toNat < 0xDC00 ∧ 0xDC00 ≤ l.toNat ∧ l.toNat < 0xE000 then
      Char.ofNat (0x10000 + (u.toNat - 0xD800) * 0x400 + (l.toNat - 0xDC00)) :: displayUnits rest
    else one u :: displayUnits tl
  | [u] => [one u]
where
  one (u : UInt16) : Char := if 0xD800 ≤ u.toNat ∧ u.toNat < 0xE000 then '\uFFFD' else Char.ofNat u.toNat

def display (s : Array UInt16) : String := String.ofList (displayUnits s.toList)

def objectCell (s : State Impl) (a : Nat) : Option (Impl.Rec (Val Impl) × Impl.Props (Val Impl)) :=
  match Impl.heapGet s.heap a with
  | some (.object sl ps) => some (sl, ps)
  | _ => none

/-- A data property of `o`, own or inherited, at most `n` objects up. -/
def dataProperty (s : State Impl) (key : String) : Nat → Nat → Option (Val Impl)
  | 0, _ => none
  | n + 1, o => do
    let (sl, ps) ← objectCell s o
    match Impl.propsGet ps (.inl (Impl.strLit key)) with
    | some (.ref d) => match Impl.heapGet s.heap d with
      | some (.record _ fs) => Impl.recGet fs Known.fValue
      | _ => none
    | some _ => none
    | none => match Impl.recGet sl (field N "Prototype") with
      | some (.obj p) => dataProperty s key n p
      | _ => none

def isError (s : State Impl) (o : Nat) : Bool :=
  match objectCell s o with
  | some (sl, _) => (Impl.recGet sl (field N "ErrorData")).isSome
  | none => false

def showNum (x : Impl.Num) : String :=
  match Impl.numView x with
  | .negZero => "-0"
  | _ => (Engine.Accel.numberToString 10 x).getD "NaN?"

def bigText (i : Impl.Big) : String := (fun (i : Int) => toString i) i

def addrNat (a : Impl.Addr) : Nat := a

def showVal (s : State Impl) : Val Impl → String
  | .undefined => "undefined"
  | .null => "null"
  | .bool b => toString b
  | .str u => "\"" ++ escapeUnits u.toList ++ "\""
  | .num x => showNum x
  | .big i => s!"{bigText i}n"
  | .sym (_, some d) => "Symbol(" ++ escapeUnits d.toList ++ ")"
  | .sym (i, none) => s!"Symbol(#{i})"
  | .obj o => if isError N s o then s!"[object {errorName s o} #{addrNat o}]" else s!"[object #{addrNat o}]"
  | _ => "(not a language value)"
where
  errorName (s : State Impl) (o : Nat) : String := match dataProperty N s "name" 64 o with
    | some (.str n) => display n
    | _ => "Error"

/-- An uncaught exception: an Error as `name` or `name: message`, another object with its
constructor's name, else the value. -/
def showThrown (s : State Impl) : Val Impl → String
  | .obj o =>
    if isError N s o then
      let name := showVal.errorName N s o
      match dataProperty N s "message" 64 o with
      | some (.str m) => if m.isEmpty then name else name ++ ": " ++ display m
      | _ => name
    else match dataProperty N s "constructor" 64 o with
      | some (.obj c) => match dataProperty N s "name" 1 c with
        | some (.str n) => showVal N s (.obj o) ++ s!" (constructor {display n})"
        | _ => showVal N s (.obj o)
      | _ => showVal N s (.obj o)
  | v => showVal N s v

/-- A stop's name as the programs print it. -/
def stopName : Stop → String
  | .blocked => "blocked"
  | .sortError => "sortError"
  | .assertFailed => "assertFailed"
  | .residue => "residue"
  | .noReturn => "noReturn"
  | .implLimit => "implLimit"

/-- The result line and exit status of a program's completion; the lines `print` wrote. -/
def outcome (c : Cells) : Res Impl (Val Impl) → String × UInt32 × List String
  | .ok v s =>
    let out := match Impl.heapGet s.heap c.out with
      | some (.list xs _) => (elems xs).filterMap fun | .str u => some (display u) | _ => none
      | _ => []
    match v with
    | .comp t x _ =>
      if t == Known.eNormal then ("normal: " ++ showVal N s x, 0, out)
      else if t == Known.eThrow then ("throw: " ++ showThrown N s x, 1, out)
      else (s!"abrupt: {(N.enumName t).getD "?"}", 4, out)
    | x => ("normal: " ++ showVal N s x, 0, out)
  | .esc v s => ("throw: " ++ showThrown N s v, 1, [])
  | .stop r => (s!"stop: {stopName r}", 3, [])

def s0 : State Impl := { heap := Impl.heapEmpty, stack := #[], resumed := .absent, agent := .absent }

/-- A set-up's failure as a program's result. -/
def setupFailed : Res Impl Cells → Res Impl (Val Impl)
  | .ok _ s => .ok .undefined s
  | .stop r => .stop r
  | .esc v s => .esc v s

/-! The driver: the realm, then the program. -/

/-- InitializeHostDefinedRealm (`g`) through `D`, new symbols after the `syms` well-known ones. -/
def realmBy (g : Option AlgId) (syms : Nat) (D : Engine.Host.Runner) : Run Impl Unit := do
  let some g := g | Run.stop .residue
  let s ← Run.get
  Run.set { s with syms := max s.syms syms }
  let _ ← D.call g []

/-- The realm by InitializeHostDefinedRealm (`g`, `syms` well-known symbols) through `mk`, set up
for the host with the options `ho`: the host's cells. -/
def setup (g : Option AlgId) (syms : Nat) (mk : Host Impl → Engine.Host.Runner) (ho : HostOpts) :
    Run Impl Cells := do
  let c ← init N ho.canBlock
  realmBy g syms (mk (hostBy N ho c))
  let r ← takeRealm
  setRealm c r
  return c

/-- `src` (as `sr` has it) from a set-up state `s` over the cells `c` by the dispatcher `mk`, the
host's options `ho`, the job policy `jp`. -/
def runFrom (mk : Host Impl → Engine.Host.Runner) (ho : HostOpts) (jp : JobPolicy) (c : Cells)
    (s : State Impl) (src : Array Nat)
    (sr : Source := .script) :
    Res Impl (Val Impl) :=
  program N (mk (hostBy N ho c)) (hostBy N ho c) c src jp sr s

/-- The names `NAME` that `text` writes as `./NAME`, up to a quote, backquote or whitespace. -/
def namedModules (text : String) : List String :=
  (text.splitOn "./").drop 1 |>.map fun seg => String.ofList (seg.toList.takeWhile fun c =>
    !(c == '\'' || c == '"' || c == '`' || c.isWhitespace))

/-- The modules of `dir` (`--module-dir`) by the specifier `./NAME`: each `*_FIXTURE.js` and
`*_FIXTURE.json` file, and each `.js`, `.mjs` or `.json` file there that `root` (the program's text)
names as `./NAME`, or a module it so reaches. -/
def moduleTable (dir : Option String) (root : String) : IO (List (String × String)) := do
  let some dir := dir | return []
  let names := ((← System.FilePath.readDir dir).map (·.fileName)).filter fun n => n.endsWith ".js" || n.endsWith ".mjs" || n.endsWith ".json"
  let read (n : String) : IO String := IO.FS.readFile (System.FilePath.mk dir / n)
  let mut table ← ((names.filter fun n => n.endsWith "_FIXTURE.js" || n.endsWith "_FIXTURE.json").qsort (· < ·)).toList.mapM fun n => do
    return ("./" ++ n, ← read n)
  let mut seen : List String := []
  let mut todo := [root]
  for _ in [0:names.size + 1] do
    let some t := todo.head? | break
    todo := todo.tail
    for n in namedModules t do
      if names.contains n && !seen.contains n then
        seen := n :: seen
        match table.find? (·.1 == "./" ++ n) with
        | some m => todo := todo ++ [m.2]
        | none =>
          let x ← read n
          table := table ++ [("./" ++ n, x)]
          todo := todo ++ [x]
  return table

/-- What a program file runs: its text, the module sources by key and whether they are d8's
(`resolve`), what the text is, the scripts that run after the preludes and before it, and the
warnings to report. -/
structure Loaded where
  text : String
  modules : List (String × String) := []
  resolve : Bool := false
  source : Source := .script
  scripts : List String := []
  warnings : List String := []
  /-- the bundle's modules (name, key, text) -/
  bundle : List (String × String × String) := []

/-- The file `path` of text `text`: with `bundle`, a d8 bundle (`Bundle`) runs its entrypoint as a
Module (parsed only with `parseOnly`) after its scripts, over its modules, and a text that is not a
bundle is a Script, as d8 runs it; else the text as `--module` and `--parse-only` have it, with
`dir`'s modules (`moduleTable`). Error: the bundle's. -/
def loadProgram (bundle asModule parseOnly : Bool) (dir : Option String) (path text : String) :
    IO (Except String Loaded) := do
  if !bundle then
    return .ok { text, modules := ← moduleTable dir text, source := sourceFor asModule parseOnly path }
  match Bundle.parse text with
  | .error e => return .error e
  | .ok none => return .ok { text, source := if parseOnly then .parsed false else .script }
  | .ok (some b) => match b.plan with
    | .error e => return .error e
    | .ok (scripts, key, entry) =>
      return .ok { text := entry, modules := b.table, resolve := true, scripts, warnings := b.warnings,
                   source := if parseOnly then .parsed true else .module key, bundle := b.modules }

end Engine.Host
