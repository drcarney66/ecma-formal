module

public import Engine.Host.Names
public import Engine.Host.Bundle
public import Engine.Host.Agents
public import Engine.Model
public import Ecma.Host.Jobs
public import Engine.Host.Strategy
public import Engine.Host.DateParse
public import Ecma.Host.Laws
public import Std.Data.HashSet

@[expose] public section

/-!
# The host of a whole program, at Impl

The host-defined operations the specification calls (by sec-id, resolved through the names `N`),
its choices at the host primitives, its jobs (the queue is the host-call log), `print`, a
host-defined built-in function whose lines go to a host-owned List, and `$262` (test262's `global`,
`detachArrayBuffer`, `createRealm` and `evalScript`, and `IsHTMLDDA` on a host that supports §B.3.6), both
on the global object, and HostLoadImportedModule, a host algorithm over the host's module map (the host-call
log) and module sources. Its laws: Spec.Host, at Ecma.Gen's names.
-/

namespace Engine.Host

open Ecma Engine

variable (N : Names)

/-- The host's cells: the printed Strings, a one-element List holding the host's realm or *null*, the
module sources by key, and whether a specifier's key is d8's (`resolve`, a bundle's) or itself. -/
structure Cells where
  out : Impl.Addr
  realm : Impl.Addr
  modules : List (String × String) := []
  resolve : Bool := false

/-- An Agent Record field by name. -/
def agentField (n : String) : FieldId := (N.field? n).getD 0

/-- A new Record of the sort of that name (a Record where the data has none), with those fields. -/
def newRecord (sort : String) (fs : List (String × Val Impl)) : Run Impl Impl.Addr :=
  alloc (.record ((N.sort? sort).getD Known.sRecord) (fs.foldl (fun m (n, v) => Impl.recSet m (agentField N n) v) Impl.recEmpty))

/-- The surrounding agent's Agent Record (§9.6): [[KeptAlive]] and [[GlobalSymbolRegistry]]
new empty Lists, [[ModuleAsyncEvaluationCount]] 0; the host's choices: little-endian,
lock-free atomics, [[CanBlock]] `canBlock`; [[Signifier]] the Record itself; [[CandidateExecution]] the
initial candidate execution (§9.7): one Agent Events Record, the agent's, with no events. -/
def newAgent (canBlock : Bool := false) : Run Impl Unit := do
  let fs : List (String × Val Impl) := [("LittleEndian", .bool true), ("CanBlock", .bool canBlock),
    ("IsLockFree1", .bool true), ("IsLockFree2", .bool true), ("IsLockFree8", .bool true),
    ("KeptAlive", .ref (← alloc (.list Impl.seqNil 0))), ("ModuleAsyncEvaluationCount", .math (Impl.ofNat 0)),
    ("GlobalSymbolRegistry", .ref (← alloc (.list Impl.seqNil 0)))]
  let a ← newRecord N "Agent Record" fs
  writeField (.ref a) (agentField N "Signifier") (.ref a)
  let er ← newRecord N "Agent Events Record" [("AgentSignifier", .ref a),
    ("EventList", .ref (← alloc (.list Impl.seqNil 0))), ("AgentSynchronizesWith", .ref (← alloc (.list Impl.seqNil 0)))]
  let ex ← newRecord N "candidate execution" [("EventsRecords", .ref (← alloc (.list (Impl.seqPush Impl.seqNil (.ref er)) 0))),
    ("ChosenValues", .ref (← alloc (.list Impl.seqNil 0)))]
  writeField (.ref a) (agentField N "CandidateExecution") (.ref ex)
  fun s => .ok () { s with agent := .ref a }

/-- New empty cells, the realm *null*; the surrounding agent's Agent Record (`newAgent`), which can
block where `canBlock` says so. -/
def init (canBlock : Bool := false) : Run Impl Cells := do
  newAgent N canBlock
  return { out := ← alloc (.list Impl.seqNil 0), realm := ← alloc (.list (Impl.seqPush Impl.seqNil .null) 0) }

def elems (xs : Impl.Seq (Val Impl)) : List (Val Impl) := Impl.seqFoldl (fun acc v => acc ++ [v]) [] xs

def readList (a : Impl.Addr) : Run Impl (List (Val Impl)) := do
  match ← readCell a with
  | .list xs _ => return elems xs
  | _ => Run.stop .sortError

def writeElems (a : Impl.Addr) (vs : List (Val Impl)) : Run Impl Unit :=
  writeList a (vs.foldl Impl.seqPush Impl.seqNil)

/-- Set the host's realm. -/
def setRealm (c : Cells) (r : Val Impl) : Run Impl Unit := writeElems c.realm [r]

def unused : Val Impl := .enum Known.eUnused

def normal (v : Val Impl) : Val Impl := .comp Known.eNormal v (.enum Known.eEmpty)

/-- The enum of that name; residue where the data has none. -/
def enumNamed (n : String) : Run Impl (Val Impl) :=
  match N.enum? n with
  | some e => Run.pure (.enum e)
  | none => Run.stop .residue

/-- A normal completion containing the enum of that name; residue where the data has none. -/
def normalEnum (n : String) : Run Impl (Val Impl) :=
  match N.enum? n with
  | some e => Run.pure (normal (.enum e))
  | none => Run.stop .residue

abbrev Hook := Cells → List (Val Impl) → Run Impl (Val Impl)

/-- splitmix64's finalizer. -/
def mix (x : Nat) : Nat :=
  let w := 2 ^ 64
  let z := (x + 0x9E3779B97F4A7C15) % w
  let z := ((z ^^^ (z >>> 30)) * 0xBF58476D1CE4E5B9) % w
  let z := ((z ^^^ (z >>> 27)) * 0x94D049BB133111EB) % w
  z ^^^ (z >>> 31)

/-- The pseudo-random word of the choice `q` at host-log length `n` under the seed `N`. -/
def draw (N q n : Nat) : Nat := mix (mix (mix N + q) + n)

/-- `draw`'s key for Math.random. -/
def randomKey : Nat := 1000000

/-- The seed of Math.random where no `--host-seed` is given, so that a run is reproducible. -/
def defaultSeed : Nat := 0

/-- A Number with positive sign, greater than or equal to +0𝔽 and less than 1𝔽, decided. -/
def unitB (n : Impl.Num) : Bool :=
  match Impl.numView n with
  | .posZero => true
  | .finite m => Impl.lt (Impl.ofNat 0) m && Impl.lt m (Impl.ofNat 1)
  | _ => false

/-- Math.random under the seed `n`: a multiple of 2^-53 in [0, 1), by the pseudo-random word at the host-call
log's length. -/
def seededRandom (n : Nat) : Run Impl (Val Impl) := fun s =>
  let x := Impl.numOf (Model.MathVal.ofQ (mkRat (draw n randomKey s.hostLog.length % 2 ^ 53) (2 ^ 53)))
  .ok (.num (if unitB x then x else Impl.numZero false)) s

/-- The host-defined and implementation-defined operations, by sec-id; a job is queued by its call's log entry;
HostGetCodeForEval's default, ~no-code~; the list separator ", "; `seededRandom` at the default seed for
Math.random, the UTC offset 0 for every time zone, residue for GetNamedTimeZoneEpochNanoseconds (only UTC: its
default implementation runs). -/
def hooks : List (String × Hook) := [
  ("sec-hostenqueuegenericjob", fun _ vs => match vs with
    | [_, _] => Run.pure unused
    | _ => Run.stop .sortError),
  ("sec-hostenqueuepromisejob", fun _ vs => match vs with
    | [_, _] => Run.pure unused
    | _ => Run.stop .sortError),
  ("sec-hostenqueuetimeoutjob", fun _ vs => match vs with
    | [_, _, _] => Run.pure unused
    | _ => Run.stop .sortError),
  ("sec-hostensurecanaddprivateelement", fun _ _ => Run.pure (normal unused)),
  ("sec-hostensurecancompilestrings", fun _ _ => Run.pure (normal unused)),
  ("sec-hostgetcodeforeval", fun _ _ => enumNamed N "no-code"),
  ("sec-hosthassourcetextavailable", fun _ _ => Run.pure (.bool true)),
  ("sec-hostgetimportmetaproperties", fun _ _ => listOf []),
  ("sec-hostfinalizeimportmeta", fun _ _ => Run.pure unused),
  ("sec-hostgetsupportedimportattributes", fun _ _ => listOf [.str (Impl.strLit "type")]),
  ("sec-hostresizearraybuffer", fun _ _ => normalEnum N "unhandled"),
  ("sec-hostgrowsharedarraybuffer", fun _ _ => normalEnum N "unhandled"),
  ("sec-localizedlistseparator", fun _ _ => Run.pure (.str (Impl.strLit ", "))),
  ("sec-host-promise-rejection-tracker", fun _ _ => Run.pure unused),
  ("sec-math.random", fun _ _ => seededRandom defaultSeed),
  ("sec-getnamedtimezoneoffsetnanoseconds", fun _ _ => Run.pure (.math (Impl.ofNat 0))),
  ("sec-getnamedtimezoneepochnanoseconds", fun _ _ => Run.stop .residue)]

/-- The clause `print`'s behaviour calls to write a line. -/
def printClause : ClauseId := 2000000

/-- `print`'s behaviour. -/
def printAlg : AlgId := ⟨2000001, 0⟩

def clearKeptSec : String := "sec-clear-kept-objects"

/-- `print(value)`: `? ToString(value)`, written as a line; *undefined*. -/
def printBuiltin : Alg := {
  id := printAlg
  name := "print"
  header := { kind := .builtin, params := [{ x := 2, ty := none, optional := false, rest := false }],
              ret := none, recv := none }
  vars := #["this value", "NewTarget", "value", "string"]
  body := [.let_ 3 (.q (.call (.alg ⟨(N.clauseOf? "sec-tostring").getD 0, 0⟩) [.var 2])),
    .perform (.call (.alg ⟨printClause, 0⟩) [.var 3]),
    .ret (some (.val .undefined))]
  closures := #[] }

/-- `print`'s line, written to the host's output. -/
def printLine (c : Cells) : List (Val Impl) → Run Impl (Val Impl)
  | [.str s] => do writeElems c.out ((← readList c.out) ++ [.str s]); return unused
  | _ => Run.stop .sortError

/-- `$262.detachArrayBuffer`'s behaviour. -/
def detachAlg : AlgId := ⟨2000005, 0⟩

/-- `$262.detachArrayBuffer(buffer)`: `? RequireInternalSlot(buffer, [[ArrayBufferData]])`, a *TypeError*
for a SharedArrayBuffer, then `? DetachArrayBuffer(buffer)` (no key: a buffer whose [[ArrayBufferDetachKey]] is ~empty~); *null*. -/
def detachBuiltin : Alg :=
  let alg (sec : String) : Callee := .alg ⟨(N.clauseOf? sec).getD 0, 0⟩
  { id := detachAlg
    name := "$262.detachArrayBuffer"
    header := { kind := .builtin, params := [{ x := 2, ty := none, optional := false, rest := false }],
                ret := none, recv := none }
    vars := #["this value", "NewTarget", "buffer"]
    body := [.perform (.q (.call (alg "sec-requireinternalslot") [.var 2, .fieldName ((N.field? "ArrayBufferData").getD 0)])),
      .if_ (.preds (.call (alg "sec-issharedarraybuffer") [.var 2]) (.isVal false false [.val .true]) [])
        (.inline (.throwVal (.call (.alg Known.algNewError) [.fieldName ((N.field? "TypeError").getD 0)]))) [] none,
      .perform (.q (.call (alg "sec-detacharraybuffer") [.var 2])),
      .ret (some (.val .null))]
    closures := #[] }

/-- `$262.createRealm`'s behaviour. -/
def createRealmAlg : AlgId := ⟨2000006, 0⟩

/-- `$262.createRealm()`: InitializeHostDefinedRealm, its execution context then removed and the
caller's restored as the running one; `? Get` of the new realm's global object's *"$262"*. -/
def createRealmBuiltin : Alg :=
  let alg (sec : String) : Callee := .alg ⟨(N.clauseOf? sec).getD 0, 0⟩
  let running : Expr := .call (.prim Known.pRunning) []
  { id := createRealmAlg
    name := "$262.createRealm"
    header := { kind := .builtin, params := [], ret := none, recv := none }
    vars := #["this value", "NewTarget", "callerContext", "status", "newContext", "realm"]
    body := [.let_ 2 running,
      .let_ 3 (.call (alg "sec-completion-ao") [.call (alg "sec-initializehostdefinedrealm") []]),
      .let_ 4 running,
      .let_ 5 (.call (.prim Known.pCurrentRealm) []),
      .removeRestore (.var 4) (.var 2),
      .perform (.q (.var 3)),
      .ret (some (.q (.call (alg "sec-get-o-p")
        [.field (.var 5) ((N.field? "GlobalObject").getD 0), .val (.str "$262")])))]
    closures := #[] }

/-- `$262.evalScript`'s behaviour. -/
def evalScriptAlg : AlgId := ⟨2000007, 0⟩

/-- `$262.evalScript(sourceText)`: a *TypeError* for a non-String; ParseScript(_sourceText_, the current
Realm Record, *undefined*) (a List of errors: a throw completion of the first); else
Completion(ScriptEvaluation(_s_)). -/
def evalScriptBuiltin : Alg :=
  let alg (sec : String) : Callee := .alg ⟨(N.clauseOf? sec).getD 0, 0⟩
  let errors : Cond := .preds (.var 4) (.isTy false false [.listOf (.sort [] ((N.sort? "error").getD 0))]) []
  { id := evalScriptAlg
    name := "$262.evalScript"
    header := { kind := .builtin, params := [{ x := 2, ty := none, optional := false, rest := false }],
                ret := none, recv := none }
    vars := #["this value", "NewTarget", "sourceText", "realm", "s", "status"]
    body := [.if_ (.preds (.var 2) (.isTy true false [.sort [] Known.sString]) [])
        (.inline (.throwVal (.call (.alg Known.algNewError) [.fieldName ((N.field? "TypeError").getD 0)]))) [] none,
      .let_ 3 (.call (.prim Known.pCurrentRealm) []),
      .let_ 4 (.call (alg "sec-parse-script") [.var 2, .var 3, .val .undefined]),
      .if_ errors (.inline (.ret (some (.call (alg "sec-throwcompletion")
        [.index (.var 4) (.math .none (.num (.dec 0)))])))) [] none,
      .let_ 5 (.call (alg "sec-runtime-semantics-scriptevaluation") [.var 4]),
      .ret (some (.call (alg "sec-completion-ao") [.var 5]))]
    closures := #[] }

/-- `$262.IsHTMLDDA`'s behaviour. -/
def isHTMLDDAAlg : AlgId := ⟨2000009, 0⟩

/-- `$262.IsHTMLDDA(...args)`: *null*, whatever the arguments. -/
def isHTMLDDABuiltin : Alg :=
  { id := isHTMLDDAAlg
    name := "$262.IsHTMLDDA"
    header := { kind := .builtin, params := [], ret := none, recv := none }
    vars := #["this value", "NewTarget"]
    body := [.ret (some (.val .null))]
    closures := #[] }

/-! HostLoadImportedModule: a host algorithm (`loaderBuiltin`) over the module map, whose clauses
are the host's own. -/

/-- HostLoadedModule(specifier, type): the module map's Module Record for _specifier_ and _type_ (a
String, or ~empty~ for no *"type"* attribute), else ~empty~. -/
def loadedClause : ClauseId := 2000002

/-- HostModuleLoaded(specifier, type, module): ~unused~; its log entry maps _specifier_ and _type_ to
_module_. -/
def storeClause : ClauseId := 2000003

/-- HostModuleSource(specifier): the source text of the module _specifier_ names, else ~empty~. -/
def sourceClause : ClauseId := 2000004

/-- HostModuleKey(referrer, specifier): the module map's key of _specifier_ as _referrer_ imports it. -/
def keyClause : ClauseId := 2000008

def empty : Val Impl := .enum Known.eEmpty

/-- Two module types, the same one: ~empty~ both, or equal Strings. -/
def sameType : Val Impl → Val Impl → Bool
  | .str a, .str b => Impl.strEq a b
  | .enum a, .enum b => a == b
  | _, _ => false

/-- The Record the earliest logged HostModuleLoaded call with a specifier equal to `k` and the type
`t` recorded. -/
def loadedIn (log : List (HostCall Impl)) (k : Impl.Str) (t : Val Impl) : Option (Val Impl) :=
  log.reverse.findSome? fun
    | .hook c [.str k', t', .ref a] _ _ _ =>
      if c == storeClause && Impl.strEq k k' && sameType t t' then some (.ref a) else none
    | _ => none

/-- HostLoadedModule's answer: `loadedIn` over the log, else ~empty~. -/
def loadedModule : List (Val Impl) → Run Impl (Val Impl)
  | [.str k, t] => fun s => .ok ((loadedIn s.hostLog k t).getD empty) s
  | _ => Run.stop .sortError

/-- HostModuleLoaded's answer. -/
def moduleLoaded : List (Val Impl) → Run Impl (Val Impl)
  | [.str _, _, _] => Run.pure unused
  | _ => Run.stop .sortError

/-- HostModuleSource's answer: the source `c.modules` has under the specifier, else ~empty~. -/
def moduleSource (c : Cells) : List (Val Impl) → Run Impl (Val Impl)
  | [.str k] => Run.pure (((c.modules.find? fun m => Impl.strEq k (Impl.strLit m.1)).map
      fun m => .str (Impl.strLit m.2)).getD empty)
  | _ => Run.stop .sortError

/-- The key the earliest logged HostModuleLoaded call recorded the Module Record at `a` under. -/
def keyIn (log : List (HostCall Impl)) (a : Impl.Addr) : Option Impl.Str :=
  log.reverse.findSome? fun
    | .hook c [.str k, _, .ref a'] _ _ _ => if c == storeClause && Impl.addrEq a a' then some k else none
    | _ => none

/-- The key the referrer `r` was loaded under: none for a Script or a Realm. -/
def referrerKey (log : List (HostCall Impl)) : Val Impl → Option Impl.Str
  | .ref a => keyIn log a
  | _ => none

/-- HostModuleKey's answer: with `c.resolve`, d8's key (`Bundle.resolve`) of the specifier against the
referrer's (`referrerKey`), else the specifier. -/
def moduleKey (c : Cells) : List (Val Impl) → Run Impl (Val Impl)
  | [r, .str k] => fun s =>
    if c.resolve then
      .ok (.str (Impl.strLit (Bundle.resolve ((referrerKey s.hostLog r).map Bundle.ofUnits) (Bundle.ofUnits k)))) s
    else .ok (.str k) s
  | _ => Run.stop .sortError

/-- The host's own clauses: `print`'s line, the module map's and the agent API's; residue for any other. -/
def ownHook (c : Cells) (k : ClauseId) (vs : List (Val Impl)) : Run Impl (Val Impl) :=
  if k == printClause then printLine c vs
  else if k == loadedClause then loadedModule vs
  else if k == storeClause then moduleLoaded vs
  else if k == sourceClause then moduleSource c vs
  else if k == keyClause then moduleKey c vs
  else if isAgentClause k then agentHook k vs
  else Run.stop .residue

/-- The hook: a host-defined operation by its sec-id (residue where `hooks` has none), else the host's
own (`ownHook`; `Names.clauseName` names a residue's clause). -/
def hook (c : Cells) (k : ClauseId) (vs : List (Val Impl)) : Run Impl (Val Impl) :=
  (N.clause k).elim (ownHook c k vs) fun sec => ((hooks N).lookup sec).getD (fun _ _ => Run.stop .residue) c vs

/-- HostLoadImportedModule's algorithm. -/
def loaderAlg : AlgId := ⟨(N.clauseOf? "sec-HostLoadImportedModule").getD 0, 0⟩

/-- HostLoadImportedModule(referrer, moduleRequest, hostDefined, payload): _specifier_ is the key of
moduleRequest.[[Specifier]] as _referrer_ imports it (HostModuleKey); _type_ is the [[Value]] of
moduleRequest.[[Attributes]]'s *"type"* entry, else ~empty~; the module map's Module Record for
_specifier_ and _type_; else, without a source, a throw completion of a new
*TypeError*; for *"json"*, Completion(ParseJSONModule(source)), its normal value added to the map; for
another String, a throw completion of a new *TypeError*; else the source parsed by ParseModule in the
current Realm (a List of errors: a throw completion of the first), added to the map; then
FinishLoadingImportedModule, synchronously. -/
def loaderBuiltin : Alg :=
  let alg (sec : String) : Callee := .alg ⟨(N.clauseOf? sec).getD 0, 0⟩
  let fld (n : String) : FieldId := (N.field? n).getD 0
  let isEmpty (x : Slot) : Cond := .preds (.var x) (.isVal false false [.enum Known.eEmpty]) []
  let isStr (x : Slot) (v : String) : Cond := .preds (.var x) (.isVal false false [.val (.str v)]) []
  let errors : Cond := .preds (.var 5) (.isTy false false [.listOf (.sort [] ((N.sort? "error").getD 0))]) []
  let isNormal : Cond := .preds (.var 7) (.isTy false false [.sort [] Known.sNormalComp]) []
  let normalC (e : Expr) : Expr := .call (alg "sec-normalcompletion") [e]
  let throwC (e : Expr) : Expr := .call (alg "sec-throwcompletion") [e]
  let typeError : Expr := .call (.alg Known.algNewError) [.fieldName (fld "TypeError")]
  let parse : Expr := .call (alg "sec-parsemodule") [.var 6, .call (.prim Known.pCurrentRealm) [], .enum Known.eEmpty]
  let param (x : Slot) : Param := { x, ty := none, optional := false, rest := false }
  { id := loaderAlg N
    name := "HostLoadImportedModule"
    header := { kind := .ao, params := [param 0, param 1, param 2, param 3], ret := none, recv := none }
    vars := #["referrer", "moduleRequest", "hostDefined", "payload", "specifier", "module", "sourceText", "result",
      "type", "attr"]
    body := [.let_ 4 (.call (.alg ⟨keyClause, 0⟩) [.var 0, .field (.var 1) (fld "Specifier")]),
      .let_ 8 (.enum Known.eEmpty),
      .forEach 9 none (.field (.var 1) (fld "Attributes")) false (.block [
        .if_ (.preds (.field (.var 9) (fld "Key")) (.isVal false false [.val (.str "type")]) [])
          (.inline (.set (.var 8) (.field (.var 9) (fld "Value")))) [] none]),
      .let_ 5 (.call (.alg ⟨loadedClause, 0⟩) [.var 4, .var 8]),
      .if_ (isEmpty 5) (.block [
          .let_ 6 (.call (.alg ⟨sourceClause, 0⟩) [.var 4]),
          .if_ (isEmpty 6) (.inline (.let_ 7 (throwC typeError)))
            [.mk (some (isStr 8 "json")) (.block [
              .let_ 7 (.call (alg "sec-completion-ao") [.call (alg "sec-parse-json-module") [.var 6]]),
              .if_ isNormal (.inline (.perform (.call (.alg ⟨storeClause, 0⟩)
                [.var 4, .var 8, .field (.var 7) (fld "Value")]))) [] none]),
             .mk (some (.preds (.var 8) (.isVal true false [.enum Known.eEmpty]) [])) (.inline (.let_ 7 (throwC typeError)))]
            (some (.mk none (.block [
            .set (.var 5) parse,
            .if_ errors (.inline (.let_ 7 (throwC (.index (.var 5) (.math .none (.num (.dec 0))))))) []
              (some (.mk none (.block [
                .perform (.call (.alg ⟨storeClause, 0⟩) [.var 4, .var 8, .var 5]),
                .let_ 7 (normalC (.var 5))])))])))])
        [] (some (.mk none (.inline (.let_ 7 (normalC (.var 5)))))),
      .perform (.call (alg "sec-FinishLoadingImportedModule") [.var 0, .var 1, .var 3, .var 7]),
      .ret (some (.enum Known.eUnused))]
    closures := #[] }

/-! The agent's first Job: the program, as algorithms of the host's (§9.6: a host evaluates its scripts and
modules in Jobs of its own). -/

def runScriptAlg : AlgId := ⟨2000040, 0⟩
def runModuleAlg : AlgId := ⟨2000041, 0⟩
def parseScriptAlg : AlgId := ⟨2000042, 0⟩
def parseModuleAlg : AlgId := ⟨2000043, 0⟩

/-- An algorithm that runs the program (`firstBuiltins`): the driver's own steps, which a trace and the debugger
leave out. -/
def driverAlg (a : AlgId) : Bool := runScriptAlg.clause ≤ a.clause && a.clause ≤ parseModuleAlg.clause

/-- The host's algorithms that run a program:

* HostRunScript(sourceText, realm): ParseScript; a List of errors is a throw completion of the first; else
  ScriptEvaluation of the Script Record.
* HostRunModule(sourceText, realm, key): ParseModule (errors so); the Module Record in the host's module map
  under `key`; LoadRequestedModules, whose promise is settled (the host loads synchronously), a rejection a throw
  completion of its reason; Link, an abrupt completion returned; then Evaluate.
* HostParseScript, HostParseModule(sourceText, realm): the parse alone, *undefined* where it has no errors. -/
def firstBuiltins : List Alg :=
  let alg (sec : String) : Callee := .alg ⟨(N.clauseOf? sec).getD 0, 0⟩
  let fld (n : String) : FieldId := (N.field? n).getD 0
  let param (x : Slot) : Param := { x, ty := none, optional := false, rest := false }
  let errors (x : Slot) : Cond := .preds (.var x) (.isTy false false [.listOf (.sort [] ((N.sort? "error").getD 0))]) []
  let throwFirst (x : Slot) : Stmt :=
    .if_ (errors x) (.inline (.ret (some (.call (alg "sec-throwcompletion") [.index (.var x) (.math .none (.num (.dec 0)))])))) [] none
  let state (x : Slot) (e : String) : Cond :=
    .preds (.field (.var x) (fld "PromiseState")) (.isVal false false [.enum ((N.enum? e).getD 0)]) []
  let mk (id : AlgId) (name : String) (n : Nat) (vars : Array String) (body : List Stmt) : Alg :=
    { id, name, header := { kind := .ao, params := (List.range n).map param, ret := none, recv := none },
      vars, closures := #[], body }
  [mk runScriptAlg "HostRunScript" 2 #["sourceText", "realm", "s"] [
      .let_ 2 (.call (alg "sec-parse-script") [.var 0, .var 1, .val .undefined]),
      throwFirst 2,
      .ret (some (.call (alg "sec-runtime-semantics-scriptevaluation") [.var 2]))],
    mk runModuleAlg "HostRunModule" 3 #["sourceText", "realm", "key", "m", "p", "l"] [
      .let_ 3 (.call (alg "sec-parsemodule") [.var 0, .var 1, .enum Known.eEmpty]),
      throwFirst 3,
      .perform (.call (.alg ⟨storeClause, 0⟩) [.var 2, .enum Known.eEmpty, .var 3]),
      .let_ 4 (.call (alg "sec-LoadRequestedModules") [.var 3]),
      .if_ (state 4 "rejected") (.inline (.ret (some (.call (alg "sec-throwcompletion")
        [.field (.var 4) (fld "PromiseResult")])))) [] none,
      .assert (state 4 "fulfilled"),
      .let_ 5 (.call (alg "sec-completion-ao") [.call (alg "sec-moduledeclarationlinking") [.var 3]]),
      .if_ (.preds (.var 5) (.isTy true false [.sort [] Known.sNormalComp]) [])
        (.inline (.ret (some (.var 5)))) [] none,
      .ret (some (.call (alg "sec-moduleevaluation") [.var 3]))],
    mk parseScriptAlg "HostParseScript" 2 #["sourceText", "realm", "s"] [
      .let_ 2 (.call (alg "sec-parse-script") [.var 0, .var 1, .val .undefined]),
      throwFirst 2,
      .ret (some (.call (alg "sec-normalcompletion") [.val .undefined]))],
    mk parseModuleAlg "HostParseModule" 2 #["sourceText", "realm", "m"] [
      .let_ 2 (.call (alg "sec-parsemodule") [.var 0, .var 1, .enum Known.eEmpty]),
      throwFirst 2,
      .ret (some (.call (alg "sec-normalcompletion") [.val .undefined]))]]

/-- NaNEncoding(value, w, p): `nanCode w p`. -/
def nanEncoding : List (Val Impl) → Run Impl (Val Impl)
  | [_, .math (.int w), .math (.int p)] => Run.pure (.math (.int (nanCode w.toNat p.toNat)))
  | _ => Run.stop .sortError

/-- An implementation-defined choice of either _a_ or _b_: of two Strings (SetFunctionName's _name_ or
_prefixedName_) the second, else the first. -/
def pairChoice : List (Val Impl) → Run Impl (Val Impl)
  | [.str _, .str b] => Run.pure (.str b)
  | v :: _ => Run.pure v
  | [] => Run.stop .sortError

/-- The code units of ASCII text. -/
def asciiUnits (t : String) : List UInt16 := t.toList.map (·.toNat.toUInt16)

/-- RefHost's `escapeUnits`: an unescaped `/` as `\/`, a LineTerminator as its escape (after a `\`, its
letters only), every other code unit as it is. -/
def patternEscUnits : Bool → List UInt16 → List UInt16
  | _, [] => []
  | true, c :: cs =>
    (if c = 10 then [110] else if c = 13 then [114] else if c = 0x2028 then asciiUnits "u2028"
      else if c = 0x2029 then asciiUnits "u2029" else [c]) ++ patternEscUnits false cs
  | false, c :: cs =>
    if c = 92 then 92 :: patternEscUnits true cs
    else (if c = 47 then [92, 47] else if c = 10 then [92, 110] else if c = 13 then [92, 114]
      else if c = 0x2028 then asciiUnits "\\u2028" else if c = 0x2029 then asciiUnits "\\u2029" else [c]) ++
      patternEscUnits false cs

/-- RefHost's `refEscape`: *"(?:)"* for the empty pattern, else `patternEscUnits`. -/
def refEscape (p : Impl.Str) : Impl.Str :=
  if p.size = 0 then (asciiUnits "(?:)").toArray else (patternEscUnits false p.toList).toArray

/-- EscapePattern's answer: `refEscape` of the pattern (a non-empty pattern that needs no escape is its own). -/
def escapeChoice : List (Val Impl) → Run Impl (Val Impl)
  | [.str p, .str _] => Run.pure (.str (refEscape p))
  | _ => Run.stop .residue

/-- NativeFunctionSource's answer: `nativeAnswer` of _func_.[[InitialName]]'s code units. -/
def nativeChoice : List (Val Impl) → Run Impl (Val Impl)
  | [f] => fun s => nativeAnswer ((initialNameIn s f).map (·.toList.map UInt16.toNat)) s
  | _ => Run.stop .sortError

/-! The global object's host-defined properties (InitializeHostDefinedRealm step 17): `print` and
`$262`, whose objects are made like the realm's own: a function like `isNaN`, an object like `Reflect`. -/

/-- A property key of ASCII text. -/
def keyOf (k : String) : Impl.Str ⊕ Impl.Sym := .inl (Impl.strLit k)

/-- A new data property Record: [[Value]] `v`, [[Writable]] `w`, [[Enumerable]] `e`, [[Configurable]] `c`. -/
def dataProp (v : Val Impl) (w e c : Bool) : Run Impl (Val Impl) := do
  let fs := Impl.recSet (Impl.recSet (Impl.recSet (Impl.recSet Impl.recEmpty Known.fValue v)
    Known.fWritable (.bool w)) Known.fEnumerable (.bool e)) Known.fConfigurable (.bool c)
  return .ref (← alloc (.record Known.sRecord fs))

/-- The object `o`'s internal slots and own properties. -/
def objectOf : Val Impl → Run Impl (Impl.Rec (Val Impl) × Impl.Props (Val Impl))
  | .obj o => do
    match ← readCell o with
    | .object sl ps => return (sl, ps)
    | _ => Run.stop .sortError
  | _ => Run.stop .sortError

/-- The value of the object `o`'s own data property `k`. -/
def ownValue (o : Val Impl) (k : String) : Run Impl (Val Impl) := do
  match Impl.propsGet (← objectOf o).2 (keyOf k) with
  | some (.ref d) => readField (.ref d) Known.fValue
  | _ => Run.stop .sortError

/-- CreateBuiltinFunction(`b`, `n`, `name`, « ») in the realm of the built-in function `f` of length 1
and no other internal slots: `f`'s internal slots, [[Behaviour]] `b` and [[InitialName]] `name`, and
the properties *"length"* and *"name"*. -/
def builtinLike (f : Val Impl) (b : AlgId) (name : String) (n : Nat) : Run Impl (Val Impl) := do
  let (sl, _) ← objectOf f
  let len ← dataProp (.num (Impl.numOf (Impl.ofNat n))) false false true
  let nm ← dataProp (.str (Impl.strLit name)) false false true
  let sl := Impl.recSet (Impl.recSet sl Known.fBehaviour (.alg b)) Known.fInitialName (.str (Impl.strLit name))
  let ps := Impl.propsPut (Impl.propsPut Impl.propsEmpty (keyOf "length") len) (keyOf "name") nm
  return .obj (← alloc (.object sl ps))

/-- CreateBuiltinFunction(`isHTMLDDAAlg`, 0, *"IsHTMLDDA"*, « [[IsHTMLDDA]] ») in the realm of the
built-in function `f`: `builtinLike`'s object with the internal slot `d`, [[IsHTMLDDA]]. -/
def htmlDDA (d : FieldId) (f : Val Impl) : Run Impl (Val Impl) := do
  let (sl, _) ← objectOf f
  let len ← dataProp (.num (Impl.numOf (Impl.ofNat 0))) false false true
  let nm ← dataProp (.str (Impl.strLit "IsHTMLDDA")) false false true
  let sl := Impl.recSet (Impl.recSet (Impl.recSet sl Known.fBehaviour (.alg isHTMLDDAAlg)) Known.fInitialName
    (.str (Impl.strLit "IsHTMLDDA"))) d .undefined
  let ps := Impl.propsPut (Impl.propsPut Impl.propsEmpty (keyOf "length") len) (keyOf "name") nm
  return .obj (← alloc (.object sl ps))

/-- `$262`'s properties `ps` with *"IsHTMLDDA"* (`htmlDDA d` in `f`'s realm, writable and
configurable) where the host supports §B.3.6 and `dda` is its [[IsHTMLDDA]] field `d`. -/
def ddaProps (dda : Option FieldId) (f : Val Impl) (ps : Impl.Props (Val Impl)) : Run Impl (Impl.Props (Val Impl)) :=
  match dda with
  | some d => do
    let o ← htmlDDA d f
    let po ← dataProp o true false true
    return Impl.propsPut ps (keyOf "IsHTMLDDA") po
  | none => Run.pure ps

/-- `ps` with the members `ms` (behaviour, name, length): functions like `f`, writable and configurable. -/
def memberProps (f : Val Impl) (ps : Impl.Props (Val Impl)) :
    List (AlgId × String × Nat) → Run Impl (Impl.Props (Val Impl))
  | [] => Run.pure ps
  | (b, name, n) :: ms => do
    let o ← builtinLike f b name n
    let po ← dataProp o true false true
    memberProps f (Impl.propsPut ps (keyOf name) po) ms

/-- The surrounding agent is its cluster's first (main). -/
def isMain (s : State Impl) : Bool := ((clusterSigs s).head?.map (Val.same (sigOf s s.agent))).getD true

/-- `$262.agent`: an object with internal slots `sl`, main's members or another agent's (`isMain`), functions like `f`. -/
def agentObject (f : Val Impl) (sl : Impl.Rec (Val Impl)) : Run Impl (Val Impl) := do
  let ps ← memberProps f Impl.propsEmpty (if isMain (← Run.get) then mainMembers else agentMembers)
  return .obj (← alloc (.object sl ps))

/-- The property Records of `print`, of `$262` and of `setTimeout` for the global object `g`: `print` and
`setTimeout` as CreateDataPropertyOrThrow makes them, `$262` writable and configurable, an object like `Reflect`
with *"global"*, *"detachArrayBuffer"*, *"createRealm"*, *"evalScript"* and *"agent"* (`agentObject`), and
*"IsHTMLDDA"* by `dda` (`ddaProps`). -/
def newGlobals (dda : Option FieldId) (g : Val Impl) : Run Impl (Val Impl × Val Impl × Val Impl) := do
  let isNaN ← ownValue g "isNaN"
  let print ← builtinLike isNaN printAlg "print" 1
  let detach ← builtinLike isNaN detachAlg "detachArrayBuffer" 1
  let create ← builtinLike isNaN createRealmAlg "createRealm" 0
  let eval ← builtinLike isNaN evalScriptAlg "evalScript" 1
  let (rsl, _) ← objectOf (← ownValue g "Reflect")
  let pg ← dataProp g true false true
  let pd ← dataProp detach true false true
  let pc ← dataProp create true false true
  let pe ← dataProp eval true false true
  let pa ← dataProp (← agentObject isNaN rsl) true false true
  let ps ← ddaProps dda isNaN (Impl.propsPut (Impl.propsPut (Impl.propsPut (Impl.propsPut (Impl.propsPut
    Impl.propsEmpty (keyOf "global") pg) (keyOf "detachArrayBuffer") pd) (keyOf "createRealm") pc) (keyOf "evalScript") pe)
    (keyOf "agent") pa)
  let o ← alloc (.object rsl ps)
  let timeout ← builtinLike isNaN setTimeoutAlg "setTimeout" 2
  return (← dataProp print true true true, ← dataProp (.obj o) true false true, ← dataProp timeout true true true)

/-- `ps` with the property `k` added where it has none. -/
def putNew (ps : Impl.Props (Val Impl)) (k : String) (v : Val Impl) : Impl.Props (Val Impl) :=
  if (Impl.propsGet ps (keyOf k)).isSome then ps else Impl.propsPut ps (keyOf k) v

/-- An object's [[Extensible]] slot is *true*. -/
def extensibleIn (sl : Impl.Rec (Val Impl)) : Bool :=
  match Impl.recGet sl Known.fExtensible with
  | some (.bool b) => b
  | _ => false

/-- HostGlobalProperties(realm, global): `print`, `$262` and `setTimeout` (`newGlobals`, with *"IsHTMLDDA"*
by `dda`), added to _global_ where it has no property of that key, and only where _global_ is extensible
(sec-invariants-of-the-essential-internal-methods). -/
def globalProps (dda : Option FieldId) : List (Val Impl) → Run Impl (Val Impl)
  | [_, .obj a] => do
    let (pp, po, pt) ← newGlobals dda (.obj a)
    let (sl, ps) ← objectOf (.obj a)
    if extensibleIn sl then
      writeCell a (.object sl (putNew (putNew (putNew ps "print" pp) "$262" po) "setTimeout" pt))
    return unused
  | _ => Run.stop .sortError

/-- The key of a code point sequence: its code points as naturals. -/
def fastKey (xs : Impl.Seq Impl.Math) : List Nat := xs.toList.filterMap Model.MathVal.idx

/-- TimeNow's answer: the default clock, one more millisecond at each reading, at least a taken
timeout job's due time, read back from the log's newest entries (`clockNumIn`). -/
def clock : Run Impl (Val Impl) := readClock clockNumIn

/-- ParseDateString's answer: `parseDateNum` of the String's code units, residue where it has none. -/
def parseDate : List (Val Impl) → Run Impl (Val Impl)
  | [.str x] => match parseDateNum (M := Impl) (x.toList.map UInt16.toNat) with
    | some n => Run.pure (.num n)
    | none => Run.stop .residue
  | _ => Run.stop .sortError

/-- A WriteSharedMemory or ReadModifyWriteSharedMemory event. -/
def isWriteIn (s : State Impl) (e : Val Impl) : Bool :=
  N.isRecordOf s "WriteSharedMemory" e || N.isRecordOf s "ReadModifyWriteSharedMemory" e

/-- ApproxPower's answer: `numPow` of the two Numbers. -/
def approxPower : List (Val Impl) → Run Impl (Val Impl)
  | [.num x, .num y] => Run.pure (.num (Model.Num.of (Model.MathVal.numPow x.1 y.1)))
  | _ => Run.stop .sortError

/-- The bit length of an integer's magnitude. -/
def bitLength (i : Int) : Nat := if i = 0 then 0 else Nat.log2 i.natAbs + 1

/-- Whether the BigInt that the method `op` returns for `x` and `y` has more than `maxBits` bits, bounded from the
operands' bit lengths without forming it: for x ** n (|x| ≥ 2, n > 0) n · (bitLength(x) - 1) + 1 when |x| is a power
of 2 (exact), else n · bitLength(x); bitLength(x) + n for x << n (x ≠ 0, n > 0); bitLength(x) + bitLength(y) for
x × y. -/
def bigTooLarge (op : Array UInt16) (x y : Int) : Bool :=
  let lim := Model.MathVal.maxBits
  if op == Impl.strLit "exponentiate" then
    let b := bitLength x
    let bits := if x.natAbs = 1 <<< (b - 1) then y.toNat * (b - 1) + 1 else y.toNat * b
    0 < y && 2 ≤ x.natAbs && decide (lim < bits)
  else if op == Impl.strLit "leftShift" then x != 0 && 0 < y && decide (lim < bitLength x + y.toNat)
  else if op == Impl.strLit "multiply" then x != 0 && y != 0 && decide (lim < bitLength x + bitLength y)
  else if op == Impl.strLit "add" then
    ((0 < x && 0 < y) || (x < 0 && y < 0)) && decide (lim ≤ max (bitLength x) (bitLength y)) &&
      decide (lim < bitLength (x + y))
  else if op == Impl.strLit "subtract" then
    ((0 < x && y < 0) || (x < 0 && 0 < y)) && decide (lim ≤ max (bitLength x) (bitLength y)) &&
      decide (lim < bitLength (x - y))
  else if op == Impl.strLit "asUintN" then
    x < 0 && decide (lim < y.toNat) &&
      (decide (bitLength x < y.toNat) || decide (lim < bitLength (x.emod ((1 : Int) <<< y.toNat))))
  else false

/-- BigIntTooLarge's answer: `bigTooLarge`, a BigInt past 2^30 bits (V8's limit). -/
def bigIntTooLarge : List (Val Impl) → Run Impl (Val Impl)
  | [.str op, .big x, .big y] => Run.pure (.bool (bigTooLarge op x y))
  | _ => Run.stop .sortError

/-- The maximum length of a String (`2^28`, matching V8 on 32-bit targets). -/
def maxStringLength : Nat := 268435456

/-- StringTooLarge's answer: whether `n > maxStringLength`. -/
def stringTooLarge : List (Val Impl) → Run Impl (Val Impl)
  | [.math n] =>
    if Impl.isInt n && !Impl.lt n (Impl.ofNat 0) then Run.pure (.bool (Impl.lt (Impl.ofNat maxStringLength) n))
    else Run.stop .sortError
  | _ => Run.stop .sortError

/-! ForInStep's history read in one pass: `forInHist` at Impl (`forInHistFast_eq`). -/

/-- The elements of the List a value refers to (`listIn`), as its Array's List. -/
def listInFast (s : State Impl) : Val Impl → Option (List (Val Impl))
  | .ref a => match Impl.heapGet s.heap a with
    | some (.list xs _) => some xs.toList
    | _ => none
  | _ => none

/-- The history ForInStep is given, as entries (`forInHist`), its Lists read by `listInFast`. -/
def forInHistFast (s : State Impl) (h : Val Impl) : Option (List (ForInEntry Impl)) :=
  (listInFast s h).bind fun vs => vs.mapM (entryInBy listInFast s)

/-- The choices: not a web browser, an approximated value as 𝔽 of the exact one, an approximated
integer as itself, `nanCode`, the first of two values that round alike, the second of two Strings, no
built-in context initialization, no additional timeout, no time zone name, the
time zone "UTC",
the time `clock`, no spin-wait signal or context resources, a Data Block of at most 2^32 bytes, no debugging
facility; only the UTC time zone, no local political rules, the one identifier *"UTC"*, no non-primary
identifiers, no transition, no global object or `this` value of its own, `print` and `$262` on the global object
(`globalProps`), no error report, no cleanup, for-in enumeration by CreateForInIterator's actions, built-in properties in
document order, SharedArrayBuffer kept, every normative optional feature provided, a pattern as RefHost's escape
(`escapeChoice`: one that needs no escape as itself), the locale-sensitive methods as their forms without a
locale (`caseAsDefault`, `compareBy fastKey`, toString's String), a built-in's source text as the reference
host's (`nativeChoice`), a sort by the stable binary insertion sort, its state handed back with each call (`sortStepBy`),
Date.parse by RefHost's parser, `dateParse` (`parseDate`), the cluster's agents selected round-robin
(`selectNext`), woken by WakeAgent or the timeout (`agentWoken`, `agentTimeout`), a shared read's bytes from
each byte's latest write in the interleaving order (`scWrites`), toISOString's year from 0 to 9999 as four digits, no extension of an intrinsic or
a created object, the default job callbacks, a power of two Numbers as `numPow`, and a BigInt's maximum size of
2^30 bits (`bigTooLarge`); the bytes stay residue. -/
def choice (p : PrimId) (vs : List (Val Impl)) : Run Impl (Val Impl) :=
  if p == Known.pWebBrowser then Run.pure (.bool false)
  else if p == Known.pApprox then Ecma.Prims.Numbers.numberFor vs
  else if p == Known.pNaNEncoding then nanEncoding vs
  else if p == Known.pApproxInteger then match vs with
    | [.math x] => if Impl.isInt x then Run.pure (.math x) else Run.stop .residue
    | _ => Run.stop .sortError
  else if p == Known.pHostChoice then pairChoice vs
  else if p == Known.pHostInitializeBuiltinContext then Run.pure unused
  else if p == Known.pAdditionalTimeout then Run.pure (.math (Impl.ofNat 0))
  else if p == Known.pTimeZoneNameSuffix then Run.pure (.str (Impl.strLit ""))
  else if p == Known.pSystemTimeZoneString then Run.pure (.str (Impl.strLit "UTC"))
  else if p == Known.pTimeNow then clock
  else if p == Known.pSpinWaitHint || p == Known.pDiscardContextResources then Run.pure unused
  else if p == Known.pCanAllocate then match vs with
    | [.math n, .bool _] => Run.pure (.bool !(Impl.lt (Impl.ofNat 4294967296) n))
    | _ => Run.stop .sortError
  else if p == Known.pDebuggerEnabled then Run.pure (.bool false)
  else if p == Known.pSupportsOnlyUTC then Run.pure (.bool true)
  else if p == Known.pHasTimeZoneRules then Run.pure (.bool false)
  else if p == Known.pAvailableNamedTimeZoneIds then listOf [.str (Impl.strLit "UTC")]
  else if p == Known.pIsNonPrimaryTimeZoneId then Run.pure (.bool false)
  else if p == Known.pPrimaryTimeZoneId then Run.pure (.str (Impl.strLit "UTC"))
  else if p == Known.pLastTransitionBefore then Run.pure (.enum Known.eEmpty)
  else if p == Known.pHostGlobalObject || p == Known.pHostThisValue || p == Known.pMayCleanup then
    Run.pure (.enum Known.eEmpty)
  else if p == Known.pHostGlobalProperties then globalProps none vs
  else if p == Known.pHostReportCleanupError || p == Known.pHostReportErrors then Run.pure unused
  else if p == Known.pForInStep then forInChoiceBy forInHistFast vs
  else if p == Known.pPropertyOrder then documentOrder vs
  else if p == Known.pOmitSharedArrayBuffer then Run.pure (.bool false)
  else if p == Known.pHostSupportsOptional then Run.pure (.bool true)
  else if p == Known.pEscapePattern then escapeChoice vs
  else if p == Known.pLocaleUppercase then caseAsDefault Impl.toUpper vs
  else if p == Known.pLocaleLowercase then caseAsDefault Impl.toLower vs
  else if p == Known.pLocaleCompare then compareBy fastKey vs
  else if p == Known.pLocaleNumberString then Run.pure (.enum Known.eEmpty)
  else if p == Known.pLocaleDateString then dateAsDefault vs
  else if p == Known.pNativeFunctionSource then nativeChoice vs
  else if p == Known.pSortStep then sortStepBy Model.MathVal.idx vs
  else if p == Known.pParseDateString then parseDate vs
  else if p == Known.pSuspendAgentUntil then suspendUntil vs
  else if p == Known.pExpandedYearForm then Run.pure (.bool false)
  else if p == Known.pHostExtendIntrinsics || p == Known.pHostExtendObject then Run.pure unused
  else if p == Known.pHostJobCallbackData then Run.pure (.enum Known.eEmpty)
  else if p == Known.pHostPrepareCallJobCallback || p == Known.pHostCleanupCallJobCallback then Run.pure unused
  else if p == Known.pHostSelectAgent then selectNext (fun s => N.isRecordOf s "Agent Record") clusterSigs vs
  else if p == Known.pAgentWoken then agentWoken
  else if p == Known.pAgentTimeout then agentTimeout suspendedAgents
  else if p == Known.pWakeAgent then Run.pure unused
  else if p == Known.pChooseReadsBytesFrom then scWrites (isWriteIn N) vs
  else if p == Known.pApproxPower then approxPower vs
  else if p == Known.pBigIntTooLarge then bigIntTooLarge vs
  else if p == Known.pStringTooLarge then stringTooLarge vs
  else Run.stop .residue

/-! Jobs (§9.5): the queue is the host-call log. -/

def genericJob : String := "sec-hostenqueuegenericjob"
def promiseJob : String := "sec-hostenqueuepromisejob"
def timeoutJob : String := "sec-hostenqueuetimeoutjob"

/-- Log position `k` is a call of one of `secs` whose job the host may take (`own`) and has not been taken. -/
def free (log : List (HostCall Impl)) (own : Nat → Bool) (secs : List String) (k : Nat) : Bool :=
  (log.reverse[k]?.any fun e => secs.any (N.callOf · e)) && own k && !log.any (·.takes k)

/-- The positions taken: the job loop's, and AgentNextJob's answers. -/
abbrev Taken := Std.HashSet Nat × List Impl.Math

/-- `t` with the position a logged call takes, if any. -/
def takeStep (t : Taken) : HostCall Impl → Taken
  | .next (some j) _ => (t.1.insert j, t.2)
  | .choice q _ (.math j) => if q == Known.pAgentNextJob then (t.1, j :: t.2) else t
  | _ => t

/-- The log positions whose jobs have been taken. -/
def takenSet (log : List (HostCall Impl)) : Taken := log.foldl takeStep (∅, [])

/-- Position `k` is taken in `t`. -/
def Taken.has (t : Taken) (k : Nat) : Bool := t.1.contains k || t.2.any (Impl.eq · (Impl.ofNat k))

/-- The first position from `i` of `es` (calls oldest first) calling one of `secs`, that `own` allows, not in `t`. -/
def firstFree (t : Taken) (own : Nat → Bool) (secs : List String) : Nat → List (HostCall Impl) → Option Nat
  | _, [] => none
  | i, e :: es => if secs.any (N.callOf · e) && own i && !t.has i then some i else firstFree t own secs (i + 1) es

/-- `pickJob` in one pass per section: the log reversed once, its taken positions a set. -/
def pickJobFast (own : Nat → Bool) (log : List (HostCall Impl)) : Option Nat :=
  let t := takenSet log
  let r := log.reverse
  (firstFree N t own [genericJob, promiseJob] 0 r).orElse fun _ => firstFree N t own [timeoutJob] 0 r

/-- The next job, `pickJob`'s (`pickJobFast`) of those ready (`jobReady`). -/
def nextJob : Run Impl (Option Nat) := fun s =>
  match pickJobFast N (jobReady s) s.hostLog with
  | some k => .ok (some k) s
  | none => .ok none s

/-- An execution context for `sm`, pushed; its Realm is `sm`.[[Realm]] where `sm` is a Record (a
Script Record or Module Record), else `realm`, and must be a Realm Record. -/
def pushCtx (realm sm : Val Impl) : Run Impl Unit := fun s =>
  match (match sm with | .ref _ => fieldOf s Known.fRealm sm | _ => some realm) with
  | some r =>
    if N.isRecordOf s "Realm Record" r then
      let ec := (N.sort? "execution context").getD Known.sRecord
      let fs := Impl.recSet (Impl.recSet (Impl.recSet Impl.recEmpty Known.fScriptOrModule sm)
        Known.fRealm r) Known.fFunction .null
      let (a, h) := Impl.heapAlloc s.heap (.record ec fs)
      .ok () { s with heap := h, stack := Impl.seqPush s.stack (.ref a), suspended := .absent }
    else .stop .sortError
  | none => .stop .sortError

/-- A job's preparation, on an execution context stack of `base` contexts (an agent's job: its own two, AgentMain's and its realm's): an execution context (`pushCtx`) for
its realm (the host's where it has none) and, for a promise job, the script or module active when it
was scheduled; none where neither has a realm. -/
def prepareJobOn (c : Cells) (base k : Nat) : Run Impl Unit := fun s =>
  match s.hostLog.reverse[k]? with
  | some e@(.hook _ (_ :: realm :: _) sm _ _) =>
    if s.stack.size = base then
      let sm := if N.callOf promiseJob e then sm else .null
      match realm with
      | .null => (do
        match (← readList c.realm).headD .null with
        | .null => Run.pure ()
        | r => pushCtx N r sm) s
      | r => pushCtx N r sm s
    else .stop .assertFailed
  | _ => .stop .sortError

/-- A job's preparation on an empty execution context stack (`prepareJobOn`). -/
def prepareJob (c : Cells) (k : Nat) : Run Impl Unit := prepareJobOn N c 0 k

/-- A job's cleanup: the execution context its preparation pushed is removed; the stack is then empty. -/
def cleanupJob (_ : Nat) : Run Impl Unit := fun s =>
  if s.stack.size = 0 then .ok () s
  else if s.stack.size = 1 then
    .ok () { s with stack := Impl.seqNil, suspended := (Impl.seqGet s.stack (Impl.ofNat 0)).getD .absent }
  else .stop .assertFailed

/-- ClearKeptObjects after the script and after each job (§9.10: "ECMAScript implementations are
expected to call ClearKeptObjects when a synchronous sequence of ECMAScript executions completes"). -/
def clearsKept : Run Impl Bool := Run.pure true

/-- The elapsed time: the default clock's as the host takes `pickJobFast`'s job (`clockElapsedIn`). -/
def elapsed (s : State Impl) : Impl.Math := clockElapsedIn (pickJobFast N (jobReady s)) s.hostLog

/-- The agents' job prims (§9.5 per agent): AgentNextJob is `next`'s position, else ~empty~;
AgentPrepareJob(k) is `prepareJob` on an empty stack, then the Job k's closure; AgentCleanupJob(k) is `cleanupJob`; else `ch`. -/
def agentJobs (c : Cells) (next : Run Impl (Option Nat)) (ch : PrimId → List (Val Impl) → Run Impl (Val Impl))
    (p : PrimId) (vs : List (Val Impl)) : Run Impl (Val Impl) :=
  if p == Known.pAgentNextJob then match vs with
    | [] => do match ← next with
      | some k => return .math (Impl.ofNat k)
      | none => return .enum Known.eEmpty
    | _ => Run.stop .sortError
  else if p == Known.pAgentPrepareJob then match vs with
    | [.math k] => match Engine.Model.MathVal.idx k with
      | some k => do
        prepareJob N c k
        match scheduled (← Run.get).hostLog k with
        | some j@(.clo ..) => return j
        | _ => Run.stop .sortError
      | none => Run.stop .sortError
    | _ => Run.stop .sortError
  else if p == Known.pAgentCleanupJob then match vs with
    | [.math k] => match Engine.Model.MathVal.idx k with
      | some k => do cleanupJob k; return .enum Known.eUnused
      | none => Run.stop .sortError
    | _ => Run.stop .sortError
  else ch p vs

/-- An abrupt completion. -/
def abrupt : Val Impl → Bool
  | .comp t _ _ => t != Known.eNormal
  | _ => false

end Engine.Host
