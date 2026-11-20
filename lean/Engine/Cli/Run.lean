module

public import Engine.Run
public import Ecma.Lower.Expand
public import Engine.Machine
public import Engine.Pins
public import Engine.Cli.Errata
public import Engine.Host.Jobs
public import Lean.CompactedRegion

@[expose] public section

/-!
# `ecma-run`: a whole JS program through the specification

```
ecma-run [--no-accel] [--checked] [--max-heap MB] [--stats] [--snapshot DIR] [--reading literal|test262|proposed]
        [--literal NAME]... [--erratum NAME=literal|test262|proposed]... [--no-blame] [--sites] [--cover] [--host-seed N] [--resize-in-place]
        [--web-browser] [--can-block] [--annex-b SEC]... [--jobs-after-throw] [--prelude FILE]... [--module-dir DIR] [--module] [--bundle] [--parse-only] (FILE | --serve)
```

`FILE`'s code points run as ParseScript and ScriptEvaluation, then the queued jobs (`Engine.SpecRun`),
by the machine at `Impl` (accelerated but with `--no-accel`, checked only with `--checked` but at the errata's
stop sites), from InitializeHostDefinedRealm's realm, over the expanded program (`P`, `Src.expanded`). It prints the result
line (`normal: v`, exit 0; `throw: e`, exit 1), then the lines `print` wrote. A stop prints
`stop: <reason> <site> <step>`, exit 3: the site is the algorithm (`sec-id#index`) and the step whose
transition stopped, the machine's own record (`Machine.Site`); `--no-blame` leaves the site out
(`stop: <reason>`).

`--sites` adds the records `site<TAB>sec-id#idx path` (`site<TAB>-` for a run that does not stop
or a stop with no site) and `caller<TAB>sec-id` for at most 3 callers, innermost first. The
job loop's stop (a job returned an abrupt completion, §9.5: checked, or at its clause's erratum) has the site `sec-jobs -`
and the job's algorithm as its caller.

`--literal NAME` reads the erratum `NAME` (readings.emu's `name=`) literally, the others as before.

A stop (a failed Assert or `!`, a sort error, no result) at a site where the literal text of an
erratum stops (`Ecma.Gen.erratumStops`, readings.emu's `stops=`: the clause and step path, and the
innermost caller when named) prints `stop: erratum <Name> <site>`, exit 3, and with `--sites` the
record `erratum<TAB>Name` after the site's.
`--erratum NAME=READING` (repeated) runs the erratum `NAME` at that reading over `--reading`'s, the
data's by default: one erratum's literal text where another's stops realm setup under `--reading literal`.
`--cover` adds `cover<TAB>sec-id#idx path A|S` for each step the run entered, `A` an Assert.

Each `--prelude FILE` runs as a Script (its jobs after it) in the realm before `FILE`, in order, as
test262's harness files may (INTERPRETING.md, `includes`): the first that does not complete normally
is the program's outcome.

`--module-dir DIR` gives `FILE` (not the preludes) the modules HostLoadImportedModule loads, each
`DIR/NAME` as the specifier `./NAME` (test262's INTERPRETING.md): every `*_FIXTURE.js` and
`*_FIXTURE.json` file, and every `.js`, `.mjs` or `.json` file that `FILE` or a module so loaded names as
`./NAME` (`type: "json"` loads it as a JSON module); any other specifier loads none (a *TypeError*).

`--module` runs `FILE` as the root of a module graph (`Engine.Host.Source.module`): ParseModule, the Module
Record in the module map under `./NAME` (`FILE`'s name, so that it imports itself), then
LoadRequestedModules, Link and Evaluate, the jobs after them; the outcome is Evaluate's promise's
(`throw: e` where it is rejected). `--parse-only` only parses `FILE` (ParseScript, or ParseModule
with `--module`): `throw: e` for its first error, else `normal: undefined`.

`--bundle` reads `FILE` as d8 does with `--bundle` (`Engine.Host.Bundle`): a bundle's one entrypoint
runs as `--module` runs `FILE`, its specifiers resolved as d8 resolves them and loaded from the
bundle's modules (dynamic `import()` too), after the preludes and then the bundle's scripts before
the entrypoint, each as a prelude; a file that is not a bundle runs as a Script. A bundle that d8
refuses (a duplicate module), or that does not run one entrypoint, prints `stop: bundle: <error>`,
exit 2; an unknown marker's warning goes to stderr.

The host is the fixed one (`Engine.SpecHost.host`) but for the test-host options (`hostBy`): `--host-seed
N` answers its open choices by a seed, `--resize-in-place` resizes ArrayBuffers in place, `--web-browser`
makes it a web browser (Annex B's features on), `--annex-b SEC` a host that otherwise supports the Annex B
clause SEC (its "web browser or otherwise supports" choice true there), `--can-block` makes the surrounding agent one that can block ([[CanBlock]] *true*, test262's
`CanBlockIsTrue`), and `--jobs-after-throw` runs the jobs after an abrupt script completion (RunScriptAndJobs; the default
is RunScriptInNewRealm).

`--max-heap MB` (default `defaultMaxHeap`, 0 for none) is the process's memory ceiling: the store only grows (no
cell is ever freed), and a run whose store passes the cells that fit stops with `stop: implLimit`, exit 3.
`--stats` prints the store's size at the end on stderr (`cells<TAB>N`).

A run has no other bound of its own: the run loop is the engine's (`Engine.Machine.runT`, proved to run the
engine's transitions: `Engine.run_sound`), and a limit on time or memory is its caller's.

`--serve` reads requests `PATH<TAB>OPTIONS` from stdin, OPTIONS among `--host-seed N`,
`--resize-in-place`, `--web-browser`, `--can-block`, `--annex-b SEC`, `--jobs-after-throw`, `--literal NAME`, `--reading MODE`, `--erratum NAME=MODE` over the command line's, `--prelude FILE`
(the request's own, in place of the command line's), `--module-dir DIR`, `--module` `--bundle` and `--parse-only` (the
request's own), and answers each with the records `outcome<TAB>line`,
`print<TAB>text` per printed line, the `site`, `caller` and `erratum` records of `--sites`, the `cover`
records with `--cover`, and `cpu<TAB>ms`, then a line `.`; a
backslash, tab or newline in a record's text is written `\\`, `\t` or `\n`. The realm is set up once
per host options and reading options, its state and the machine's records after it reused, and so is the
state after each prefix of the preludes (by their text; the last `preludeCacheSize`).

With `JS_TRACE_STEPS=1` in the environment, the machine prints each step it enters on stderr
(`sec-id 2.a. Let x be …`), after the line `ecma-run: trace`.
-/

namespace Engine.Cli

open Ecma Engine Ecma.Spec Engine.SpecHost Engine.Host.RealmLookup Engine.SpecRun
open Engine.Host (jobSite Loaded loadProgram)

/-- `--max-heap`'s default, in megabytes. -/
def defaultMaxHeap : Nat := 512

/-- What a cell of the store costs, in bytes, with what it holds, and what the process takes with an empty
store, in megabytes: measured on a loop and on an allocating program (241 bytes a cell on both). -/
def cellBytes : Nat := 241

def baseMegabytes : Nat := 65

/-- The store's ceiling in cells for a process of `mb` megabytes. -/
def cellsFor (mb : Nat) : Nat := (mb - baseMegabytes) * 1048576 / cellBytes

structure Opts where
  checked : Bool := false
  noAccel : Bool := false
  checkPins : Bool := false
  /-- `--max-heap MB`: the store's ceiling, in megabytes (0: none). -/
  maxHeap : Nat := defaultMaxHeap
  /-- `--stats`: the store's size at the end, on stderr. -/
  stats : Bool := false
  /-- `--snapshot DIR` (else the environment's `ECMA_SNAPSHOT`): where the states after set-up and the preludes are
  kept. -/
  snapshot : Option String := none
  /-- The program's units under `reading`, for the step records (`unitsFor`): made once, as the readings are settled. -/
  units : Thunk Engine.Machine.Units := Thunk.pure {}
  reading : ErratumId → Reading := readingOf
  /-- The errata `--literal` names, read literally over `reading`. -/
  literals : List ErratumId := []
  /-- `--erratum`'s readings, over `reading`. -/
  erratumReadings : List (String × Reading) := []
  /-- A `--serve` request's `--reading` and `--erratum` options, as given. -/
  readingArgs : List String := []
  file : Option String := none
  trace : Bool := false
  blame : Bool := true
  sites : Bool := false
  cover : Bool := false
  host : HostOpts := {}
  jobs : JobPolicy := .inNewRealm
  serve : Bool := false
  preludes : List String := []
  moduleDir : Option String := none
  /-- `moduleDir`'s modules, by specifier. -/
  modules : List (String × String) := []
  asModule : Bool := false
  /-- `file` is a d8 bundle (`Engine.Host.loadProgram`). -/
  bundle : Bool := false
  /-- `modules` are by d8's keys. -/
  resolve : Bool := false
  parseOnly : Bool := false
  /-- What `file` is (`Engine.Host.sourceFor`). -/
  source : Source := .script

/-- The stderr line before ecma-run's own trace. -/
def traceMark : String := "ecma-run: trace"


/-- What the machine's runs keep beside them for `o`. -/
def obsOf (o : Opts) : Machine.Obs := { trace := o.trace, sites := o.blame || o.sites || o.serve, cover := o.cover }

/-- The program's units under the readings `rd`, found on first use. -/
def unitsFor (rd : ErratumId → Reading) : Thunk Engine.Machine.Units :=
  Thunk.mk fun _ =>
    let keys := Engine.Machine.specKeys
    Engine.Machine.unitsMemo P rd Engine.Machine.specRows (keys.1 ++ keys.2.1 ++ hostIds)

/-- `o` with its readings settled: `--erratum`'s over `--reading`'s, and the units under them. -/
def Opts.settle (o : Opts) : Opts :=
  let rd := readingsOver Ecma.Gen.errata o.erratumReadings o.reading
  { o with reading := rd, units := unitsFor rd }

/-- The runner of `o` over the host `H`: the engine's set-up (`Engine.setupAt`, the one `Engine.implementation`
is). -/
def dispatchOf (o : Opts) (H : Host F) : Engine.Host.Runner :=
  let mc := if o.maxHeap == 0 then none else some (cellsFor o.maxHeap)
  Engine.Machine.dispatch (Engine.setupAt H mc (!o.noAccel) o.reading o.checked) o.units (obsOf o)

/-- `src`'s run (as `sr` has it) from the state `s` over the cells `c` (`runFrom`). -/
def runNoted (o : Opts) (c : Cells) (s : State F) (src : Array Nat) (sr : Source := .script) : Res F (Val F) :=
  runFrom (dispatchOf o) o.host o.jobs c s src sr


/-! Preludes. -/

/-- How the preludes ended: the state after them all, or the first that did not complete normally,
with the state it started from, its source and its result. -/
inductive AfterPreludes where
  | ok (s : State F)
  | ended (s : State F) (src : Array Nat) (r : Res F (Val F))

/-- The preludes `ps` from the state `s`, each run as a Script with its jobs. -/
def afterPreludes (o : Opts) (c : Cells) : State F → List (Array Nat) → AfterPreludes
  | s, [] => .ok s
  | s, p :: ps => match runNoted o c s p with
    | .ok v s' => if abrupt v then .ended s p (.ok v s') else afterPreludes o c s' ps
    | r => .ended s p r

/-- `src`'s run from the set-up `set` after the preludes `after` (`plain`: none), with `o`'s modules
(a bundle's preludes too): the cells and the result (the program's, or the prelude's that ended it). -/
def runAfter (o : Opts) (set : Res F Cells) (after : Cells → State F → AfterPreludes)
    (src : Array Nat) : Cells × Res F (Val F) :=
  match set with
  | .ok c s =>
    let cm := { c with modules := o.modules, resolve := o.resolve }
    let c := if o.resolve then cm else c
    match after c s with
    | .ok s =>
      (cm, runNoted o cm s src o.source)
    | .ended _ _ r => (c, r)
  | r => ({ out := (0 : Nat), realm := (0 : Nat) }, setupFailed r)

/-! Sites, errata and cover records. -/

/-- The site of a run that ended in `r`, if it stopped, and its callers: the machine's record (at most 3
callers, innermost first); a stop without one that follows a job's abrupt completion is the job loop's
(`jobSite`). -/
def stopSiteOf (r : Res F (Val F)) : IO (Option (String × List String)) := do
  if !(r matches .stop _) then return none
  return some <| match ← Machine.stopSite 3 with
    | some ((a, p), cs) => (Machine.siteText Ecma.Gen.clauses a p, cs.map (clauseName ·.clause))
    | none => jobSite clauseName Ecma.Gen.jobErrata.toList r

/-- The `site` and `caller` records of a run whose stop's site is `site` (`--sites`, `--serve`). -/
def siteRecords : Option (String × List String) → List String
  | none => ["site\t-"]
  | some (b, cs) => (if b == "? ?" then "site\t-" else s!"site\t{b}") :: cs.map (s!"caller\t{·}")

/-- The erratum of the stop `r`, cross-checked (`Ecma.erratumText`) against the rows of
`Ecma.Gen.erratumStops` at its site `site` (`sec-id#idx path`, with its callers). -/
def erratumOf (r : Res F (Val F)) : Option (String × List String) → Option String
  | some (b, cs) => match r with
    | .stop x => erratumText Ecma.Gen.erratumStops id (fun e => Ecma.Gen.errata.getD e s!"{e}") x b cs
    | _ => none
  | none => none

/-- The `cover` records of the machine's run (`--cover`). -/
def coverRecords : IO (List String) := Machine.coverRecords Ecma.Gen.clauses

/-! The command line. -/

/-- The readings of the errata `--reading` names (a definition reading is no choice, and none is asked of it). -/
def readingNamed : String → Option (ErratumId → Reading)
  | "literal" => some fun _ => .literal
  | "test262" => some readingOf
  | "proposed" => some fun _ => .proposed
  | _ => none

/-- `o` with the erratum `name` read literally. -/
def literalNamed (o : Opts) (name : String) : Option Opts :=
  (Ecma.Gen.errataIds.idxOf? s!"erratum-{name}").map fun e =>
    { o with reading := fun e' => if e' == e then .literal else o.reading e', literals := e :: o.literals }

/-- Whether `r` is a valid reading for erratum `name`. -/
def validErratumReading (name : String) (r : Reading) : Bool :=
  match Ecma.Gen.errataIds.idxOf? s!"erratum-{name}" with
  | some e => (Ecma.Gen.erratumReadings.getD e []).contains r
  | none => false

/-- The options a `--serve` request may give. -/
partial def parseRequest (o : Opts) : List String → Except String Opts
  | [] => .ok o
  | "--resize-in-place" :: r => parseRequest { o with host.resizeInPlace := true } r
  | "--web-browser" :: r => parseRequest { o with host.webBrowser := true } r
  | "--can-block" :: r => parseRequest { o with host.canBlock := true } r
  | "--annex-b" :: sec :: r =>
    if Engine.Host.annexBClauses.contains sec then parseRequest { o with host.annexB := o.host.annexB ++ [sec] } r
    else .error s!"unsupported --annex-b {sec}"
  | "--jobs-after-throw" :: r => parseRequest { o with jobs := .andJobs } r
  | "--host-seed" :: n :: r => match n.toNat? with
    | some k => parseRequest { o with host.seed := some k } r
    | none => .error s!"--host-seed {n}"
  | "--prelude" :: f :: r => parseRequest { o with preludes := o.preludes ++ [f] } r
  | "--module-dir" :: d :: r => parseRequest { o with moduleDir := some d } r
  | "--module" :: r => parseRequest { o with asModule := true } r
  | "--bundle" :: r => parseRequest { o with bundle := true } r
  | "--parse-only" :: r => parseRequest { o with parseOnly := true } r
  | "--literal" :: n :: r => match literalNamed o n with
    | some o => parseRequest o r
    | none => .error s!"--literal {n}"
  | "--reading" :: m :: r => match readingNamed m with
    | some rd =>
      parseRequest { o with reading := (fun e => if o.literals.contains e then .literal else rd e),
                            readingArgs := o.readingArgs ++ ["--reading", m] } r
    | none => .error s!"--reading {m}"
  | "--erratum" :: a :: r => match erratumReading a with
    | some (n, m) =>
      if validErratumReading n m then
        parseRequest { o with erratumReadings := o.erratumReadings ++ [(n, m)], readingArgs := o.readingArgs ++ ["--erratum", a] } r
      else .error s!"--erratum {a}"
    | none => .error s!"--erratum {a}"
  | a :: _ => .error s!"unsupported {a}"

partial def parse (o : Opts) : List String → Except String Opts
  | [] => .ok o.settle
  | "--checked" :: r => parse { o with checked := true } r
  | "--no-accel" :: r => parse { o with noAccel := true } r
  | "--check-pins" :: r => parse { o with checkPins := true } r
  | "--stats" :: r => parse { o with stats := true } r
  | "--snapshot" :: d :: r => parse { o with snapshot := some d } r
  | "--max-heap" :: n :: r => match n.toNat? with
    | some k => parse { o with maxHeap := k } r
    | none => .error s!"--max-heap {n}"
  | "--no-blame" :: r => parse { o with blame := false } r
  | "--sites" :: r => parse { o with sites := true } r
  | "--cover" :: r => parse { o with cover := true } r
  | "--serve" :: r => parse { o with serve := true } r
  | "--reading" :: m :: r => match readingNamed m with
    | some rd => parse { o with reading := fun e => if o.literals.contains e then .literal else rd e } r
    | none => .error s!"--reading {m}"
  | "--erratum" :: a :: r => match erratumReading a with
    | some (n, m) =>
      if validErratumReading n m then parse { o with erratumReadings := o.erratumReadings ++ [(n, m)] } r
      else .error s!"--erratum {a}"
    | none => .error s!"--erratum {a}"
  | a :: r =>
    if a == "--resize-in-place" || a == "--web-browser" || a == "--can-block" || a == "--jobs-after-throw" ||
        a == "--module" || a == "--bundle" || a == "--parse-only" then
      parseRequest o [a] >>= (parse · r)
    else if a == "--host-seed" || a == "--annex-b" || a == "--prelude" || a == "--module-dir" ||
        a == "--literal" then match r with
      | n :: r => parseRequest o [a, n] >>= (parse · r)
      | [] => .error s!"{a}"
    else if a.startsWith "--" then .error s!"unsupported {a}" else parse { o with file := some a } r

/-- `o` running the program `l` (`Engine.Host.loadProgram`). -/
def withLoaded (o : Opts) (l : Loaded) : Opts :=
  { o with modules := l.modules, resolve := l.resolve, source := l.source }

/-- The result line (with the site of a stop; `stop: erratum <Name> <site>` at a registered erratum's),
exit status, printed lines, stop's site and erratum of a run `(cells, result)`. -/
def report (o : Opts) (cr : Cells × Res F (Val F)) :
    IO (String × UInt32 × List String × Option (String × List String) × Option String) := do
  let (line, code, out) := SpecRun.outcome cr.1 cr.2
  let site ← if o.blame || o.sites || o.serve then stopSiteOf cr.2 else pure none
  let err := erratumOf cr.2 site
  let line := match err, o.blame, site with
    | some e, _, some (b, _) => s!"stop: erratum {e} {b}"
    | _, true, some (b, _) => line ++ " " ++ b
    | _, _, _ => line
  return (line, code, out, site, err)

/-- The records of a stop's site and erratum (`--sites`, `--serve`). -/
def stopRecords (site : Option (String × List String)) (err : Option String) : List String :=
  siteRecords site ++ (err.map (s!"erratum\t{·}")).toList

/-! `--serve`. -/

/-- A record's text: backslash, tab and newline escaped. -/
def escapeRecord (t : String) : String :=
  t.foldl (fun acc ch => acc ++ match ch with
    | '\\' => "\\\\"
    | '\t' => "\\t"
    | '\n' => "\\n"
    | ch => ch.toString) ""

/-- Set-up realms by host options and reading options, each with the machine's records after it. -/
abbrev SetupCache := List ((HostOpts × List ErratumId × List String) × Res F Cells × Machine.ObsRecords)

/-- The set-up realm for `o`'s host options and reading options and the machine's records after it (a failed set-up's
site), from the cache or new. -/
def setupFor (o : Opts) (cache : SetupCache) : IO (Res F Cells × Machine.ObsRecords × SetupCache) := do
  match cache.find? (·.1 == (o.host, o.literals, o.readingArgs)) with
  | some (_, r, k) => return (r, k, cache)
  | none =>
    Machine.resetObs
    let r := setup (dispatchOf o) o.host SpecRun.s0
    let k : Machine.ObsRecords ← match r with
      | .ok .. => do pure { cover := (← Machine.getObs).cover }
      | _ => Machine.getObs
    return (r, k, ((o.host, o.literals, o.readingArgs), r, k) :: cache)

/-- The cached states after prelude prefixes, each with the machine's records after it: their host options,
reading options, a bundle's modules and texts. -/
abbrev PreludeCache :=
  List ((HostOpts × List ErratumId × List String × List (String × String) × List String) ×
    AfterPreludes × Machine.ObsRecords)

def preludeCacheSize : Nat := 64

/-- The preludes `texts` (their sources `srcs`) from the state `s`, resumed from the longest prefix
`cache` holds (its machine records restored); each new prefix's state and records cached. -/
def preludesCached (o : Opts) (c : Cells) (s : State F) (texts : List String) (srcs : List (Array Nat))
    (cache : PreludeCache) : IO (AfterPreludes × PreludeCache) := do
  let key := fun n => (o.host, o.literals, o.readingArgs, (if o.resolve then o.modules else []), texts.take n)
  let hit := (List.range (texts.length + 1)).reverse.findSome? fun n =>
    (cache.find? (·.1 == key n)).map (n, ·.2)
  let (n, start) ← match hit with
    | some (n, a, k) => do Machine.setObs k; pure (n, a)
    | none => pure (0, .ok s)
  let rec go : Nat → AfterPreludes → List (Array Nat) → PreludeCache → IO (AfterPreludes × PreludeCache)
    | _, a@(.ended ..), _, cache => pure (a, cache)
    | _, a, [], cache => pure (a, cache)
    | k, .ok s, p :: ps, cache => do
      let a := afterPreludes o c s [p]
      let r : Machine.ObsRecords ← match a with
        | .ok .. => do pure { cover := (← Machine.getObs).cover }
        | .ended .. => Machine.getObs
      go (k + 1) a ps (((key (k + 1), a, r) :: cache).take preludeCacheSize)
  go n start (srcs.drop n) cache

partial def serveLoop (o : Opts) (stdin stdout : IO.FS.Stream) (cache : SetupCache) (pcache : PreludeCache) :
    IO UInt32 := do
  let line ← stdin.getLine
  if line.isEmpty then return 0
  let line := (line.dropEndWhile (· == '\n')).toString
  let (path, opts) := match line.splitOn "\t" with
    | p :: rest => (p, "\t".intercalate rest)
    | [] => ("", "")
  let emit := fun (r : String) => stdout.putStrLn r
  match parseRequest { o with preludes := [], asModule := false, bundle := false, parseOnly := false }
      ((opts.splitOn " ").filter (!·.isEmpty)) with
  | .error e =>
    emit s!"outcome\t{escapeRecord s!"stop: {e}"}"
    emit "site\t-"
    emit "cpu\t0"
    emit "."
    stdout.flush
    serveLoop o stdin stdout cache pcache
  | .ok o' =>
    let o' := if o'.preludes.isEmpty then { o' with preludes := o.preludes } else o'
    let o' := o'.settle
    let t0 ← IO.monoMsNow
    let fail := fun (e : String) => do
      emit s!"outcome\t{escapeRecord s!"stop: {e}"}"
      emit "site\t-"
      emit "cpu\t0"
      emit "."
      stdout.flush
    match ← (do
        let texts ← (path :: o'.preludes).mapM fun (f : String) => IO.FS.readFile f
        return (texts, ← loadProgram o'.bundle o'.asModule o'.parseOnly o'.moduleDir path (texts.headD "")) : IO _).toBaseIO with
    | .error e =>
      fail s!"cannot read {path}: {e}"
      serveLoop o stdin stdout cache pcache
    | .ok (_, .error e) =>
      fail s!"bundle: {e}"
      serveLoop o stdin stdout cache pcache
    | .ok (texts, .ok l) =>
      for w in l.warnings do IO.eprintln w
      let o' := withLoaded o' l
      let texts := l.text :: texts.tail ++ l.scripts
      let srcs := texts.map fun t => (t.toList.map Char.toNat).toArray
      let src := srcs.headD #[]
      let (set, k, cache) ← setupFor o' cache
      Machine.setObs k
      let (pre, pcache) ← match set with
        | .ok c s => do
          let c := if o'.resolve then { c with modules := o'.modules, resolve := true } else c
          let (a, pc) ← preludesCached o' c s texts.tail srcs.tail pcache
          pure (some a, pc)
        | _ => pure (none, pcache)
      let after : Cells → State F → AfterPreludes := fun _ s => pre.getD (.ok s)
      let (res, _, out, site, err) ← report o' (runAfter o' set after src)
      emit s!"outcome\t{escapeRecord res}"
      for l in out do emit s!"print\t{escapeRecord l}"
      for l in stopRecords site err do emit l
      if o'.cover then for l in ← coverRecords do emit l
      let t1 ← IO.monoMsNow
      emit s!"cpu\t{t1 - t0}"
      emit "."
      stdout.flush
      serveLoop o stdin stdout cache pcache

/-! Snapshots: the state after set-up and the preludes, written once and mapped back.

The state is data: the store's cells, the stacks, the host's log. A snapshot is that data as Lean's runtime lays it
out (a compacted region, as an `.olean` is), so reading one is a memory mapping. The runtime refuses to write a
closure, so a snapshot that is written shows the state holds none. A snapshot is of one build of this program and
one command line: the file's name is a hash of both and of the preludes' texts, and the text hashed is kept in it
and compared. Writing one takes about a kilobyte of memory a cell of the store while it is written:
`ECMA_SNAPSHOT_MAX_CELLS` (0 or unset: no bound) leaves a larger state unwritten, for a caller that bounds this
process's memory. -/

/-- A snapshot: what it is of (`key`), the host's cells, and the state. -/
structure Snapshot where
  key : String
  cells : Cells
  state : State F

/-- What a snapshot is of: this program's file (its size and time), the arguments but the program's file, and
the preludes' texts. -/
def snapshotKey (args : List String) (file : String) (pres : List String) : IO String := do
  let app ← IO.appPath
  let md ← app.metadata
  return s!"{app}|{md.byteSize}|{md.modified.sec}|{md.modified.nsec}|{args.filter (· != file)}|{pres}"

/-- The snapshot's file for a key. -/
def snapshotPath (dir key : String) : System.FilePath :=
  System.FilePath.mk dir / s!"{(hash key).toNat}.ecmasnap"

/-- The snapshot of `key` in `dir`, if there is one. -/
unsafe def readSnapshotImpl (dir key : String) : IO (Option (Cells × State F)) := do
  let path := snapshotPath dir key
  unless ← path.pathExists do return none
  try
    let ((x : Snapshot), _) ← Lean.CompactedRegion.read path #[]
    return if x.key == key then some (x.cells, x.state) else none
  catch _ => return none

@[implemented_by readSnapshotImpl]
opaque readSnapshot (dir key : String) : IO (Option (Cells × State F))

/-- Writes the snapshot of `key`: to a file of its own, then renamed, so that a reader sees all of it or none. A
failure (a closure in the state among them) is reported and the run goes on. -/
unsafe def writeSnapshotImpl (dir key : String) (c : Cells) (s : State F) : IO Unit := do
  let path := snapshotPath dir key
  let tmp := path.withExtension s!"tmp{← IO.monoNanosNow}"
  try
    IO.FS.createDirAll dir
    let x : Snapshot := { key, cells := c, state := s }
    let _ ← Lean.CompactedRegion.save tmp (Lean.Name.mkSimple s!"ecma{hash key}") x #[] none
    IO.FS.rename tmp path
  catch e =>
    IO.eprintln s!"ecma-run: no snapshot written: {e}"
    try IO.FS.removeFile tmp catch _ => pure ()

@[implemented_by writeSnapshotImpl]
opaque writeSnapshot (dir key : String) (c : Cells) (s : State F) : IO Unit

/-- The run of `src` after set-up and the preludes `pres`: from a snapshot of them where `dir` has one, else by
running them, a snapshot then written where they completed. No snapshot is used where the run is observed from its
start (a trace, cover records, a stop's site) or a bundle's modules change the cells. -/
def runSnap (o : Opts) (args : List String) (file : String) (texts : List String) (pres : List (Array Nat))
    (src : Array Nat) : IO (Cells × Res F (Val F)) := do
  let dir ← match o.snapshot with
    | some d => pure (some d)
    | none => IO.getEnv "ECMA_SNAPSHOT"
  let dir := if o.trace || o.cover || o.sites || o.resolve || o.bundle then none else dir
  let fresh : IO (Res F Cells) := do
    let (set, k, _) ← setupFor o []
    Machine.setObs k
    return set
  match dir with
  | none => return runAfter o (← fresh) (fun c s => afterPreludes o c s pres) src
  | some dir =>
    let key ← snapshotKey args file texts
    match ← readSnapshot dir key with
    | some (c, s) => return runAfter o (.ok c s) (fun _ s => .ok s) src
    | none => match ← fresh with
      | .ok c s => match afterPreludes o c s pres with
        | .ok s' =>
          let most := ((← IO.getEnv "ECMA_SNAPSHOT_MAX_CELLS").bind String.toNat?).getD 0
          if most == 0 || s'.heap.size ≤ most then writeSnapshot dir key c s'
          return runAfter o (.ok c s') (fun _ s => .ok s) src
        | a => return runAfter o (.ok c s) (fun _ _ => a) src
      | set => return runAfter o set (fun c s => afterPreludes o c s pres) src

/-- ecma-run, the command line's options over `base`. -/
def main (base : Opts) (args : List String) : IO UInt32 := do
  match parse base args with
  | .error e =>
    IO.println s!"stop: {e}"
    return 2
  | .ok o =>
    let o := { o with trace := (← IO.getEnv "JS_TRACE_STEPS") == some "1" }
    if o.serve then return ← serveLoop o (← IO.getStdin) (← IO.getStdout) [] []
    if o.checkPins then
      let bad := Engine.Machine.failedPins
      for n in bad do IO.println s!"FAIL pin: {n}"
      IO.println s!"{if bad.isEmpty then "ok  " else "FAIL"} pins: {Engine.Machine.pinChecks.length} checked, {bad.length} failed"
      return if bad.isEmpty then 0 else 1
    let some file := o.file | IO.eprintln "usage: ecma-run [options] FILE"; return 6
    let text ← IO.FS.readFile file
    let l ← match ← loadProgram o.bundle o.asModule o.parseOnly o.moduleDir file text with
      | .ok l => pure l
      | .error e => IO.println s!"stop: bundle: {e}"; return 2
    for w in l.warnings do IO.eprintln w
    let src := (l.text.toList.map Char.toNat).toArray
    let texts ← o.preludes.mapM fun (p : String) => IO.FS.readFile p
    let texts := texts ++ l.scripts
    let pres := texts.map fun t => (t.toList.map Char.toNat).toArray
    let o := withLoaded o l
    if o.trace then IO.eprintln traceMark
    let cr ← runSnap o args file texts pres src
    let (line, code, out, site, err) ← report o cr
    IO.println line
    for l in out do IO.println l
    if o.stats then match cr.2 with
      | .ok _ s | .esc _ s => IO.eprintln s!"cells\t{s.heap.size}"
      | .stop _ => IO.eprintln "cells\t-"
    if o.sites then for l in stopRecords site err do IO.println l
    if o.cover then for l in ← coverRecords do IO.println l
    return code

end Engine.Cli
