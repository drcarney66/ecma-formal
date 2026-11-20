module

public import Engine.Cli.Run
public import Debugger.Machine.Watch

@[expose] public section

/-!
# `ecma-dbg`: the native spec-step debugger

```
ecma-dbg [--dbg-in PATH] [--dbg-out PATH] [--dbg-poll PATH]
```

It speaks the debugger's protocol (`Debugger.Protocol`: DAP-shaped JSON lines) on stdin and stdout,
or on the files (devices) `--dbg-in` and `--dbg-out`. `--dbg-poll` names the poll channel, a file
whose first byte a client sets to pause the run (`Debugger.Session`); without it, a run pauses only
by itself. The WebAssembly build (`ecma-dbg-web`, `scripts/build_wasm.py`; tools/dbg/engine-worker.mjs) runs on three
devices.
`launch` gives the program (`program`, a path, or `source`, its text) and ecma-run's options
(`args`); the run is the machine's (accelerated; `--checked` turns its checks on),
from InitializeHostDefinedRealm's realm. A d8 bundle (`--bundle`, or a text that is one) runs as
ecma-run runs it: its entry module is the program, and its other modules are sources of their own
(`Debugger.bundlePrograms`), each sent as `loadedSource` at `arm`. Once launched and configured, the
realm is set up and the preludes run (their steps pause only with `stopInSetup`), the session
armed, and the program run under the step hook (`Debugger.Machine.runW`). Its end is the event `output` with the lines `print` wrote and `terminated` with
ecma-run's result line (with the site of a stop, the machine's record of it) and exit status.
-/

namespace Debugger.Main

open Ecma Engine Ecma.Spec Engine.SpecHost Engine.Host.RealmLookup Engine.SpecRun Engine.Cli Debugger
open Engine.Host (Loaded loadProgram)

/-- The watched dispatcher for `o` over the host `H`. -/
def dispatchW (o : Opts) (H : Host Impl) : Engine.Host.Runner :=
  Debugger.Machine.dispatchW
    { Engine.Machine.ctx P' H o.reading o.checked with
      maxCells := if o.maxHeap == 0 then none else some (cellsFor o.maxHeap) } (obsOf o).sites

/-- The program's text: `source`, else the file `program`. -/
def launchText (l : Req) : IO (Except String String) := do
  match (l.arg? "source").bind Json.str?, (l.arg? "program").bind Json.str? with
  | some s, _ => pure (Except.ok s)
  | none, some p => do
    match ← (IO.FS.readFile p).toBaseIO with
    | Except.ok t => pure (Except.ok t)
    | Except.error e => pure (Except.error s!"cannot read {p}: {e}")
  | none, none => pure (Except.error "launch: no program or source")

/-- The program of the text `text` (`loadProgram`): a d8 bundle, by `--bundle` or found so, else as
the options have it. -/
def loadLaunch (o : Opts) (path : Option String) (text : String) : IO (Except String Loaded) :=
  let bundle := o.bundle || !(Engine.Host.Bundle.parse text matches .ok none)
  loadProgram bundle o.asModule o.parseOnly o.moduleDir (path.getD "source") text

def points (t : String) : Array Nat := (t.toList.map Char.toNat).toArray

/-- The preludes `ps` from the state `s`, each run as a Script with its jobs under the watched
dispatcher. -/
def preludes (o : Opts) (c : Cells) : State F → List (Array Nat) → AfterPreludes
  | s, [] => .ok s
  | s, p :: ps => match runFrom (dispatchW o) o.host o.jobs c s p with
    | .ok v s' => if abrupt v then .ended s p (.ok v s') else preludes o c s' ps
    | r => .ended s p r

/-- The channel's paths: `--dbg-in`, `--dbg-out`, `--dbg-poll`. -/
structure Channel where
  inp : Option String := none
  out : Option String := none
  poll : Option String := none

def channelOf : List String → Except String Channel
  | [] => .ok {}
  | "--dbg-in" :: p :: rest => return { ← channelOf rest with inp := some p }
  | "--dbg-out" :: p :: rest => return { ← channelOf rest with out := some p }
  | "--dbg-poll" :: p :: rest => return { ← channelOf rest with poll := some p }
  | a :: _ => .error s!"ecma-dbg: unknown argument {a} (usage: ecma-dbg [--dbg-in PATH] [--dbg-out PATH] [--dbg-poll PATH])"

/-- The session opened on the channel's files, stdin and stdout by default. -/
def openChannel (ch : Channel) : IO Unit := do
  let inp ← match ch.inp with
    | some p => pure (IO.FS.Stream.ofHandle (← IO.FS.Handle.mk p .read))
    | none => IO.getStdin
  let out ← match ch.out with
    | some p => pure (IO.FS.Stream.ofHandle (← IO.FS.Handle.mk p .write))
    | none => IO.getStdout
  let poll := ch.poll.map System.FilePath.mk
  Debugger.openOn inp out Debugger.Machine.names poll

def main (argv : List String) : IO UInt32 := do
  match channelOf argv with
  | .error e => IO.eprintln e; return 2
  | .ok ch => openChannel ch
  let some l ← Debugger.awaitLaunch | return 0
  let args := ((((l.arg? "args").bind Json.arr?).getD #[]).filterMap Json.str?).toList
  let path := (l.arg? "program").bind Json.str?
  let (o, text) ← match parse {} args, ← launchText l with
    | .error e, _ | _, .error e => Debugger.finish s!"stop: {e}" 2 []; return (0 : UInt32)
    | .ok o, .ok text => pure (o, text)
  let ld ← match ← loadLaunch o path text with
    | .ok ld => pure ld
    | .error e => Debugger.finish s!"stop: bundle: {e}" 2 []; return (0 : UInt32)
  for w in ld.warnings do IO.eprintln w
  let read : IO (List (Array Nat)) := o.preludes.mapM fun (p : String) => do pure (points (← IO.FS.readFile p))
  let pres ← match ← read.toBaseIO with
    | .ok ps => pure (ps ++ ld.scripts.map points)
    | .error e => Debugger.finish s!"stop: {e}" 2 []; return (0 : UInt32)
  let o := withLoaded o ld
  let src := points ld.text
  -- The program from the state after set-up and the preludes.
  let go (c : Cells) (s : State F) : IO Unit := do
    let cm := { c with modules := o.modules, resolve := o.resolve }
    let prog : Debugger.Program := { path, src, stamp := s.parses }
    let (prog, mods) := match o.source with
      | .module key => bundlePrograms prog key ld.bundle
      | _ => (prog, [])
    Debugger.arm (some prog) (some c.out) mods
    let r := runFrom (dispatchW o) o.host o.jobs cm s src o.source
    let (line, code, out, _) ← report o (cm, r)
    Debugger.finish line code out
  -- That state from a snapshot (`ECMA_SNAPSHOT`, as ecma-run's) where there is one, else written as one.
  let dir ← IO.getEnv "ECMA_SNAPSHOT"
  let dir := if o.resolve then none else dir
  let key ← match dir with
    | some _ => snapshotKey args "" [toString (hash pres)]
    | none => pure ""
  let snap ← match dir with
    | some d => readSnapshot d key
    | none => pure none
  match snap with
  | some (c, s) => go c s
  | none => match setup (dispatchW o) o.host SpecRun.s0 with
    | .ok c s =>
      let cm := { c with modules := o.modules, resolve := o.resolve }
      let c := if o.resolve then cm else c
      match preludes o c s pres with
      | .ok s =>
        if let some d := dir then writeSnapshot d key c s
        go c s
      | .ended _ _ r =>
        let (line, code, out, _) ← report o (c, r)
        Debugger.finish line code out
    | r =>
      let (line, code, out, _) ← report o ({ out := (0 : Nat), realm := (0 : Nat) }, setupFailed r)
      Debugger.finish line code out
  return 0

end Debugger.Main

def main (argv : List String) : IO UInt32 := Debugger.Main.main argv
