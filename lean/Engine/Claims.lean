module

public import Engine.Machine
public import Engine.Pins
public import Engine.Host.SpecOpts
public import Engine.Run
public import Ecma.Implements
public import Engine.Proofs.Laws
public import Engine.Proofs.Nodes
public import Engine.Proofs.Parse.Shape
public import Engine.Proofs.Unicode
public import Engine.Proofs.Host.Opts
public import Engine.Proofs.Step.Kinds

@[expose] public section

/-!
# What the engine claims

**The engine implements the specification** (`Ecma.Implements`, `Ecma/Implements.lean`):
`Engine.implements : ∀ o cells mc accel, Ecma.Implements (Engine.implementation o cells mc accel)`, proved with no
hypothesis (`Proofs/Model.lean`, which imports this module and every proof). With it, **every run the engine's run
loop returns is a run of the specification's machine**, or a stop at an implementation limit: `Engine.run_sound`.

The engine as an implementation (`implementation`): its values `Impl` (the model's laws: `Engine.Impl.laws`,
`Engine.Impl.unicodeLaws`); its host under the options `o` over the cells `cells` (`hostBy`; the host's laws:
`Engine.SpecHost.wfBy`, `Proofs/Host/`); its own algorithms, the host's (`hostAlgs`: its built-in functions, the
agent API's, HostLoadImportedModule, the algorithms that run a program), none at an id the specification defines;
its transition `Engine.Machine.stepE` at the set-up `Engine.setupAt`: a stop at the store's ceiling `mc`, else the
accelerator table's shortcut where one answers (with `accel` false, or where a pinned check fails, none), else
the specification's step. Every row of the table is proved (`Proofs/Step/`); a power too large to form
(`powTooBig`: an exact power past 2^30 bits) is a stop at an implementation limit. The code table the engine runs
(`Engine.P'`, tables of thunks) is the specification's program (`Engine.P'_eq : Engine.P' = Spec.program hostAlgs`).

The set-ups covered: `ecma-run` by default and with `--no-accel` (`Engine.Cli.dispatchOf` builds `Engine.setupAt`),
whatever `--checked`, `--reading`, `--erratum`, `--literal`, `--max-heap`, the host's options (`--host-seed`,
`--web-browser`, `--annex-b`, `--can-block`, `--resize-in-place`), the trace, `--sites` and `--cover` (the loop's
observers are the identity to the logic). Outside the claim: the debugger's loop
(`Debugger.Machine.runW`, `partial`).

Also proved: Parent's laws (`parentLaws`) and the Parse Nodes' laws (`nodeLaws`): a parse's result and a covered
node the model gives are checked against their productions' occurrences.

Axioms of `Engine.implements` and of `Engine.run_sound`: `propext`, `Classical.choice`, `Quot.sound` and 0
`native_decide` pins.

Owed, and part of no claim here: the parser's laws. `Model.ParseLaws Impl` (a Parse Node `parse` gives is a parse
of the text under the grammar, and where it gives none there is none) and, with it, `Model.CoverLaws Impl` (the
node `cover` gives from a Parse Node of parser invocations in a context is a parse of that node's source text with
the goal, in that context: `Ecma/Model/NodeRel.lean`). Neither is proved.

Trusted:

- The driver between runs (`Engine.Host.setup`, `Engine.Host.program`, `Engine.Cli.afterPreludes`, the snapshots
  and `--serve`'s caches), which starts each run of the loop. `setup` allocates the host's cells in the heap and
  sets the agent record (`init`), raises the symbol counter (`realmBy`) and runs InitializeHostDefinedRealm, then
  empties the execution context stack (`takeRealm`) and writes the realm cell (`setRealm`). `program` writes the
  realm cell (the source, its kind, the job policy), runs the agent's jobs, reads the result from the cell and
  writes the cell back. Each prelude is a `program` from the state the last one ended in; a run that ends otherwise
  than with a value ends the driver, and so does an abrupt completion. A snapshot or a cache restores a state a run
  ended in. None of these writes `State.frames`: each run starts from a configuration `Ecma.Reached` covers
  (`first` from the empty state's cells, `next` after a run that ended with a value). That is read, not proved.
- The `implemented_by` overrides: the run loop's observers (`traceOut`, `noteOut`, `noteStep`: the identity to
  the logic), the model's (the binary64 operations `addHw`, `mulHw`, `divHw`, and Parent's `treeIndex`,
  `treeHeight`, `parentFast`).
- Lean's kernel and compiler.
-/

namespace Engine

open Ecma Ecma.Machine Engine.SpecHost

/-- The engine as an implementation of the specification: the host's algorithms (`hostAlgs`), the host under the
options `o` over the cells `cells`, and the engine's transition (`Engine.Machine.stepE`) at its set-up
(`setupAt`): the store's ceiling `mc` (in cells), the accelerator table's shortcuts, or with `accel` false
(`--no-accel`) none. -/
def implementation (o : Engine.Host.HostOpts) (cells : Engine.Host.Cells) (mc : Option Nat) (accel : Bool := true) :
    Ecma.Implementation Impl where
  extras := hostAlgs
  host := hostBy o cells
  step rd chk := Engine.Machine.stepE (setupAt (hostBy o cells) mc accel rd chk)

end Engine

namespace Engine.Claims

open Ecma Ecma.Machine

/-- Parent's laws, proved. -/
theorem parentLaws : Model.ParentLaws Impl := Engine.Impl.parentLaws

/-- The Parse Node accessors' laws, proved, over the specification's GL under the engine's readings
(`Engine.Impl.grammarCtx`), whatever the parse's context: a Parse Node `parse` gives, and a covered node `cover`
gives, has passed the check that every node's children are its production's occurrences (`Engine.shapeOk`). -/
theorem nodeLaws (cx : Grammar.Ctx) (P : Grammar.CodePrims) (strict : Bool) :
    Model.NodeLaws Impl (Engine.Impl.grammarCtx cx P strict) := Engine.Impl.nodeLaws cx P strict

end Engine.Claims
