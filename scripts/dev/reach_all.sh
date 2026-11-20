#!/bin/bash
# The dead-code sweep's analysis, into the directory $1 (outside the repository):
# one run of reach.lean per executable (ecma-print's too: the printer is reached only from it) and one for the proved claims and the stated laws, then reach_combine.py.
# Then, in $1: python3 <repo>/scripts/dev/reach_prune.py [--dry]. The project must be built.
set -e
D=$(cd "$1" && pwd)
R=$(cd "$(dirname "$0")/../.." && pwd)
cd "$R"
L="lean --run $R/scripts/dev/reach.lean"
# The proved claims (Engine/Claims.lean, Proofs/Model.lean), what it is to implement the specification
# (Ecma/Implements.lean), the laws stated and owed, the run relations (Ecma/Machine/Run.lean), and
# the specification's definitions no law reads (valid executions, races and data race freedom, 29.7.5-29.10).
CL="+Engine.implements +Engine.run_sound +Engine.run_sound_reached +Engine.Claims.parentLaws +Engine.Claims.nodeLaws
  +Ecma.Implements +Ecma.Spec.program +Ecma.Model.ParseLaws +Ecma.Model.CoverLaws
  +Ecma.Machine.Ctx.spec +Ecma.Machine.Step +Ecma.Machine.Ends +Ecma.Machine.Steps +Ecma.Machine.Runs
  +Ecma.Machine.Calls
  +Ecma.MemoryModel.Valid +Ecma.MemoryModel.DataRaceFree"
nix develop ~/.local/state/ecma-formal/devshell -c lake env bash -c "cd $D && rm -f *.tsv *.mods &&
  $L run Engine.Cli.Main && $L bundle Engine.Cli.Bundle && $L dbg Debugger.Main && $L print SpecPrint &&
  $L claims Engine.Proofs.Model Ecma.Model.NodeRel Ecma.Model.Laws Ecma.Machine.Run Ecma.MemoryModel $(echo $CL)"
cd "$D" && python3 "$R/scripts/dev/reach_combine.py"
