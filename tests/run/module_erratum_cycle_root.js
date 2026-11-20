// module: yes
// args: --module-dir tests/run/modules
// expect: stop: erratum GatherAvailableAncestorsEmptyCycleRoot sec-gather-available-ancestors#0 1.a
// A module whose synchronous evaluation threw has no [[CycleRoot]] (Evaluate
// step 9.a). When its async dependency b finishes, GatherAvailableAncestors
// step 1.a reads a.[[CycleRoot]].[[EvaluationError]], a field of ~empty~: the
// pinned text has no result there (docs/spec-issues/02). No test262 test
// builds this graph, so the defect is kept literal (Erratum
// GatherAvailableAncestorsEmptyCycleRoot) and the run stops, naming it
// (`stop: erratum <Name> <site>`, exit 3: Engine/Cli/Run.lean). The proposed
// reading skips an ancestor whose [[EvaluationError]] is set: b runs to its
// end and c's error is the outcome (`--erratum
// GatherAvailableAncestorsEmptyCycleRoot=proposed`: `throw: Error: c`, then b).
import "./f22_a.mjs";
