module

public import Engine.Host.Spec
public import Engine.Host.Opts

@[expose] public section

/-!
# The host's test options, over Ecma.Gen

`hostBy o c` is `host c` with ecma-run's test-host options (`Engine.Host.hostBy` at Ecma.Gen's
names): a seed (`--host-seed N`) answers the choices the host laws leave open by a pseudo-random
word, and `resizeInPlace` (`--resize-in-place`) makes HostResizeArrayBuffer resize the Data Block in
place, and `annexB` (`--annex-b SEC`) makes the host otherwise support those Annex B clauses.
`hostIn σ o c` takes the open decisions from the inputs `σ`.
-/

namespace Engine.SpecHost

open Ecma Engine

export Engine.Host (HostOpts mix draw randomKey jobKey timeAt unitB seededChoice seededRandom
  resized resizeClause randomClause browserBy choiceBy   )

/-! The test host's definitions at Ecma.Gen's names. -/

abbrev hostBy := Engine.Host.hostBy names

end Engine.SpecHost
