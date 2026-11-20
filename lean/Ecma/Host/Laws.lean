module

public import Ecma.Host.Laws.Jobs
public import Ecma.Host.Laws.Time
public import Ecma.Host.Laws.Memory
public import Ecma.Host.Laws.RegExp
public import Ecma.Host.Laws.Order
public import Ecma.Host.Laws.Locale
public import Ecma.Host.Laws.Optional
public import Ecma.Host.Laws.Values
public import Ecma.Host.Laws.Hooks
public import Ecma.Host.Laws.Changes

@[expose] public section

/-!
# The laws of a host

What the specification requires of the host, stated over a `Host` and never assumed: a law constrains what one
call of the host gives, given the state and the host-call log (`State.hostLog`) before it. The machine owns the
log: a host reads it, and a host step adds only its own entry. Each law is a field of the structure of its topic
(`Ecma/Host/Laws/`), and its docstring says the clause of the specification it reads, quotes the sentence that
governs it, and gives its reading (`scripts/law_quotes.py` checks the quotations against `spec.html`).
-/

namespace Ecma

/-- The laws of a host: those of every topic. -/
structure Host.WF {M : Model} (H : Host M) : Prop extends
    H.JobLaws, H.TimeLaws, H.MemoryLaws, H.RegExpLaws, H.OrderLaws, H.LocaleLaws, H.OptionalLaws, H.ValueLaws,
    H.HookLaws, H.ChangeLaws

end Ecma
