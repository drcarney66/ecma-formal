module

public import Ecma.Machine.Step

@[expose] public section

/-!
# Runs

What it is for the specification's algorithms to run, over any model and host: a relation between
configurations, with no bound. `Step` is one transition of the machine (`step`), `Steps` any number of them, and
`Runs` a run that ends. `Calls` is a call's run from a state to its result. The specification's own context
(`Ctx.spec`) has the program's code, the host and the readings, and nothing else.

What it is for an implementation to be the specification's is stated over these (`Ecma.Implements`).
-/

namespace Ecma.Machine
open Ecma

variable {M : Model}

/-- The specification's context: the program's code, the host, and whether Asserts are checked. -/
def Ctx.spec (prog : Prog') (H : Host M) (chk : Bool) : Ctx M :=
  { prog, H, chk }

/-- One transition. -/
def Step (X : Ctx M) (c c' : Cfg M) : Prop := step X c = .inl c'

/-- The machine ends at `c`, with `f`. -/
def Ends (X : Ctx M) (c : Cfg M) (f : Final M) : Prop := step X c = .inr f

/-- Any number of transitions. -/
inductive Steps (X : Ctx M) : Cfg M → Cfg M → Prop where
  | refl (c : Cfg M) : Steps X c c
  | step {c c' c'' : Cfg M} : Step X c c' → Steps X c' c'' → Steps X c c''

/-- A run from `c` that ends with `f`. -/
def Runs (X : Ctx M) (c : Cfg M) (f : Final M) : Prop := ∃ c', Steps X c c' ∧ Ends X c' f

/-- The call `k` from the state `s` gives `v`, leaving the state `t`. -/
def Calls (X : Ctx M) (k : Call M) (s : State M) (v : Val M) (t : State M) : Prop := Runs X (start s k) (.ok v t)

end Ecma.Machine
