module

public import Ecma.Machine.Run
public import Ecma.Lower.Expand
public import Ecma.Lower.Lin
public import Ecma.Spec.Program
public import Ecma.Host.Laws
public import Ecma.Model.Laws

@[expose] public section

/-!
# What it is to implement the specification

An implementation has values (a `Model`), a host (a `Host`), algorithms of its own beside the specification's, and
its own transition between the machine's configurations. It implements the specification (`Implements`) when its
values obey the model's laws, its host obeys the host's laws, and each transition it takes from a configuration
the specification's machine reaches is some transitions of that machine. Its every run is then a run of the
specification's machine.

Both machines run under whether Asserts are checked.
-/

namespace Ecma
open Machine

variable {M : Model}

/-- The specification's program, with an implementation's own algorithms `extras` where the specification defines
none (sec-conformance: an implementation "may provide additional types, values, objects, properties, and
functions beyond those described in this specification"). -/
def Spec.program (extras : AlgId → Option Alg) : Prog' := Prog'.of (Spec.src.expanded extras)

/-- An implementation over the model `M`: its own algorithms, its host, and its transition under
whether Asserts are checked. A transition may take many of the specification's steps at once, or
compute one differently. -/
structure Implementation (M : Model) where
  extras : AlgId → Option Alg
  host : Host M
  step : Bool → Cfg M → Out M

/-- The specification's machine for `I`: the specification's program with `I`'s algorithms, and `I`'s host. -/
def Implementation.spec (I : Implementation M) (chk : Bool) : Ctx M :=
  Ctx.spec (Spec.program I.extras) I.host chk

/-- The configurations the machine `X` reaches: from a call in a state with no suspended execution context, by its
transitions, and by a further call from the state a run ended in, whatever else of that state the host changed
meanwhile (its suspended execution contexts it may not). -/
inductive Reached (X : Ctx M) : Cfg M → Prop where
  | first (s : State M) (k : Call M) : s.frames = [] → Reached X (start s k)
  | step {c c' : Cfg M} : Reached X c → Step X c c' → Reached X c'
  | next {c : Cfg M} {v : Val M} {s s' : State M} (k : Call M) :
      Reached X c → Ends X c (.ok v s) → s'.frames = s.frames → Reached X (start s' k)

/-- A run of `I` from `c` that ends with `f`. -/
inductive Implementation.Runs (I : Implementation M) (chk : Bool) :
    Cfg M → Final M → Prop where
  | ends {c : Cfg M} {f : Final M} : I.step chk c = .inr f → I.Runs chk c f
  | step {c c' : Cfg M} {f : Final M} : I.step chk c = .inl c' → I.Runs chk c' f → I.Runs chk c f

/-- `I` implements the specification. -/
structure Implements (I : Implementation M) : Prop where
  /-- its values are the specification's: the model's laws -/
  model : Model.Laws M ∧ Model.UnicodeLaws M ∧ Model.ParentLaws M
  /-- its host meets every requirement the specification makes of a host -/
  host : Host.WF I.host
  /-- each transition it takes from a configuration the specification's machine reaches is some transitions of
  that machine, and where it ends, that machine's run ends so; or it gives up at a limit of its own (it never
  answers otherwise than the specification) -/
  step : ∀ chk c, Reached (I.spec chk) c →
    match I.step chk c with
    | .inl c' => Steps (I.spec chk) c c'
    | .inr f => Runs (I.spec chk) c f ∨ f = .stop .implLimit

end Ecma
