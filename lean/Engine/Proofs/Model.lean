module

public import Engine.Claims
public import Engine.Proofs.Step.Final
public import Engine.Proofs.Run

@[expose] public section

/-!
# The engine implements the specification

`Engine.implements` from the model's laws (`Engine.Impl.laws`, `Engine.Impl.unicodeLaws`,
`Engine.Impl.parentLaws`), the host's (`Engine.SpecHost.wfBy`) and the engine's transition at the configurations
the specification's machine reaches (`Engine.Machine.stepE_sim`, over `Engine.P'`, the specification's program:
`Engine.P'_eq`). `Engine.run_sound` from it, the run loop's runs (`Engine.Machine.runT_runs`) and
`Ecma.Implements.run_sound`. No hypothesis.
-/

namespace Engine

open Ecma Ecma.Machine Engine.SpecHost

/-- **The engine implements the specification**, under every option set of its host and its cells, every store
ceiling, with or without the accelerator table. -/
theorem implements (o : Engine.Host.HostOpts) (cells : Engine.Host.Cells) (mc : Option Nat) (accel : Bool) :
    Implements (implementation o cells mc accel) where
  model := ⟨Engine.Impl.laws, Engine.Impl.unicodeLaws, Engine.Impl.parentLaws⟩
  host := wfBy o cells
  step rd chk c hc := by
    have hc' : Reached (Ctx.spec Engine.P' (hostBy o cells) rd chk) c := by
      rw [P'_eq]
      exact hc
    have h := Machine.stepE_sim o cells mc accel rd chk c hc'
    rw [P'_eq] at h
    change Machine.Sim _ c ((implementation o cells mc accel).step rd chk c) at h
    generalize (implementation o cells mc accel).step rd chk c = out at h ⊢
    cases out with
    | inl c' => exact h
    | inr f => exact Or.symm h

/-- **Every run of the engine's loop is the specification's**, from any configuration the specification's machine
reaches: a run the loop (`Engine.Machine.runT`, whatever it keeps) returns at the engine's set-up is a run of the
specification's machine, with the specification's program and the engine's host, that ends with the same result;
or it stopped at an implementation limit. The driver's later runs start from such configurations
(`Reached.next`: from the state an earlier run ended in). -/
theorem run_sound_reached (o : Engine.Host.HostOpts) (cells : Engine.Host.Cells) (mc : Option Nat) (accel : Bool)
    (rd : ErratumId → Reading) (chk : Bool) (units : Thunk Engine.Machine.Units) (ob : Engine.Machine.Obs)
    (c : Cfg Impl) (f : Final Impl) (hc : Reached (Ctx.spec (Spec.program hostAlgs) (hostBy o cells) rd chk) c)
    (h : Machine.runT (setupAt (hostBy o cells) mc accel rd chk) units ob c = some f) :
    Runs (Ctx.spec (Spec.program hostAlgs) (hostBy o cells) rd chk) c f ∨ f = .stop .implLimit :=
  (implements o cells mc accel).run_sound hc
    (Machine.runT_runs (implementation o cells mc accel) rd chk _ (fun _ => rfl) units ob c f h)

/-- **Every run of the engine's loop is the specification's**: a run the loop returns at the engine's set-up, from
a call in a state with no suspended execution context, is a run of the specification's machine that ends with the
same result, or it stopped at an implementation limit. -/
theorem run_sound (o : Engine.Host.HostOpts) (cells : Engine.Host.Cells) (mc : Option Nat) (accel : Bool)
    (rd : ErratumId → Reading) (chk : Bool) (units : Thunk Engine.Machine.Units) (ob : Engine.Machine.Obs)
    (s : State Impl) (k : Call Impl) (f : Final Impl) (hs : s.frames = [])
    (h : Machine.runT (setupAt (hostBy o cells) mc accel rd chk) units ob (start s k) = some f) :
    Runs (Ctx.spec (Spec.program hostAlgs) (hostBy o cells) rd chk) (start s k) f ∨ f = .stop .implLimit :=
  run_sound_reached o cells mc accel rd chk units ob _ f (.first s k hs) h

end Engine
