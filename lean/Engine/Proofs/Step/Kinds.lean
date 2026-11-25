module

public import Engine.Machine
public import Ecma.Machine.Run

@[expose] public section

/-!
# The step claim, by kind of shortcut

`Sim X c o`: the outcome `o` of a transition of the engine from `c` is the specification's: some transitions of
its machine, or an end its run reaches, or an implementation limit. `Sound E R`: what each kind of shortcut of
the set-up `E` owes at the configurations `R`, one field for each place `stepA` consults a shortcut.
`stepA_sim`: with them, every transition of the engine from a configuration of `R` is the specification's.
-/

namespace Engine.Machine

open Ecma Ecma.Machine

/-- The outcome `o` from `c` is the specification's: its machine's transitions to there, or its run's end, or an
implementation limit. -/
def Sim (X : Ctx F) (c : Cfg F) : Out F → Prop
  | .inl c' => Steps X c c'
  | .inr f => f = .stop .implLimit ∨ Runs X c f

/-- The machine's own transition is the specification's. -/
theorem Sim.step (X : Ctx F) (c : Cfg F) : Sim X c (step X c) := by
  unfold Sim
  split
  · rename_i c' h
    exact .step h (.refl _)
  · rename_i f h
    exact .inr ⟨c, .refl _, h⟩

/-- The stop at a power or Data Block too large is allowed. -/
theorem Sim.limit {X : Ctx F} {c : Cfg F} (b : Bool) {o : Out F} (h : Sim X c o) :
    Sim X c (if b = true then .inr (.stop .implLimit) else o) := by
  cases b
  · exact h
  · exact .inl rfl

/-- Replacing a stop outcome with `.implLimit` on a limit check is allowed. -/
theorem Sim.catchLimit {X : Ctx F} {c : Cfg F} (b : Unit → Bool) {o : Out F} (h : Sim X c o) :
    Sim X c (orParseLimit b o) := by
  cases o with
  | inl _ => exact h
  | inr f =>
    cases f <;> first | exact h | (dsimp only [orParseLimit]; split <;> first | exact .inl rfl | exact h)

/-- What the shortcuts of `E` owe at the configurations `R`. -/
structure Sound (E : Setup) (R : Cfg F → Prop) : Prop where
  /-- an algorithm's shortcut: its value, or the machine's transition from the state it left -/
  alg : ∀ c a vs r, R c → c.ctl = .invoke (.alg a vs) → E.A.alg a vs = some r →
    Sim E.X c (bindR c r fun o c => match o with
      | some v => c.to (.val v)
      | none => step E.X c)
  /-- an SDO's shortcut -/
  sdo : ∀ c s nd vs r, R c → c.ctl = .invoke (.sdo s nd vs) → s ≠ Known.sdoEarlyErrors → E.A.sdo s nd vs = some r →
    Sim E.X c (leafV c r)
  /-- a primitive's shortcut -/
  prim : ∀ c q xs r, R c → c.ctl = .invoke (.prim q xs) → E.A.prim q xs = some r → Sim E.X c (leafV c r)
  /-- a loop's shortcut: the rounds skipped, at the next round's test -/
  loop : ∀ c back l t run, R c → c.ctl = .loop (.spend back) l → l.it = .while_ t →
    E.A.loop l.p t l.body none c.top.slots c.s = some run →
    Sim E.X c (bindR c run fun (g, ws) c =>
      loopTest (c.mapTop fun f => { f with slots := writeSlots ws f.slots }) { l with r := l.r + g + 1 } t)

/-- With its shortcuts sound at `R`, a transition of the engine from a configuration of `R` is the
specification's. -/
theorem stepA_sim (E : Setup) (R : Cfg F → Prop) (h : Sound E R) (c : Cfg F) (hc : R c) :
    Sim E.X c (stepA E c) := by
  unfold stepA
  refine Sim.limit _ ?_
  split
  · rename_i a vs heq
    dsimp only
    split
    · exact h.alg c a vs _ hc heq ‹_›
    · exact Sim.step _ _
  · rename_i s nd vs heq
    split
    · exact Sim.step _ _
    · rename_i hs
      split
      · exact Sim.step _ _
      · rename_i r hr
        exact h.sdo c s nd vs r hc heq (by simpa using hs) hr
  · split
    · exact h.prim c _ _ _ hc (by assumption) ‹_›
    · split
      · exact Sim.catchLimit _ (Sim.step _ _)
      · exact Sim.step _ _
  · rename_i back l heq
    split
    · rename_i t hit
      split
      · exact h.loop c back l t _ hc heq hit ‹_›
      · exact Sim.step _ _
    · exact Sim.step _ _
  · exact Sim.step _ _

end Engine.Machine
