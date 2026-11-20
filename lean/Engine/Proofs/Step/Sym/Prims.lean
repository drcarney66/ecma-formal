module

public import Engine.Proofs.Step.Sym.Basic

@[expose] public section

/-!
# Symbolic execution: a primitive's call

`step_prim_plain`: the machine's transition at a call of a plain primitive (`plainPrim`: not the machine's own,
a table's or the host's) that the program does not define is the primitive's run; `step_prim_ok`: where the run
answers, its value in its state. Both hypotheses on the primitive are `rfl` at a literal id. `mprim h`: the
transition, from the run's equation `h : Ecma.prim q xs s = .ok v s'`. Restate the goal with `show` first where
the arguments are not yet in the form `h` is stated at.
-/

namespace Engine.Machine

open Ecma Ecma.Machine

/-- A primitive that is neither the machine's own, nor a table's, nor the host's. -/
def plainPrim (q : PrimId) : Bool :=
  !(q == Known.pMustCoverChild) && !(q == Known.pNewRecord) && !(q == Known.pInstanceOf) &&
    !(q == Known.pEvaluateBuiltin) && !tableQ q && !hostPrim q && !(q == Known.pMakeObject)

/-- The machine's transition at a call of a plain primitive that the program does not define: its run. -/
theorem step_prim_plain (X : Ctx F) (c : Cfg F) (q : PrimId) (xs : List (Val F)) (hc : c.ctl = .invoke (.prim q xs))
    (hq : plainPrim q = true) (hp : progPrim (leafCtx X) X.P X.H q xs = none) :
    step X c = leafV c (Ecma.prim q xs) := by
  simp only [plainPrim, Bool.and_eq_true, Bool.not_eq_true'] at hq
  obtain ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, ht⟩, hh⟩, hm⟩ := hq
  have ha : X.H.allocL q xs = Ecma.prim q xs := by
    funext s
    simp [Host.allocL, hm]
  unfold step
  rw [hc]
  simp only [invoke]
  simp [h1, h2, h3, h4, ht, hh, hp, ha]

/-- The machine's transition at a call of a plain primitive that the program does not define: its run's value. -/
theorem step_prim_ok (X : Ctx F) (s s' : State F) (fr : List (Frame F)) (q : PrimId) (xs : List (Val F)) (v : Val F)
    (hq : plainPrim q = true) (hp : progPrim (leafCtx X) X.P X.H q xs = none)
    (h : Ecma.prim q xs s = .ok v s') :
    step X ⟨s, fr, .invoke (.prim q xs)⟩ = .inl ⟨s', fr, .val v⟩ := by
  rw [step_prim_plain X _ q xs rfl hq hp]
  simp only [leafV, bindR, h]
  rfl

/-- The transition at a plain primitive's call, from its run's equation. -/
macro "mprim" h:term : tactic => `(tactic| refine Steps.next (step_prim_ok _ _ _ _ _ _ _ rfl rfl $h) ?_)

end Engine.Machine
