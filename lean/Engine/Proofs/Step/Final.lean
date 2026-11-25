module

public import Engine.Claims
public import Engine.Proofs.Step.Rows
public import Engine.Proofs.Step.ProgEq
public import Engine.Proofs.Step.Plain

@[expose] public section

/-!
# The step claim, assembled

The engine's transition is the specification's (`stepE_sim`), from the rows' theorems (`Rows.lean`, `Rows/`).
The engine has no shortcut at a cover's reparse (§5.1.5): the covered node is the model's (`Model.cover`), which the
specification's own reparse asks.

Here: which rows of the table answer at each kind of key (`fastTable_alg`, `fastTable_sdo`, `fastTable_loop`; the
primitives' is `fastTable_prim`); `Sound` at the engine's set-up from them (`ctx_sound`); the engine's transition
at the configurations the specification's machine reaches (`stepE_sim`).
-/

namespace Engine.Machine

open Ecma Ecma.Machine Engine.Accel Engine.Accel.Rows Engine.Accel.Table

/-! ## The table's rows, by kind -/

/-- Every row of the engine's table meets its obligation at algorithms, at the
engine's host: the exact rows; the other rows are no algorithm's. -/
theorem fastTable_alg [PinsHold] (o : Engine.Host.HostOpts) (cells : Engine.Host.Cells)
    (chk : Bool) :
    ∀ row ∈ fastTable (facts Engine.P'.P),
      RowAlgOk (Ctx.spec Engine.P' (Engine.SpecHost.hostBy o cells) chk) row := by
  intro row hrow
  simp only [fastTable, List.mem_append] at hrow
  rcases hrow with ((hrow | hrow) | hrow) | hrow
  · exact exactRows_ok _ chk row hrow
  · simp only [sdoRows, List.mem_cons, List.not_mem_nil, or_false] at hrow
    rcases hrow with rfl | rfl <;> trivial
  · simp only [primRows, List.map, List.mem_cons, List.not_mem_nil, or_false] at hrow
    rcases hrow with rfl | rfl | rfl | rfl <;> trivial
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hrow
    subst hrow
    trivial

theorem sdo_at {k s : SdoId} {α : Type} {x : Option α} {y : α} (h : (if k = s then x else none) = some y) :
    k = s ∧ x = some y := by
  split at h
  · exact ⟨‹_›, h⟩
  · cases h

/-- The table's rows at an SDO are Contains' and ComputedPropertyContains'. -/
theorem fastTable_sdo {Fc : Facts} {s : SdoId} {nd : F.Node}
    {vs : List (Val F)} {x : Run F (Val F)} (h : (fastTable Fc).sdo s nd vs = some x) :
    (s = Contains.sdoC ∧ Contains.accelSdo Fc.tab Contains.sdoC nd vs = some x) ∨
    (s = Contains.sdoCPC ∧ Contains.accelSdo Fc.tab Contains.sdoCPC nd vs = some x) := by
  simp only [Table.sdo, fastTable, exactRows, sdoRows, primRows, loopRow, algRow,
    List.findSome?_cons, List.findSome?_nil, List.map, Row.sdo, List.cons_append, List.nil_append] at h
  split at h
  · cases h
    obtain ⟨h1, h2⟩ := sdo_at ‹_›
    exact .inl ⟨h1.symm, h2⟩
  · split at h
    · cases h
      obtain ⟨h1, h2⟩ := sdo_at ‹_›
      exact .inr ⟨h1.symm, h2⟩
    · cases h

/-- The table's row at a loop is the sparse HasProperty loops'. -/
theorem fastTable_loop {Fc : Facts} {p : List Nat} {t : Op}
    {body : Code} {l : Option Nat} {sl : Array (Val F)} {s : State F} {x : Run F (Nat × List (Slot × Val F))}
    (h : (fastTable Fc).loop p t body l sl s = some x) :
    loopRow.loop p t body l sl s = some x := by
  simp only [Table.loop, fastTable, exactRows, sdoRows, primRows, algRow,
    List.findSome?_cons, List.findSome?_nil, List.map, Row.loop,
    List.append_nil, List.cons_append, List.nil_append] at h
  split at h
  · cases h
    assumption
  · cases h

/-! ## `Sound` at the engine's set-up -/

/-- The shortcuts of the engine's set-up are sound: each field of `Sound` from its rows' theorems. -/
theorem ctx_sound [PinsHold] (o : Engine.Host.HostOpts) (cells : Engine.Host.Cells)
    (chk : Bool) :
    Sound (ctx Engine.P' (Engine.SpecHost.hostBy o cells) chk) (fun _ => True) where
  alg := fun c a vs r _ hctl h =>
    alg_of_rows (fastTable_alg o cells chk) c a vs r hctl h
  sdo := fun c s nd vs r _ hctl _ h => by
    rcases fastTable_sdo (Fc := facts Engine.P'.P) h with ⟨rfl, h'⟩ | ⟨rfl, h'⟩
    · exact (contains_sdoRows _ chk).1 c nd vs r hctl h'
    · exact (contains_sdoRows _ chk).2 c nd vs r hctl h'
  prim := fun c q xs r _ hctl h => ctx_prim Engine.P' _ chk c q xs r hctl h
  loop := fun c back l t run _ hctl hit h =>
    loopSkip_row _ chk lsIntKeys c back l t run hctl hit (fastTable_loop (Fc := facts Engine.P'.P) h)

/-- Shortcuts sound at `R` are so whatever the store's ceiling. -/
theorem Sound.ceil {E : Setup} {R : Cfg F → Prop} (h : Sound E R) (mc : Option Nat) :
    Sound { E with maxCells := mc } R :=
  ⟨h.1, h.2, h.3, h.4⟩

/-! ## The engine's transition -/

open Engine.SpecHost in
/-- The engine's transition (`stepE`) at its set-up (`Engine.setupAt`), under every option set of its host, store
ceiling, and mode, with or without the accelerator table, from every configuration the specification's
machine reaches, is the specification's: some transitions of its machine, or where it ends, that machine's run's
end, or an implementation limit (the store's ceiling, a power too large to compute). -/
theorem stepE_sim (o : Engine.Host.HostOpts) (cells : Engine.Host.Cells) (mc : Option Nat) (accel : Bool)
    (chk : Bool) (c : Cfg F) (_hc : Reached (Ctx.spec Engine.P' (hostBy o cells) chk) c) :
    Sim (Ctx.spec Engine.P' (hostBy o cells) chk) c (stepE (Engine.setupAt (hostBy o cells) mc accel chk) c) := by
  unfold stepE
  refine Sim.limit _ ?_
  cases hok : accel && pinsOkThunk.get
  · rw [show Engine.setupAt (hostBy o cells) mc accel chk =
        plain { ctx Engine.P' (hostBy o cells) chk with maxCells := mc } by simp [Engine.setupAt, hok]]
    rcases stepA_plain { ctx Engine.P' (hostBy o cells) chk with maxCells := mc } c with h | h <;> rw [h]
    · exact Sim.step _ _
    · exact .inl rfl
  · rw [show Engine.setupAt (hostBy o cells) mc accel chk =
        { ctx Engine.P' (hostBy o cells) chk with maxCells := mc } by simp [Engine.setupAt, hok]]
    simp only [Bool.and_eq_true] at hok
    obtain ⟨_, hp⟩ := hok
    haveI : PinsHold := pinsHold_of_ok hp
    exact stepA_sim _ _ ((ctx_sound o cells chk).ceil mc) c trivial

end Engine.Machine
