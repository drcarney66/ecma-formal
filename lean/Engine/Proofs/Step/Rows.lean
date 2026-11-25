module

public import Engine.Proofs.Step.Table
public import Engine.Proofs.Step.Rows.IsWrite
public import Engine.Proofs.Step.Rows.CodePoints
public import Engine.Proofs.Step.Rows.Stcp
public import Engine.Proofs.Step.Rows.Gsi
public import Engine.Proofs.Step.Rows.Contains
public import Engine.Proofs.Step.Rows.LoopSkip
public import Engine.Proofs.Step.Rows.LoopSkip.IntKeys

@[expose] public section

/-!
# The rows

`exactRows_ok`: each row of `Engine.Accel.Table.exactRows` meets its obligation (`RowAlgOk`), from the rows proved
(`Rows/`). `contains_sdoRows`: Contains' and ComputedPropertyContains' rows, the
rows' table checked at runtime (`containsRows_true` under `PinsHold`).
-/

namespace Engine.Machine

open Ecma Ecma.Machine Engine.Accel Engine.Accel.Table

/-- The exact algorithms' rows. -/
theorem exactRows_ok [PinsHold] (H : Host F) (chk : Bool) :
    ∀ row ∈ exactRows, RowAlgOk (Ctx.spec Engine.P' H chk) row := by
  intro row hrow
  simp only [exactRows, List.mem_cons, List.not_mem_nil, or_false] at hrow
  rcases hrow with rfl | rfl | rfl
  · exact isWrite_algRow H chk
  · exact stcp_algRow H chk
  · exact gsi_algRow H chk

/-- Contains' and ComputedPropertyContains' rows. -/
theorem contains_sdoRows [PinsHold] (H : Host F) (chk : Bool) :
    SdoRowOk (Ctx.spec Engine.P' H chk) 23 (Contains.accelSdo (Engine.Machine.facts Engine.P'.P).tab 23) ∧
    SdoRowOk (Ctx.spec Engine.P' H chk) 24 (Contains.accelSdo (Engine.Machine.facts Engine.P'.P).tab 24) :=
  contains_sdoRow H chk containsRows_true

end Engine.Machine
