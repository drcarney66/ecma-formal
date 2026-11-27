module

public import Engine.Accel.Rows
public import Engine.Accel.Algs
public import Engine.Accel.Contains
public import Engine.Accel.StringScan
public import Engine.Accel.ToNumber
public import Engine.Accel.ListUpdate

@[expose] public section

/-!
# The Bare accelerators as one table

`fastTable Fc rd`: every proved accelerator of the engine as a row keyed by spec id (`Engine.Accel.Rows.Key`),
over what the rows read of the program (`Facts`): the exact algorithms (`exactRows`), Contains and
ComputedPropertyContains, the List updates in place, 2.l's reading by its id, and the sparse HasProperty loops.
-/

namespace Engine.Accel.Table
open Ecma Engine.Accel.Rows Engine.Accel

abbrev F := Engine.Impl

/-- What the rows read of the program: the Contains tables. -/
structure Facts where
  tab : Engine.Accel.Contains.Tab

/-- The algorithms' ids of `exactRows`. -/
def writeId : AlgId := ⟨Known.cSortWriteSharedMemoryEvent, 0⟩
def stcpId : AlgId := ⟨Known.cStringToCodePoints, 0⟩
def gsiId : AlgId := ⟨Known.cGetStringIndex, 0⟩
def utf16EncId : AlgId := ⟨Known.cUTF16EncodeCodePoint, 0⟩
def cptsId : AlgId := ⟨Known.cCodePointsToString, 0⟩
def numToStrId : AlgId := ⟨Known.cNumberToString, 0⟩
def toStrId : AlgId := ⟨Known.cToString, 0⟩
def toNumId : AlgId := ⟨Known.cToNumber, 0⟩
def cnisId : AlgId := ⟨Known.cCanonicalNumericIndexString, 0⟩
def roundDecMVId : AlgId := ⟨Known.cFormalRoundDecimalMV, 0⟩

/-- An algorithm's row. -/
def algRow (a : AlgId) (e : Entry) (m : Mode) : Row F := ⟨.alg a, e, m⟩

/-- The exact algorithms' rows. -/
def exactRows : Table F :=
  [algRow writeId isWriteEntry .exact,
    algRow stcpId stcpEntry .exact,
    algRow gsiId gsiEntry .exact,
    algRow utf16EncId utf16EncEntry .exact,
    algRow cptsId cptsEntry .exact,
    algRow numToStrId numToStrEntry .exact,
    algRow toStrId toStrEntry .exact,
    algRow toNumId toNumEntry .exact,
    algRow cnisId cnisEntry .exact,
    algRow roundDecMVId roundDecMVEntry .exact]

/-- The SDOs' rows: Contains, ComputedPropertyContains, and StringNumericValue. -/
def sdoRows (Fc : Facts) : Table F :=
  [⟨.sdo Contains.sdoC, Contains.accelSdo Fc.tab Contains.sdoC, .exact⟩,
    ⟨.sdo Contains.sdoCPC, Contains.accelSdo Fc.tab Contains.sdoCPC, .exact⟩,
    ⟨.sdo Known.sdoStringNumericValue, snvSdo, .exact⟩]

/-- The primitives' rows: the List updates in place. -/
def primRows : Table F :=
  [Known.pAppend, Known.pPrepend, Known.pSetAdd, Known.pReplaceElem].map fun q =>
    ⟨.prim q, ListUpdate.prim q, .exact⟩

/-- The sparse HasProperty loops' row: the rounds skipped at a `hasPropLoop` match. -/
def loopRow : Row F :=
  ⟨.loop, fun p t body l sl s => (hasPropLoop p t body).bind fun m => skipRun m l sl s, .exact⟩

/-- The Bare tiers' accelerators: `exactRows`, `sdoRows`, `primRows` and `loopRow`. -/
def fastTable (Fc : Facts) : Table F :=
  exactRows ++ sdoRows Fc ++ primRows ++ [loopRow]

end Engine.Accel.Table
