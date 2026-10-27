module

public import CORALean.DiscrDynamics.GridPartition.Definitions.GridPartitionFloat
public import CORALean.DiscrDynamics.GridPartition.Operations.CellIntervalsFloat
public import CORALean.ContSet.Interval.Float.Operations.CenterBox

@[expose] public section

/-!
# `GridPartition.cellCenter`, over a floating-point scalar

CORA's `@partition/cellCenter`: the midpoint of each cell given, `[]` if one is out of range. A
midpoint is not exact in floats, so each is the box `centerBox` of the cell's box, which holds the
real midpoint: the sum rounded down for the lower end and up for the upper, `half` being exact.

## Inputs
* `P` – grid partition
* `cellNrs` – cell numbers

## Output
* box holding the midpoint of each cell
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       26-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The brackets of the midpoints, or none if a cell is out of range. -/
def GridPartition.cellCenter (P : GridPartition 𝕋 n) (cellNrs : List ℕ) :
    List (Interval (Vec 𝕋 n)) :=
  if ∀ c ∈ cellNrs, 0 < c ∧ c ≤ P.nrOfCells then
    cellNrs.map fun c => (P.cellInterval c).centerBox
  else []

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
