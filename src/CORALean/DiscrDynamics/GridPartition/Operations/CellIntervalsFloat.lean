module

public import CORALean.DiscrDynamics.GridPartition.Definitions.GridPartitionFloat
public import CORALean.DiscrDynamics.GridPartition.Operations.NrOfCellsFloat
public import CORALean.DiscrDynamics.GridPartition.Operations.CellIntervalFloat
public import CORALean.ContSet.Interval.Float.Interval

@[expose] public section

/-!
# `GridPartition.cellIntervals`, over a floating-point scalar

CORA's `@partition/cellIntervals`: the box of each cell given, all by default, cells out of range
dropped. The box of a cell runs from divider `sub - 1` to divider `sub` in each dimension, so the
stored dividers are copied and nothing is rounded.

## Inputs
* `P` – grid partition
* `cellNrs` – cell numbers

## Output
* boxes of the cells in range
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

/-- The boxes of the cells given that are in range, all cells by default. -/
def GridPartition.cellIntervals (P : GridPartition 𝕋 n)
    (cellNrs : List ℕ := List.range' 1 P.nrOfCells) : List (Interval (Vec 𝕋 n)) :=
  (cellNrs.filter fun c => 0 < c ∧ c ≤ P.nrOfCells).map P.cellInterval

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
