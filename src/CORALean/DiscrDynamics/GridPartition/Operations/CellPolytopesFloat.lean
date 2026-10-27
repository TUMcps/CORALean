module

public import CORALean.DiscrDynamics.GridPartition.Definitions.GridPartitionFloat
public import CORALean.DiscrDynamics.GridPartition.Operations.CellIntervalsFloat
public import CORALean.ContSet.Conversion.Float.Operations.Interval_to_HPolytope

@[expose] public section

/-!
# `GridPartition.cellPolytopes`, over a floating-point scalar

CORA's `@partition/cellPolytopes`: each cell box as a polytope by halfspaces. The float version
converts each float box of `cellIntervals` with `Interval.hPolytope`.

## Inputs
* `P` – grid partition
* `cellNrs` – cell numbers

## Output
* halfspace polytope of each cell in range
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

/-- Each cell box as a polytope by halfspaces. -/
def GridPartition.cellPolytopes (P : GridPartition 𝕋 n)
    (cellNrs : List ℕ := List.range' 1 P.nrOfCells) : List (HPolytope 𝕋 (Vec 𝕋 n)) :=
  (P.cellIntervals cellNrs).map Interval.hPolytope

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
