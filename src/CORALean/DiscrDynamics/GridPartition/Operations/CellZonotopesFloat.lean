module

public import CORALean.DiscrDynamics.GridPartition.Definitions.GridPartitionFloat
public import CORALean.DiscrDynamics.GridPartition.Operations.CellIntervalsFloat
public import CORALean.ContSet.Conversion.Float.Operations.Interval_to_Zonotope

@[expose] public section

/-!
# `GridPartition.cellZonotopes`, over a floating-point scalar

CORA's `@partition/cellZonotopes`: each cell box as a zonotope. The float version converts each
float box of `cellIntervals` with `Interval.zonotope`, which rounds the center and radius outward.

## Inputs
* `P` – grid partition
* `cellNrs` – cell numbers

## Output
* zonotope of each cell in range
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

/-- Each cell box as a zonotope. -/
def GridPartition.cellZonotopes (P : GridPartition 𝕋 n)
    (cellNrs : List ℕ := List.range' 1 P.nrOfCells) : List (Zonotope (Vec 𝕋 n)) :=
  (P.cellIntervals cellNrs).map Interval.zonotope

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
