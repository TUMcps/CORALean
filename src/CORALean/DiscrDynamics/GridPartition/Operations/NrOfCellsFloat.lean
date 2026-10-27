module

public import CORALean.DiscrDynamics.GridPartition.Definitions.GridPartitionFloat

@[expose] public section

/-!
# `GridPartition.nrOfCells`, over a floating-point scalar

CORA's `@partition/nrOfCells`, `prod(nrOfSegments)`: the number of subscript vectors. The segment
counts are natural numbers, so nothing is rounded and the count is the exact layer's.

## Inputs
* `P` – grid partition

## Output
* number of cells
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

/-- The product of the segment counts. -/
def GridPartition.nrOfCells (P : GridPartition 𝕋 n) : ℕ := ∏ j, P.nrOfSegments j

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
