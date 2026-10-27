module

public import CORALean.DiscrDynamics.GridPartition.Definitions.GridPartitionFloat

@[expose] public section

/-!
# `GridPartition.cellSegments`, over a floating-point scalar

CORA's `@partition/cellSegments`: the subscripts of each cell number by MATLAB's `ind2sub`, the
first dimension fastest. The subscripts depend on the segment counts only, so they are the exact
layer's.

## Inputs
* `P` – grid partition
* `indexVector` – cell numbers

## Output
* subscripts of each cell number
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

/-- `i2s` of each cell number. -/
def GridPartition.cellSegments (P : GridPartition 𝕋 n) (indexVector : List ℕ) :
    List (Fin n → ℕ) :=
  indexVector.map (CORALean.GridPartition.i2s P.nrOfSegments)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
