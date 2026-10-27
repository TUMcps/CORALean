module

public import CORALean.DiscrDynamics.GridPartition.Definitions.GridPartitionFloat

@[expose] public section

/-!
# `GridPartition.cellIndices`, over a floating-point scalar

CORA's `@partition/cellIndices`: the cell number of each subscript vector, `0` if one is out of
range. The numbers depend on the segment counts only, so they are the exact layer's.

## Inputs
* `P` – grid partition
* `subscriptVectors` – subscripts of the cells

## Output
* cell number of each subscript vector
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

/-- `s2i` of each subscript vector. -/
def GridPartition.cellIndices (P : GridPartition 𝕋 n) (subscriptVectors : List (Fin n → ℕ)) :
    List ℕ :=
  subscriptVectors.map (CORALean.GridPartition.s2i P.nrOfSegments)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
