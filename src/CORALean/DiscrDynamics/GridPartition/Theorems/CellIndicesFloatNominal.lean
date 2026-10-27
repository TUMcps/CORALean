module

public import CORALean.DiscrDynamics.GridPartition.Operations.CellIndicesFloat

@[expose] public section

/-!
# `GridPartition.cellIndices` is the exact layer's

The cell number of a subscript vector is computed from the segment counts, which the float
partition stores as natural numbers, so it is the nominal partition's.

## Inputs
* `P` – grid partition
* `subscriptVectors` – subscripts of the cells

## Hypotheses
* none

## Conclusion
* the cell numbers equal the nominal partition's
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       26-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem GridPartition.cellIndices_nominal (P : GridPartition 𝕋 n)
    (subscriptVectors : List (Fin n → ℕ)) :
    P.cellIndices subscriptVectors = P.nominal.cellIndices subscriptVectors := rfl

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
