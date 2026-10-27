module

public import CORALean.DiscrDynamics.GridPartition.Operations.NrOfCellsFloat

@[expose] public section

/-!
# `GridPartition.nrOfCells` is the exact layer's count

The segment counts are stored as natural numbers, so the float count is the nominal grid
partition's.

## Inputs
* `P` – grid partition

## Hypotheses
* none

## Conclusion
* the count equals the nominal partition's count
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

theorem GridPartition.nrOfCells_nominal (P : GridPartition 𝕋 n) :
    P.nrOfCells = P.nominal.nrOfCells := rfl

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
