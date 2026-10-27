module

public import CORALean.DiscrDynamics.GridPartition.Operations.CellSegmentsFloat

@[expose] public section

/-!
# `GridPartition.cellSegments` is the exact layer's

The subscripts of a cell number are computed from the segment counts, which the float partition
stores as natural numbers, so they are the nominal partition's.

## Inputs
* `P` – grid partition
* `indexVector` – cell numbers

## Hypotheses
* none

## Conclusion
* the subscripts equal the nominal partition's
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

theorem GridPartition.cellSegments_nominal (P : GridPartition 𝕋 n) (indexVector : List ℕ) :
    P.cellSegments indexVector = P.nominal.cellSegments indexVector := rfl

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
