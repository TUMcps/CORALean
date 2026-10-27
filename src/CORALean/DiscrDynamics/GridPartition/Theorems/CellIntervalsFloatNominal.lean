module

public import CORALean.DiscrDynamics.GridPartition.Operations.CellIntervalsFloat

@[expose] public section

/-!
# `GridPartition.cellIntervals` is the exact layer's

The boxes copy the stored dividers, whose reading as reals is the nominal partition's, and the
range test is on the natural-number cell count, so the float boxes read back as the exact layer's
boxes, cell for cell.

## Inputs
* `P` – grid partition
* `cs` – cell numbers

## Hypotheses
* none

## Conclusion
* the nominal boxes are the exact layer's boxes
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

theorem GridPartition.cellIntervals_nominal (P : GridPartition 𝕋 n) (cs : List ℕ) :
    (P.cellIntervals cs).map Interval.nominal = P.nominal.cellIntervals cs := by
  unfold GridPartition.cellIntervals CORALean.GridPartition.cellIntervals
  rw [List.map_map]
  rfl

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
