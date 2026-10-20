module

public import CORALean.ContSet.PolyZonotope.Float.Operations.Compact
public import CORALean.ContSet.PolyZonotope.Float.Theorems.SumMask

@[expose] public section

/-!
# The downward masked sum never overshoots the exact fibre sum

## Inputs
* `r` – map from generators to kept columns
* `G` – generator matrix
* `i` – row index
* `j` – target column

## Hypotheses
* none

## Conclusion
* the rounded-down sum is at most the exact one
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   05-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n h : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

-- so the two directed masked sums bracket the exact fibre from either side
theorem PolyZonotope.fiberDown_le (r : Fin h → Fin h) (G : Mat 𝕋 n h) (i : Fin n)
    (j : Fin h) :
    toReal (PolyZonotope.fiberDown r G i j)
      ≤ Real.PolyZonotope.fiberSum r (fun l => toReal (G i l)) j := by
  rw [← PolyZonotope.sum_mask r G i j]
  exact sumDown_le_sum _

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
