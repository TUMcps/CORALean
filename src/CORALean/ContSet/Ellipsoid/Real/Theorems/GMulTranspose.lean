module

public import CORALean.ContSet.Ellipsoid.Real.Theorems.GTranspose

@[expose] public section

/-!
# The generator matrix factors the shape matrix

`G Gᵀ = Q`: `G` is symmetric and squares to `Q`, `Q` being positive semi-definite. This is what
every statement in the shape matrix is proved through, by `Theorems/ConstructEqOfFactor`.

## Inputs
* `E` – ellipsoid

## Hypotheses
* none

## Conclusion
* `G Gᵀ = Q`
-/

-- Authors:       Claude Opus 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix
open scoped MatrixOrder

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- `G Gᵀ = Q`. -/
theorem Ellipsoid.G_mul_transpose (E : Ellipsoid n) : E.G * E.Gᵀ = E.Q := by
  rw [E.G_transpose]
  exact CFC.sqrt_mul_sqrt_self E.Q E.psd.nonneg

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
