module

public import CORALean.ContSet.Ellipsoid.Real.Ellipsoid
public import CORALean.ContSet.Ellipsoid.Real.Operations.Basic

@[expose] public section

/-!
# The generator matrix is symmetric

`G = Q^(1/2)` is the nonnegative square root of a positive semi-definite matrix, which is
Hermitian, and over ℝ that is `Gᵀ = G`.

## Inputs
* `E` – ellipsoid

## Hypotheses
* none

## Conclusion
* the generator matrix is symmetric
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

/-- `G = Q^(1/2)` is symmetric. -/
theorem Ellipsoid.G_transpose (E : Ellipsoid n) : E.Gᵀ = E.G := by
  show (CFC.sqrt E.Q)ᵀ = CFC.sqrt E.Q
  have h := (CFC.sqrt_nonneg E.Q).posSemidef.isHermitian.eq
  simpa [conjTranspose_eq_transpose_of_trivial] using h

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
