module

public import CORALean.ContSet.Ellipsoid.Real.Operations.ApplyEqDotProduct
public import CORALean.ContSet.Ellipsoid.Real.Operations.Pullback

@[expose] public section

/-!
# A functional applied to a generator-space image is the dot product with its pullback
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   05-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Ellipsoid.apply_mulVec (E : Ellipsoid n) (c : Vec ℝ n →ₗ[ℝ] ℝ) (u : Vec ℝ E.k) :
    c (E.G *ᵥ u) = E.pullback c ⬝ᵥ u := by
  rw [apply_eq_dotProduct, dotProduct_mulVec, Ellipsoid.pullback, mulVec_transpose]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
