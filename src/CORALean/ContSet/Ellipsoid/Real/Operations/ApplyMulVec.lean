import CORALean.ContSet.Ellipsoid.Real.Operations.ApplyEqDotProduct
import CORALean.ContSet.Ellipsoid.Real.Operations.Pullback

/-!
# A functional applied to a generator-space image is the dot product with its pullback
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   05-September-2026
-- Last revision: ---

namespace CORALean.Real

open Matrix

variable {n : ℕ}

theorem Ellipsoid.apply_mulVec (E : Ellipsoid n) (c : Vec ℝ n →ₗ[ℝ] ℝ) (u : Vec ℝ E.k) :
    c (E.G *ᵥ u) = E.pullback c ⬝ᵥ u := by
  rw [apply_eq_dotProduct, dotProduct_mulVec, Ellipsoid.pullback, mulVec_transpose]

end CORALean.Real
