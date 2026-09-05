import CORALean.ContSet.Ellipsoid.Real.Ellipsoid
import CORALean.ContSet.Ellipsoid.Real.Operations.DualVec

/-!
# `Ellipsoid.pullback`

The direction pulled back into generator space, which is what the support
value is the length of.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   05-September-2026
-- Last revision: ---

namespace CORALean.Real

open Matrix

variable {n : ℕ}

/-- The direction pulled back into generator space, which is what the support
value is the length of. -/
noncomputable def Ellipsoid.pullback (E : Ellipsoid n) (c : Vec ℝ n →ₗ[ℝ] ℝ) : Vec ℝ E.k :=
  E.Gᵀ *ᵥ dualVec c

end CORALean.Real
