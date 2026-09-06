import CORALean.ContSet.Ellipsoid.Real.Theorems.ConstructEqImage
import CORALean.ContSet.Ellipsoid.Real.Theorems.ContinuousAffine

/-!
# An ellipsoid is compact

The Euclidean unit ball is compact — closed because `‖·‖₂` is continuous, and
inside the supremum-norm ball the ambient type carries because no coordinate
exceeds the whole — and the affine map onto the ellipsoid is continuous.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   04-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Ellipsoid.isCompact_construct (E : Ellipsoid n) : IsCompact E.construct := by
  rw [E.construct_eq_image]
  exact isCompact_unitBall₂.image E.continuous_affine

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
