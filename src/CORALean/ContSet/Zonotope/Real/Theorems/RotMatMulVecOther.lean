import CORALean.ContSet.Zonotope.Real.Operations.RotMat
import Mathlib.Data.Matrix.Mul

/-!
# `rotMat` off the two coordinates

The other coordinates are unchanged.
-/

-- Authors:       Tobias Ladner
-- Written:       02-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix


-- =======================================  MAIN THEOREM  ======================================= --

/-- The other coordinates are unchanged. -/
theorem rotMat_mulVec_other {n : ℕ} (i j : Fin n) (angle : ℝ) (x : Vec ℝ n) (k : Fin n)
    (hki : k ≠ i) (hkj : k ≠ j) : (rotMat n i j angle *ᵥ x) k = x k := by
  simp only [mulVec, dotProduct, rotMat, hki, hkj, if_false]
  simp

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
