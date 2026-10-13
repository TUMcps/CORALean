module

public import CORALean.ContSet.Zonotope.Real.Operations.RotMat
public import Mathlib.Data.Matrix.Mul

@[expose] public section

/-!
# `rotMat` off the two coordinates

The other coordinates are unchanged.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


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
