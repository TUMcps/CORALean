module

public import CORALean.ContSet.Ellipsoid.Real.Operations.DualVec
public import Mathlib.Data.Matrix.Mul
public import Mathlib.LinearAlgebra.Pi

@[expose] public section

/-!
# A functional applied is the dot product with its `dualVec`
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   05-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem apply_eq_dotProduct (c : Vec ℝ n →ₗ[ℝ] ℝ) (x : Vec ℝ n) : c x = dualVec c ⬝ᵥ x := by
  rw [LinearMap.pi_apply_eq_sum_univ c x, dotProduct]
  exact Finset.sum_congr rfl fun i _ => by rw [smul_eq_mul]; exact mul_comm _ _

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
