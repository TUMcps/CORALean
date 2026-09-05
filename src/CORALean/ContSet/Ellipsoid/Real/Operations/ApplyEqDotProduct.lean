import CORALean.ContSet.Ellipsoid.Real.Operations.DualVec

/-!
# A functional applied is the dot product with its `dualVec`
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   05-September-2026
-- Last revision: ---

namespace CORALean.Real

variable {n : ℕ}

theorem apply_eq_dotProduct (c : Vec ℝ n →ₗ[ℝ] ℝ) (x : Vec ℝ n) : c x = dualVec c ⬝ᵥ x := by
  rw [LinearMap.pi_apply_eq_sum_univ c x, dotProduct]
  exact Finset.sum_congr rfl fun i _ => by rw [smul_eq_mul]; exact mul_comm _ _

end CORALean.Real
