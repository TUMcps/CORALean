import CORALean.ContDynamics.LinearSys.MatExp.Operations.ExpTaylor
import Mathlib.Data.Matrix.Basic

/-!
# The truncated series applied to a vector, with the time pulled out

`expTaylor (τ • A) η *ᵥ v` order by order, each order's `τ^i` a scalar in front
of `Aⁱ *ᵥ v` rather than inside the matrix. That is what lets an input solution
take the matrix out of an integral over `τ` and leave a scalar weight behind.
-/

-- Authors:       Tobias Ladner
-- Written:       08-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix NormedSpace

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- The exponential's first `η+1` orders, applied to a vector, with the powers
of `τ` pulled out as scalars. -/
theorem MatExp.expTaylor_smul_mulVec (A : Mat ℝ n n) (η : ℕ) (τ : ℝ) (v : Vec ℝ n) :
    MatExp.expTaylor (τ • A) η *ᵥ v
      = ∑ i ∈ Finset.range (η + 1), ((Nat.factorial i : ℝ)⁻¹ * τ ^ i) • (A ^ i *ᵥ v) := by
  rw [MatExp.expTaylor, Matrix.sum_mulVec]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [smul_pow, Matrix.smul_mulVec, Matrix.smul_mulVec, mul_smul]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
