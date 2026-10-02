import CORALean.ContSet.Interval.Real.Interval
import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.Topology.Instances.Matrix
import Mathlib.Analysis.Matrix.Normed
/-!
# The exponential of a scaled matrix, as one series in the unscaled matrix

`exp` expands in powers of `t • A`; pulling `t` out of each power leaves a
series in `A` alone, with the scalar folded into the coefficient. That is the
shape a difference of two such series needs, since `A^i` then matches between
them term by term.
-/

-- Authors:       Tobias Ladner
-- Written:       18-August-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix NormedSpace

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

-- `exp_eq_tsum` is elaborated against the four local `Matrix.linftyOp*` instances
set_option maxHeartbeats 200000 in
/-- The exponential of a scaled matrix, with the scalar pulled out of the power. -/
theorem exp_smul_tsum (A : Mat ℝ n n) (t : ℝ) :
    exp (t • A) = ∑' i : ℕ, (((Nat.factorial i : ℝ))⁻¹ * t ^ i) • A ^ i := by
  have h : exp (t • A) = ∑' i : ℕ, ((Nat.factorial i : ℝ))⁻¹ • (t • A) ^ i := by
    rw [exp_eq_tsum (𝕂 := ℝ)]
  rw [h]
  exact tsum_congr fun i => by rw [smul_pow, smul_smul]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
