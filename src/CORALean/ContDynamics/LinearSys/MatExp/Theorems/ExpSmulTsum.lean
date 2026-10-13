module

public import CORALean.ContSet.Interval.Real.Interval
public import Mathlib.Analysis.Normed.Algebra.Exponential
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Analysis.Matrix.Normed

@[expose] public section

/-!
# The exponential of a scaled matrix, as one series in the unscaled matrix

`exp` expands in powers of `t • A`; pulling `t` out of each power leaves a
series in `A` alone, with the scalar folded into the coefficient. That is the
shape a difference of two such series needs, since `A^i` then matches between
them term by term.
-/

-- Authors:       Claude Opus 5
-- Written:       18-August-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix NormedSpace

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- The exponential of a scaled matrix, with the scalar pulled out of the power. -/
theorem exp_smul_tsum (A : Mat ℝ n n) (t : ℝ) :
    exp (t • A) = ∑' i : ℕ, (((Nat.factorial i : ℝ))⁻¹ * t ^ i) • A ^ i := by
  have h : exp (t • A) = ∑' i : ℕ, ((Nat.factorial i : ℝ))⁻¹ • (t • A) ^ i := by
    rw [exp_eq_tsum (𝕂 := ℝ)]
  rw [h]
  exact tsum_congr fun i => by rw [smul_pow, smul_smul]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
