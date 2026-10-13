import CORALean.ContDynamics.LinearSys.MatExp.Operations.ExpIntegral
import CORALean.ContDynamics.LinearSys.MatExp.Theorems.ExpIntegral

/-!
# `A ∫₀ᵗ e^{Aσ} dσ = e^{At} - I`

The series identity behind `expIntegral_eq_inv_mul`, with no invertibility asked: the integrated
exponential is `A⁻¹ (e^{At} - I)` where `A` is invertible [1, Eq. 12], and this is what remains
of it where it is not. Termwise: `A · Aⁱ tⁱ⁺¹/(i+1)!` is term `i + 1` of `e^{At}`.

## References

* [1] M. Wetzlinger, A. Kulmburg and M. Althoff. "Inner Approximations of Reachable Sets for
  Nonlinear Systems using the Minkowski Difference". IEEE Control Systems Letters,
  8:2033-2038, 2024.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix NormedSpace

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem MatExp.mul_expIntegral (A : Mat ℝ n n) (t : ℝ) :
    A * MatExp.expIntegral A t = exp (t • A) - 1 := by -- --- PROOF ---
  have hs := expSeries_summable' (𝕂 := ℝ) (t • A)
  rw [MatExp.expIntegral, ← (MatExp.summable_expIntegral A t).tsum_mul_left,
    exp_eq_tsum (𝕂 := ℝ)]
  beta_reduce
  erw [hs.tsum_eq_zero_add]
  rw [pow_zero, Nat.factorial_zero, Nat.cast_one, inv_one, one_smul,
    add_sub_cancel_left]
  refine tsum_congr fun i => ?_
  rw [Matrix.mul_smul, ← pow_succ', smul_pow, smul_smul, mul_comm]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
