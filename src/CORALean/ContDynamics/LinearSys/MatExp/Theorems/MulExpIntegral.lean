import CORALean.ContDynamics.LinearSys.MatExp.Operations.ExpIntegral
import CORALean.ContDynamics.LinearSys.MatExp.Theorems.ExpIntegral

/-!
# The integrated exponential against `A`

`A ∫₀ᵗ e^{Aσ} dσ = e^{At} - I`, so for invertible `A`, `∫₀ᵗ e^{Aσ} dσ = A⁻¹(e^{At} - I)`:
[1, Eq. 12]'s constant-input solution, with `expIntegral_constInput` giving the integral
against the input. Termwise: `A · Aⁱ tⁱ⁺¹/(i+1)!` is term `i + 1` of `e^{At}`, and the
term `i = 0` of `e^{At}` is the `I` subtracted. [1]'s fallback for a singular `A` — "factor
`A⁻¹` into the power series" — is `expIntegral` itself.

## References

* [1] M. Wetzlinger, A. Kulmburg and M. Althoff. "Inner Approximations of Reachable Sets for
  Nonlinear Systems using the Minkowski Difference". IEEE Control Systems Letters,
  8:2033-2038, 2024.
-/

-- Authors:       Tobias Ladner
-- Written:       04-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix NormedSpace

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The series identity behind it: `A ∫₀ᵗ e^{Aσ} dσ = e^{At} - I`. -/
theorem MatExp.aux_mul_expIntegral (A : Mat ℝ n n) (t : ℝ) :
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


-- =======================================  MAIN THEOREM  ======================================= --

theorem MatExp.expIntegral_eq_inv_mul (A : Mat ℝ n n) (hA : IsUnit A.det) (t : ℝ) :
    MatExp.expIntegral A t = A⁻¹ * (exp (t • A) - 1) := by
  rw [← MatExp.aux_mul_expIntegral, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hA,
    Matrix.one_mul]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
