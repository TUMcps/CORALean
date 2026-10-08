import CORALean.ContDynamics.LinearSys.MatExp.Operations.ExpIntegral
import CORALean.ContDynamics.LinearSys.MatExp.Theorems.MulExpIntegralEq

/-!
# The integrated exponential against `A`

`A ∫₀ᵗ e^{Aσ} dσ = e^{At} - I`, so for invertible `A`, `∫₀ᵗ e^{Aσ} dσ = A⁻¹(e^{At} - I)`:
[1, Eq. 12]'s constant-input solution, and [2, Eq. 5]'s `Γ(t) = A⁻¹(e^{At} - I)`, with
`expIntegral_constInput` giving the integral against the input. Termwise:
`A · Aⁱ tⁱ⁺¹/(i+1)!` is term `i + 1` of `e^{At}`, and the term `i = 0` of `e^{At}` is the
`I` subtracted. [1]'s fallback for a singular `A` — "factor
`A⁻¹` into the power series" — is `expIntegral` itself.

## References

* [1] M. Wetzlinger, A. Kulmburg and M. Althoff. "Inner Approximations of Reachable Sets for
  Nonlinear Systems using the Minkowski Difference". IEEE Control Systems Letters,
  8:2033-2038, 2024.
* [2] M. Althoff and B. H. Krogh. "Avoiding Geometric Intersection Operations in
      Reachability Analysis of Hybrid Systems". In Proc. of the 15th ACM
      International Conference on Hybrid Systems: Computation and Control (HSCC),
      2012, pp. 45-54.
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


-- =======================================  MAIN THEOREM  ======================================= --

theorem MatExp.expIntegral_eq_inv_mul (A : Mat ℝ n n) (hA : IsUnit A.det) (t : ℝ) :
    MatExp.expIntegral A t = A⁻¹ * (exp (t • A) - 1) := by
  rw [← MatExp.mul_expIntegral, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hA,
    Matrix.one_mul]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
