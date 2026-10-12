import CORALean.ContDynamics.LinProbSys.LinProbSys
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# The covariance of one step's noise, sign corrected

`priv_inputSolution` of `linProbSys/initReach` [1] with the sign of the exponent corrected. It
takes the eigendecomposition `A = V Λ V⁻¹`, `Λ = diag(λ)` with real eigenvalues as CORA's
`eig` gives them for a diagonalizable `A`, transforms the noise to `C* = V⁻¹C`,
`D = C* C*ᵀ`, and takes in those coordinates
`Σ_ij = D_ij/(λ_i + λ_j) (e^{(λ_i+λ_j) r} - 1)`, which is `∫₀ʳ D_ij e^{(λ_i+λ_j)s} ds`, the
limit `D_ij r` where `λ_i + λ_j = 0`, and returns `V Σ Vᵀ`. CORA writes
`(1 - e^{-(λ_i+λ_j) r})` instead, the covariance for the drift `-A` (`initReachCov`, see
FINDINGS.md), and divides by `λ_i + λ_j` with no case for `0`.

The eigendecomposition is an argument, as `[V,W] = eig(A)` is CORA's: what ties it to `A` is
the hypothesis of `inputCov_eq_noiseCovariance`. CORA's `aux_generators` then factors the
result as `G Gᵀ` after symmetrizing it, a no-op in exact arithmetic (`V Σ Vᵀ` is symmetric), so
the covariance is returned as it is.

## References

* [1] `contDynamics/@linProbSys/private/priv_inputSolution.m`
-/

-- Authors:       Tobias Ladner
-- Written:       11-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `Sigma` of `priv_inputSolution`, line by line, the exponent's sign corrected. -/
noncomputable def LinProbSys.inputCov (V : Mat ℝ n n) (lambda : Fin n → ℝ) (C : Mat ℝ n n)
    (r : ℝ) : Mat ℝ n n :=
  let Ct := V⁻¹ * C                                                 -- C=inv(V)*obj.C
  let D := Ct * Ctᵀ                                                 -- D=C*C.'
  let Sigma : Mat ℝ n n := fun i j =>
    let lambdaSum := lambda i + lambda j                           -- lambdaSum=lambda(i)+lambda(j)
    if lambdaSum = 0 then D i j * r                                 -- the limit at lambdaSum = 0
    else D i j / lambdaSum * (Real.exp (lambdaSum * r) - 1)         -- Sigma(i,j), corrected
  V * Sigma * Vᵀ                                                    -- Sigma=V*Sigma*V.'

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
