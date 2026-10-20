module

public import CORALean.ContDynamics.LinProbSys.LinProbSys
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

@[expose] public section

/-!
# The covariance of one step's noise, sign corrected

`priv_inputSolution` of `linProbSys/initReach` [1] with the sign of the exponent corrected. It
takes the eigendecomposition `A = V Λ V⁻¹`, `Λ = diag(λ)`, transforms the noise to `C* = V⁻¹C`,
`D = C* C*ᵀ`, and takes `Σ_ij = D_ij/(λ_i + λ_j) (e^{(λ_i+λ_j) r} - 1)`, which is
`∫₀ʳ D_ij e^{(λ_i+λ_j)s} ds`, the limit `D_ij r` where `λ_i + λ_j = 0`, and returns `V Σ Vᵀ`. CORA
writes `(1 - e^{-(λ_i+λ_j) r})` instead, the covariance for the drift `-A` (`initReachCov`, see
`references/coverage/contDynamics/linProbSys.md`, row `initReach`). The eigendecomposition is an
argument, as `[V,W] = eig(A)` is CORA's: what ties it to `A` is the hypothesis of
`inputCov_eq_noiseCovariance`.

## Inputs
* `V` – eigenvector matrix
* `lambda` – eigenvalues
* `C` – noise matrix
* `r` – step size

## Output
* the corrected input covariance matrix

## References

* [1] `contDynamics/@linProbSys/private/priv_inputSolution.m`
-/

-- Authors:       Claude Opus 5.5
-- Written:       11-October-2026
-- Last update:   ---
-- Reviewed:      ---


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
