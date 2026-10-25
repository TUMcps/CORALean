module

public import CORALean.ContDynamics.LinProbSys.LinProbSys

@[expose] public section

/-!
# The covariance of `initReach`'s probabilistic input solution

`priv_inputSolution` of `linProbSys/initReach` [1] takes the eigendecomposition `A = V Λ V⁻¹`,
`D = (V⁻¹C)(V⁻¹C)ᵀ`, `Σ_ij = D_ij/(λ_i + λ_j) (1 - e^{-(λ_i+λ_j) r})` and returns `V Σ Vᵀ`. At a
diagonal `A = diag(l)`, `V = I`, this is `D_ij/(l_i + l_j) (1 - e^{-(l_i+l_j) r})`: the form
[2, Sec. II] prints. It is the covariance for the drift `-A`, not `A`, see
`references/coverage/contDynamics/linProbSys.md`, row `initReach`.

## Inputs
* `l` – eigenvalues
* `C` – noise matrix
* `r` – step size

## Output
* the covariance matrix of the probabilistic input solution

## References

* [1] `contDynamics/@linProbSys/private/priv_inputSolution.m`
* [2] M. Althoff, O. Stursberg and M. Buss. "Safety Assessment for Stochastic Linear Systems using
      Enclosing Hulls of Probability Density Functions". 2009 European Control Conference (ECC),
      2009.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `Sigma(i,j)` at a diagonal `A`, as CORA computes it. -/
noncomputable def LinProbSys.initReachCov (l : Fin n → ℝ) (C : Mat ℝ n n) (r : ℝ) : Mat ℝ n n :=
  fun i j => (C * C.transpose) i j / (l i + l j) * (1 - Real.exp (-(l i + l j) * r))

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
