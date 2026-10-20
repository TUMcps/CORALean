module

public import CORALean.ContSet.ProbZonotope.Real.ProbZonotope

@[expose] public section

/-!
# `ProbZonotope.generators`

CORA's `generators(probZ)` (also the factor `V sqrt(W)` inside `probReduce`): the covariance is
symmetrized, `Σ ← (Σ + Σᵀ)/2`, "for numerical stability", and its eigendecomposition
`Σ = V W Vᵀ` gives the probabilistic generators `G = V √W`, one per dimension. The eigenvectors
are Mathlib's, `V` orthogonal; MATLAB's `eig` picks its own, and any choice gives the same
`G Gᵀ` (`Theorems.GeneratorsMulTranspose`). `√` is the real square root, which for a negative
eigenvalue is `0` where MATLAB's is imaginary: a covariance has none.

## Inputs
* `P` – probabilistic zonotope

## Output
* the probabilistic generators `G = V √W` of the symmetrized covariance
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --
namespace CORALean.Real

open Matrix

variable {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

theorem aux_symmetrize_isHermitian (S : Mat ℝ n n) :
    ((2 : ℝ)⁻¹ • (S + Sᵀ)).IsHermitian := by
  ext i j
  simp [Matrix.conjTranspose_apply, add_comm]
  ring


-- =====================================  MAIN DEFINITION  ====================================== --

noncomputable def ProbZonotope.generators (P : ProbZonotope n) : Mat ℝ n n :=
  ((aux_symmetrize_isHermitian P.cov).eigenvectorUnitary : Mat ℝ n n)
    * diagonal (fun i => Real.sqrt ((aux_symmetrize_isHermitian P.cov).eigenvalues i))

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
