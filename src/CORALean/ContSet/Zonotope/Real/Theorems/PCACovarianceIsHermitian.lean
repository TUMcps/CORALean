import CORALean.ContSet.Zonotope.Real.Operations.PCACovariance

/-!
# The scatter matrix is Hermitian

Over `ℝ` the conjugate transpose is the transpose, so being Hermitian is being
symmetric, and `∑ l, g_l i * g_l j` is symmetric in `i` and `j` because
multiplication is commutative. That is the entire content.

It earns a file because of what it unlocks rather than what it says: Mathlib's
spectral theorem for matrices is stated for `Matrix.IsHermitian`, so this is
the term `pcaBasis` feeds to `Matrix.IsHermitian.eigenvectorUnitary` to get an
eigenvector basis at all.
-/

-- Authors:       Tobias Ladner
-- Written:       08-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n q r : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- `pcaCovariance` is Hermitian, which over `ℝ` is symmetric: the hypothesis
Mathlib's spectral theorem takes. -/
theorem Zonotope.pcaCovariance_isHermitian (Z : Zonotope (Vec ℝ n))
    (part : Split (Fin Z.h) into (Fin q) ⊕ (Fin r)) :
    (Z.pcaCovariance part).IsHermitian := by
  ext i j
  simp [Zonotope.pcaCovariance, Matrix.conjTranspose_apply, mul_comm]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
