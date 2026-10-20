module

public import CORALean.ContSet.Ellipsoid.Real.Operations.Generators
public import Mathlib.Analysis.Matrix.PosDef
public import Mathlib.Algebra.Order.Star.Real

@[expose] public section

/-!
# `generators(E)` has the shape matrix of `E`

CORA's `generators` returns a matrix `G` with `G Gᵀ = Q`: `U sqrt(D) sqrt(D)ᵀ Uᵀ = U D Uᵀ = Q`,
the eigenvalues of the positive semi-definite `Q` being nonnegative. Exact for the shape matrix,
and so for the set: `construct_eq_of_factor` makes the image of the unit ball under this matrix
the ellipsoid itself.

## Inputs
* `E` – ellipsoid

## Hypotheses
* none

## Conclusion
* `generators(E)` times its transpose is `Q`
-/

-- Authors:       Claude Opus 5.5
-- Written:       08-October-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Ellipsoid.generators_mul_transpose (E : Ellipsoid n) : -- --- CONCL ---
    E.generators * E.generatorsᵀ = E.Q := by -- --- PROOF ---
  have hQ : E.Q.IsHermitian := E.psd.isHermitian
  have hnn : ∀ i, 0 ≤ hQ.eigenvalues i := E.psd.eigenvalues_nonneg
  set U : Mat ℝ n n := (hQ.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℝ) with hU
  have hspec : E.Q = U * Matrix.diagonal hQ.eigenvalues * Uᵀ := by
    have := hQ.spectral_theorem
    simpa [hU, Matrix.star_eq_conjTranspose, Function.comp_def] using this
  -- `sqrt(D) sqrt(D)ᵀ = D` since the eigenvalues are nonnegative
  have hD : Matrix.diagonal (fun i => Real.sqrt (hQ.eigenvalues i)) *
      (Matrix.diagonal (fun i => Real.sqrt (hQ.eigenvalues i)))ᵀ
        = Matrix.diagonal hQ.eigenvalues := by
    rw [Matrix.diagonal_transpose, Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    exact Real.mul_self_sqrt (hnn i)
  have hG : E.generators = U * Matrix.diagonal (fun i => Real.sqrt (hQ.eigenvalues i)) := rfl
  rw [hG, Matrix.transpose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc (Matrix.diagonal _), hD,
    ← Matrix.mul_assoc]
  exact hspec.symm

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
