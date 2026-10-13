import CORALean.ContSet.Ellipsoid.Real.Operations.Generators
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Algebra.Order.Star.Real

/-!
# `generators(E)` has the shape matrix of `E`

CORA's `generators` returns a matrix `G` with `G Gᵀ = Q`: `U sqrt(D) sqrt(D)ᵀ Uᵀ = U D Uᵀ = Q`,
the eigenvalues of `Q = E.G (E.G)ᵀ` being nonnegative. Exact for the shape matrix. That the
ellipsoid built on this matrix is the same set as `E` needs `G Gᵀ = H Hᵀ` to imply the same
image of the unit ball, which is not stated here.
-/

-- Authors:       Claude Opus 5.5
-- Written:       08-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Ellipsoid.generators_mul_transpose (E : Ellipsoid n) :
    E.generators * E.generatorsᵀ = E.shape := by -- --- PROOF ---
  have hQ : E.shape.IsHermitian := by
    simpa [Ellipsoid.shape] using Matrix.isHermitian_mul_conjTranspose_self E.G
  have hpsd : Matrix.PosSemidef E.shape := by
    simpa [Ellipsoid.shape] using Matrix.posSemidef_self_mul_conjTranspose E.G
  have hnn : ∀ i, 0 ≤ hQ.eigenvalues i := hpsd.eigenvalues_nonneg
  set U : Mat ℝ n n := (hQ.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℝ) with hU
  have hspec : E.shape = U * Matrix.diagonal hQ.eigenvalues * Uᵀ := by
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
