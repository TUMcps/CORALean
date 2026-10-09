import CORALean.ContSet.Ellipsoid.Real.Operations.Shape
import Mathlib.Analysis.Matrix.Spectrum

/-!
# `Ellipsoid.generators`

CORA's `@ellipsoid/generators.m`: `[U,D,~] = svd(Q); G = U * sqrt(D)`, a square generator matrix
of the shape matrix `Q = G Gᵀ`. `Q` is symmetric positive semi-definite, so its singular value
decomposition is its eigendecomposition `Q = U D Uᵀ`; here `U` is Mathlib's orthonormal
eigenvector matrix and `D` the diagonal of eigenvalues, in Mathlib's order (CORA's `svd` sorts
them in decreasing order, an order that does not enter `G Gᵀ = Q`). The result differs from the
stored `E.G`, a generator matrix with the same `Q` and not in general `n × n`.
-/

-- Authors:       Tobias Ladner
-- Written:       08-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `generators(E)`: `U * sqrt(D)` from the eigendecomposition `Q = U D Uᵀ`. -/
noncomputable def Ellipsoid.generators (E : Ellipsoid n) : Mat ℝ n n :=
  let hQ : E.shape.IsHermitian := by
    simpa [Ellipsoid.shape] using Matrix.isHermitian_mul_conjTranspose_self E.G
  let U : Mat ℝ n n := (hQ.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℝ)
  let D := Matrix.diagonal (fun i => Real.sqrt (hQ.eigenvalues i))
  let G := U * D
  G

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
