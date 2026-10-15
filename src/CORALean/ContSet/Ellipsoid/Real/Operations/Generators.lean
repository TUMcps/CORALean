module

public import CORALean.ContSet.Ellipsoid.Real.Ellipsoid
public import Mathlib.Analysis.Matrix.Spectrum

@[expose] public section

/-!
# `Ellipsoid.generators`

CORA's `@ellipsoid/generators.m`: `[U,D,~] = svd(Q); G = U * sqrt(D)`, a square generator matrix
of the shape matrix `Q`. `Q` is symmetric positive semi-definite, so its singular value
decomposition is its eigendecomposition `Q = U D Uᵀ`; here `U` is Mathlib's orthonormal
eigenvector matrix and `D` the diagonal of eigenvalues, in Mathlib's order (CORA's `svd` sorts
them in decreasing order, an order that does not enter `G Gᵀ = Q`). The result differs from the
symmetric square root `E.G` in general, by the orthogonal factor `Uᵀ`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       08-October-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `generators(E)`: `U * sqrt(D)` from the eigendecomposition `Q = U D Uᵀ`. -/
noncomputable def Ellipsoid.generators (E : Ellipsoid n) : Mat ℝ n n :=
  let hQ : E.Q.IsHermitian := E.psd.isHermitian
  let U : Mat ℝ n n := (hQ.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℝ)
  let D := Matrix.diagonal (fun i => Real.sqrt (hQ.eigenvalues i))
  let G := U * D
  G

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
