import CORALean.ContSet.Ellipsoid.Real.Operations.Rank

/-!
# The rank of the shape matrix

CORA's `rank(E)` counts the singular values of the shape matrix `Q = G Gᵀ`; `rank (G Gᵀ) = rank G`,
so the rank of the stored generator matrix is the same number (at tolerance `0`).
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

/-- The rank of CORA's shape matrix `Q = G Gᵀ` is the rank of `G`. -/
theorem Ellipsoid.rank_shape {n : ℕ} (E : Ellipsoid n) : E.shape.rank = E.rank :=
  Matrix.rank_self_mul_transpose E.G

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
