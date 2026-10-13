import CORALean.ContSet.Ellipsoid.Real.Operations.Shape
import Mathlib.LinearAlgebra.Matrix.Rank

/-!
# `Ellipsoid.rank`

CORA's `@ellipsoid/rank`: the number of singular values of the shape matrix `Q = G Gᵀ` above the
tolerance `d(1) * E.TOL`. Here the exact rank, the tolerance being `0` (as for `Zonotope.rank`):
the rank of the stored generator matrix `G`, which `Ellipsoid.rank_shape` shows equals that of `Q`.
CORA's `rank` of an empty ellipsoid is `0`; an `Ellipsoid` here is never empty (`k = 0` is the
point `q`), so that case does not arise.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `ellipsoid/rank`: the rank of the generator matrix. -/
noncomputable def Ellipsoid.rank (E : Ellipsoid n) : ℕ := E.G.rank

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
