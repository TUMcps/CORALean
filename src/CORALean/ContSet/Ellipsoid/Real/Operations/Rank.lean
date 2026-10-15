module

public import CORALean.ContSet.Ellipsoid.Real.Ellipsoid
public import Mathlib.LinearAlgebra.Matrix.Rank

@[expose] public section

/-!
# `Ellipsoid.rank`

CORA's `@ellipsoid/rank`: the number of singular values of the shape matrix `Q` above the
tolerance `d(1) * E.TOL`. Here the exact rank of `Q`, the tolerance being `0` (as for
`Zonotope.rank`). CORA's `rank` of an empty ellipsoid is `0`; an `Ellipsoid` here is never empty
(`Q = 0` is the point `q`), so that case does not arise.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `ellipsoid/rank`: the rank of the shape matrix. -/
noncomputable def Ellipsoid.rank (E : Ellipsoid n) : ℕ := E.Q.rank

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
