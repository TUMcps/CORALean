import CORALean.ContSet.Ellipsoid.Real.Ellipsoid
import CORALean.Global.Tensor

/-!
# `Ellipsoid.enclosePointsOriented`

The first steps of CORA's `@ellipsoid/enclosePoints.m` at `method = 'cov'` for points spanning the
whole space: `c = mean(points, 2)`, `points = points - c`, `points = T' * points` and
`orientedMatrix = U' * points`, one column per point. `T` and `U` are arguments, as no SVD
algorithm exists here (see `Ellipsoid.enclosePointsCov`). At least one point (`NeZero N`).
-/

-- Authors:       Tobias Ladner
-- Written:       08-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n N : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `orientedMatrix = U' * (T' * (points - c))`, one column per point. -/
noncomputable def Ellipsoid.enclosePointsOriented [NeZero N] (pts : Fin N → Vec ℝ n)
    (T U : Mat ℝ n n) : Fin N → Vec ℝ n :=
  let c := (1 / (N : ℝ)) • ∑ j, pts j
  let points := fun j => pts j - c
  let pointsT := fun j => Tᵀ *ᵥ points j
  let orientedMatrix := fun j => Uᵀ *ᵥ pointsT j
  orientedMatrix

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
