import CORALean.ContSet.Ellipsoid.Real.Operations.ContainsPoint

/-!
# `Ellipsoid.isIntersectingPoint`

The numeric branch of CORA's `@ellipsoid/isIntersecting_.m`: `if isnumeric(S), res =
contains_(E, S, type, tol, 0, false, false)`, a point intersects the ellipsoid iff the ellipsoid
contains it, here at `tol = 0` through `Ellipsoid.containsPoint`. The emptiness branch (an
`Ellipsoid` is never empty), the branch for an ellipsoid that is a point, and the set arguments
through `distance` (solver-dependent) and `priv_isIntersectingMixed` are not formalized.
-/

-- Authors:       Tobias Ladner
-- Written:       08-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `isIntersecting_(E, p)` for a point `p`: `contains_(E, p)`. -/
noncomputable def Ellipsoid.isIntersectingPoint (E : Ellipsoid n) (p : Vec ℝ n) : Prop :=
  E.containsPoint p

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
