module

public import CORALean.ContSet.Ellipsoid.Real.Operations.ContainsPoint

@[expose] public section

/-!
# `Ellipsoid.isIntersectingPoint`

The numeric branch of CORA's `@ellipsoid/isIntersecting_.m`: `if isnumeric(S), res =
contains_(E, S, type, tol, 0, false, false)`, a point intersects the ellipsoid iff the ellipsoid
contains it, here at `tol = 0` through `Ellipsoid.containsPoint`. The emptiness branch (an
`Ellipsoid` is never empty), the branch for an ellipsoid that is a point, and the set arguments
through `distance` (solver-dependent) and `priv_isIntersectingMixed` are not formalized.

## Inputs
* `E` – ellipsoid
* `p` – point

## Output
* `E` contains `p`
-/

-- Authors:       Claude Opus 5.5
-- Written:       08-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `isIntersecting_(E, p)` for a point `p`: `contains_(E, p)`. -/
noncomputable def Ellipsoid.isIntersectingPoint (E : Ellipsoid n) (p : Vec ℝ n) : Prop :=
  E.containsPoint p

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
