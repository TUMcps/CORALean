import CORALean.ContSet.Ellipsoid.Real.Operations.EllipsoidNorm

/-!
# `Ellipsoid.containsPoint`

CORA's `@ellipsoid/contains_` for a point `p`, through `priv_containsPoint`: `scaling =
ellipsoidNorm(p - c)` with `c = center(E)`, and `res` is `scaling <= 1 + tol`, here at `tol = 0`
and for a full-rank `E` (where `ellipsoidNorm` is modelled). The branches for a point or an empty
ellipsoid, a set argument (an ellipsoid through the SDP of `priv_containsEllipsoid`, a capsule
through two ellipsoids, vertex enumeration for the polytopes, a Grothendieck SDP for the
zonotope) and the tolerance are not formalized.
-/

-- Authors:       Tobias Ladner
-- Written:       04-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `contains_(E, p)` at `tol = 0`: `ellipsoidNorm(p - c) <= 1`. -/
noncomputable def Ellipsoid.containsPoint (E : Ellipsoid n) (p : Vec ℝ n) : Prop :=
  let c := E.q
  let scaling := E.ellipsoidNorm (p - c)
  scaling ≤ 1

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
