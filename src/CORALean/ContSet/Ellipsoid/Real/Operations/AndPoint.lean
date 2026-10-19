module

public import CORALean.ContSet.OptEmpty.OptEmpty
public import CORALean.ContSet.Ellipsoid.Real.Operations.OfPoint
public import CORALean.ContSet.Ellipsoid.Real.Instances

@[expose] public section

/-!
# `Ellipsoid.andPoint`

The numeric branch of CORA's `@ellipsoid/and_.m`: for a point `S`,
`if contains_(E, S, 'exact', eps, 0, false, false), E = ellipsoid(zeros(n), S), else E =
ellipsoid.empty(n)`. The point itself as a degenerate ellipsoid (`Q = 0`, center `S`) when it
lies in `E`, and the empty ellipsoid otherwise, here `OptEmpty.empty`, as no `Ellipsoid` denotes
`∅`. The membership test is the set-level `p ∈ E`, classical, at tolerance `0`; the
`representsa_(E, 'point')` branch has the same result for a point argument. The hyperplane,
polytope and ellipsoid branches (`priv_andHyperplane`, `priv_andPolytope`, `priv_andEllipsoidOA`,
`priv_andEllipsoidIA`) are not formalized.

## Inputs
* `E` – ellipsoid
* `p` – point

## Output
* the point as ellipsoid if `E` contains it, else empty
-/

-- Authors:       Claude Opus 5.5
-- Written:       08-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open scoped Classical

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `and_(E, p)` for a point `p`: the point as an ellipsoid if `E` contains it, else `∅`. -/
noncomputable def Ellipsoid.andPoint (E : Ellipsoid n) (p : Vec ℝ n) : OptEmpty (Ellipsoid n) :=
  if p ∈ E.construct then .of (Ellipsoid.ofPoint p) else .empty

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
