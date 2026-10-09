import CORALean.ContSet.Ellipsoid.Real.Operations.IsIntersectingPoint
import CORALean.ContSet.Ellipsoid.Real.Theorems.ContainsPointIff

/-!
# A point intersects an ellipsoid iff the ellipsoid contains it

For a full-rank ellipsoid, `Ellipsoid.isIntersectingPoint` holds iff `{p}` and the ellipsoid are
not disjoint. Exact for the point, at tolerance `0`.
-/

-- Authors:       Tobias Ladner
-- Written:       08-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Ellipsoid.isIntersectingPoint_iff (E : Ellipsoid n) (hr : E.rank = n) (p : Vec ℝ n) :
    E.isIntersectingPoint p ↔ ¬ Disjoint ({p} : Set (Vec ℝ n)) E.construct := by
  unfold Ellipsoid.isIntersectingPoint
  rw [Ellipsoid.containsPoint_iff E hr p, Set.disjoint_singleton_left, not_not]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
