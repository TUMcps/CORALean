module

public import CORALean.ContSet.Ellipsoid.Real.Operations.IsIntersectingPoint
public import CORALean.ContSet.Ellipsoid.Real.Theorems.ContainsPointIff

@[expose] public section

/-!
# A point intersects an ellipsoid iff the ellipsoid contains it

For a full-rank ellipsoid, `Ellipsoid.isIntersectingPoint` holds iff `{p}` and the ellipsoid are
not disjoint. Exact for the point, at tolerance `0`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       08-October-2026
-- Last update:   ---
-- Reviewed:      ---


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
