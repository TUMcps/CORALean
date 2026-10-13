import CORALean.ContSet.Polygon.Real.Polygon
import CORALean.ContSet.VPolytope.Real.Instances

/-!
# A polygon is compact

CORA's `polygon/isBounded` returns `true`: a finite union of polytopes is bounded, and closed.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

theorem Polygon.isCompact_construct (P : Polygon) :
    IsCompact (ContSet.construct P) := by
  show IsCompact (⋃ s ∈ P.sets, ContSet.construct s)
  exact (List.finite_toSet P.sets).isCompact_biUnion fun p _ => VPolytope.isCompact_construct p

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
