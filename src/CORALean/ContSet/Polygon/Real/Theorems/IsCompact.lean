import CORALean.ContSet.Polygon.Real.Polygon

/-!
# A polygon is compact

CORA's `polygon/isBounded` returns `true`: a finite union of polytopes is bounded, and closed.
-/

-- Authors:       Tobias Ladner
-- Written:       02-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

theorem Polygon.isCompact_construct (P : Polygon) :
    IsCompact (ContSet.construct P) := by
  show IsCompact (⋃ s ∈ P.sets, ContSet.construct s)
  exact (List.finite_toSet P.sets).isCompact_biUnion fun p _ => VPolytope.isCompact_construct p

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
