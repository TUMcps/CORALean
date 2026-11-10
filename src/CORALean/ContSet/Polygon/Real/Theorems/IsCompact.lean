module

public import CORALean.ContSet.Polygon.Real.Polygon
public import CORALean.ContSet.VPolytope.Real.Instances

@[expose] public section

/-!
# A polygon is compact

CORA's `polygon/isBounded` returns `true`: a finite union of polytopes is bounded, and closed.

## Inputs
* `P` – polygon

## Hypotheses
* none

## Conclusion
* A polygon is compact
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

theorem Polygon.isCompact_toSet (P : Polygon) :
    IsCompact (ContSetLike.toSet P) := by
  show IsCompact (⋃ s ∈ P.sets, ContSetLike.toSet s)
  exact (List.finite_toSet P.sets).isCompact_biUnion fun p _ => VPolytope.isCompact_toSet p

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
