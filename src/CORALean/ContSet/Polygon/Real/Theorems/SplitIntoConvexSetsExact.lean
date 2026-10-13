import CORALean.ContSet.Polygon.Real.Operations.SplitIntoConvexSets
import CORALean.ContSet.VPolytope.Real.Theorems.Convex
import CORALean.ContSet.VPolytope.Real.Instances

/-!
# `Polygon.splitIntoConvexSets` is a convex split

Exactly: every returned set is convex and their union is the region.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

theorem Polygon.splitIntoConvexSets_exact (P : Polygon) :
    (∀ p ∈ Polygon.splitIntoConvexSets P, Convex ℝ (VPolytope.construct p)) ∧
      (⋃ p ∈ Polygon.splitIntoConvexSets P, VPolytope.construct p) = ContSet.construct P :=
  ⟨fun p _ => p.convex_construct, rfl⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
