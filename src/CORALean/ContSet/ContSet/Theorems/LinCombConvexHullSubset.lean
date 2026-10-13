import CORALean.ContSet.ContSet.Definitions.ConvexSet
import CORALean.ContSet.ContSet.Theorems.ConvexHullUnionEqSegments

/-!
# For a convex representation, `linComb` holds the convex hull of the union

`linComb_outer` and `convexHull_union_eq_segments`: an enclosure of CORA's `convHull_`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet

variable {α : Type} [AddCommGroup α] [Module ℝ α] {S : Type} [ContSet S α]


-- =======================================  MAIN THEOREM  ======================================= --

theorem LinComb.convexHull_subset_linComb [LinComb S α] [ConvexSet S α] (s t : S)
    (hs : (construct s).Nonempty) (ht : (construct t).Nonempty) :
    convexHull ℝ (construct s ∪ construct t) ⊆ construct (LinComb.linComb s t) := by
  rw [convexHull_union_eq_segments hs ht (ConvexSet.convex_construct s)
    (ConvexSet.convex_construct t)]
  exact LinComb.linComb_outer s t

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
