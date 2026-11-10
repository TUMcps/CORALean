module

public import CORALean.ContSet.ContSet.Definitions.Interfaces
public import CORALean.ContSet.ContSet.Theorems.ConvexHullUnionEqSetLinComb

@[expose] public section

/-!
# For a convex representation, `linComb` holds the convex hull of the union

`linComb_outer` and `convexHull_union_eq_setLinComb`: an enclosure of CORA's `convHull_`.

## Inputs
* `s` – set
* `t` – set

## Hypotheses
* `hs` – `s` nonempty
* `ht` – `t` nonempty

## Conclusion
* convex hull of the union lies in the linear combination
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
    (hs : (toSet s).Nonempty) (ht : (toSet t).Nonempty) :
    convexHull ℝ (toSet s ∪ toSet t) ⊆ toSet (LinComb.linComb s t) := by
  rw [convexHull_union_eq_setLinComb hs ht (ConvexSet.convex_toSet s)
    (ConvexSet.convex_toSet t)]
  exact LinComb.linComb_outer s t

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
