module

public import CORALean.ContSet.ContSet.Theorems.UnionSubsetSegments

@[expose] public section

/-!
# Whatever represents `linComb` of two nonempty sets holds both

`linComb_outer` and `union_subset_segments`: an enclosure of CORA's `or`.
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

theorem LinComb.union_subset_linComb [LinComb S α] (s t : S) (hs : (construct s).Nonempty)
    (ht : (construct t).Nonempty) :
    construct s ∪ construct t ⊆ construct (LinComb.linComb s t) :=
  (union_subset_segments hs ht).trans (LinComb.linComb_outer s t)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
