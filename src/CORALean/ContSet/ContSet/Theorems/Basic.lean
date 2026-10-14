module

public import CORALean.ContSet.ContSet.Definitions.CompactSet
public import CORALean.ContSet.ContSet.Operations.Basic
public import CORALean.ContSet.ContSet.Theorems.UnionSubsetSegments

@[expose] public section

/-!
# `ContSet/ContSet/Theorems`: small declarations

One section per declaration, at most five code lines each; alphabetical, after the
sections each one uses (CONTRIBUTING, "Small declarations").
-/


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --


namespace CORALean

open ContSet

variable {S α : Type} [NormedAddCommGroup α] [NormedSpace ℝ α] [ContSet S α]


-- =============================  `CompactSet.isBounded_construct`  ============================= --
-- Authors:       Claude Sonnet 5
-- Written:       02-September-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `CompactSet.isBounded_construct`: compactness over a normed space gives boundedness for free. -/
theorem CompactSet.isBounded_construct [CompactSet S α] (s : S) :
    Bornology.IsBounded (construct s) :=
  (CompactSet.isCompact_construct s).isBounded


-- =============================  `CompactSet.isClosed_construct`  ============================== --
-- Authors:       Claude Sonnet 5
-- Written:       02-September-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `CompactSet.isClosed_construct`: compactness over a normed space gives closedness for free. -/
theorem CompactSet.isClosed_construct [CompactSet S α] (s : S) : IsClosed (construct s) :=
  (CompactSet.isCompact_construct s).isClosed

end CORALean


namespace CORALean

open ContSet

variable {S α : Type} [ContSet S α] [Isequal S]


-- ==================================  `ContSet.eq_construct`  ================================== --
-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- If `eq` holds the two representations denote one set. Sound, not exact: `eq` can fail on
two representations of one set. -/
theorem ContSet.eq_construct {s t : S} (h : ContSet.eq s t) : construct s = construct t :=
  Isequal.isequal_construct s t h


-- ===============================  `ContSet.ne_of_construct_ne`  =============================== --
-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- If the denoted sets differ, `ne` holds. Only this direction: `ne` can hold of two
representations of one set, since `isequal` is conservative. -/
theorem ContSet.ne_of_construct_ne {s t : S} (h : construct s ≠ construct t) : ContSet.ne s t :=
  fun hi => h (Isequal.isequal_construct s t hi)

end CORALean


namespace CORALean

open ContSet Scalar

variable {S α : Type} [ContSet S α]


-- ==================================  `ContSet.uplus_exact`  =================================== --
-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `uplus` denotes the set it is given, so it is exact, not only an outer bound. -/
theorem ContSet.uplus_exact (s : S) : construct (ContSet.uplus s) = construct s := rfl

end CORALean


namespace CORALean

open ContSet

variable {α : Type} [AddCommGroup α] [Module ℝ α] {S : Type} [ContSet S α]


-- ==============================  `LinComb.union_subset_linComb`  ============================== --
-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `linComb_outer` and `union_subset_segments`: an enclosure of CORA's `or`. -/
theorem LinComb.union_subset_linComb [LinComb S α] (s t : S) (hs : (construct s).Nonempty)
    (ht : (construct t).Nonempty) :
    construct s ∪ construct t ⊆ construct (LinComb.linComb s t) :=
  (union_subset_segments hs ht).trans (LinComb.linComb_outer s t)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
