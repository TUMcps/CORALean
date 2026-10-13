module

public import CORALean.ContSet.Fullspace.Real.Operations.ConvHull
public import CORALean.ContSet.Fullspace.Real.Fullspace
public import CORALean.ContSet.ContSet.ContSet
public import Mathlib.Analysis.Convex.Hull

@[expose] public section

/-!
# `Fullspace.convHull` is the convex hull

Exact for any operand: the hull contains the whole space already.
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open ContSet

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Fullspace.convHull_exact {S : Type} [ContSet S (Vec ℝ n)] (F : Fullspace n) (s : S) :
    convexHull ℝ (F.construct ∪ ContSet.construct s) = (F.convHull s).construct :=
  Set.eq_univ_of_univ_subset ((Set.subset_union_left).trans (subset_convexHull ℝ _))

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
