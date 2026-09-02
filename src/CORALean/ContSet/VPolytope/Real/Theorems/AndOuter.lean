import CORALean.ContSet.VPolytope.Real.Operations.And
import CORALean.ContSet.VPolytope.Real.Theorems.OfIntervalOuter
import CORALean.ContSet.VPolytope.Real.Theorems.IntervalOuter

/-!
# `VPolytope.and` contains the intersection

Three steps, each already proved: each hull sits in its own box, intersecting
boxes is exact, and a box sits in the hull of its corners.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Real

variable {n : ℕ}

theorem VPolytope.and_outer (P₁ P₂ : VPolytope (Vec ℝ n)) :
    P₁.construct ∩ P₂.construct ⊆ (P₁.and P₂).construct := by
  refine subset_trans ?_ (VPolytope.subset_ofInterval _)
  rw [Interval.and_exact]
  exact Set.inter_subset_inter P₁.interval_outer P₂.interval_outer

end CORALean.Real
