module

public import CORALean.ContSet.ContSet.Theorems.ConvexHullUnionEqSegments
public import CORALean.ContSet.ConZonotope.Real.Theorems.Convex
public import CORALean.ContSet.ConZonotope.Real.Theorems.LinCombInner
public import CORALean.ContSet.ConZonotope.Real.Theorems.LinCombOuter

@[expose] public section

/-!
# `linComb` of two nonempty constrained zonotopes is the convex hull of the union

`linComb_outer` and `linComb_inner` bound `linComb` by the segments from both sides, and for two
convex nonempty sets the segments are the convex hull of the union. So CORA's exact `convHull_`
(Raghuraman and Koeln) is `linComb` here, for nonempty operands; for an empty one CORA returns the
other operand, which this does not claim.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =======================================  MAIN THEOREM  ======================================= --

theorem ConZonotope.linComb_eq_convexHull (cZ₁ cZ₂ : ConZonotope α)
    (h₁ : cZ₁.construct.Nonempty) (h₂ : cZ₂.construct.Nonempty) :
    (cZ₁.linComb cZ₂).construct = convexHull ℝ (cZ₁.construct ∪ cZ₂.construct) := by
  rw [convexHull_union_eq_segments h₁ h₂ cZ₁.convex_construct cZ₂.convex_construct]
  exact Set.Subset.antisymm (ConZonotope.linComb_inner cZ₁ cZ₂ h₁ h₂)
    (ConZonotope.linComb_outer cZ₁ cZ₂)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
