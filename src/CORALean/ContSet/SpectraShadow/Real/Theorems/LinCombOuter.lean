module

public import CORALean.ContSet.SpectraShadow.Real.Theorems.ConvHullExact
public import CORALean.ContSet.ContSet.Theorems.SetLinCombEqConvexJoin
public import Mathlib.Analysis.Convex.Hull

@[expose] public section

/-!
# The segments between two shadows are inside their convex hull

`Set.linComb` is the set `linComb` has to enclose, `{λ x₁ + (1 - λ) x₂}`; for a shadow `linComb` is
`convHull_`, whose set is the convex hull of the union (`convHull_exact`), so the segments lie
in it.
-/

-- Authors:       Claude Opus 5.5
-- Written:       09-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --
namespace CORALean.Real

open CORALean

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem SpectraShadow.setLinComb_subset_convHull (S₁ S₂ : SpectraShadow (Vec ℝ n)) :
    Set.linComb S₁.construct S₂.construct ⊆ (S₁.convHull_ S₂).construct := by
  rw [SpectraShadow.convHull_exact, CORALean.setLinComb_eq_convexJoin]
  exact convexJoin_subset_convexHull _ _

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
