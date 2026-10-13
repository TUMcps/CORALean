module

public import CORALean.ContSet.SpectraShadow.Real.Operations.Or
public import CORALean.ContSet.SpectraShadow.Real.Theorems.ConvHullExact

@[expose] public section

/-!
# `SpectraShadow.or` is exactly the convex hull of the union

`or` is `convHull_`, so `convHull_exact` is its guarantee: equality, not an enclosure.
-/

-- Authors:       Claude Opus 5.5
-- Written:       09-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --
namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem SpectraShadow.or_exact (S₁ S₂ : SpectraShadow (Vec ℝ n)) :
    (S₁.or S₂).construct = convexHull ℝ (S₁.construct ∪ S₂.construct) :=
  S₁.convHull_exact S₂

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
