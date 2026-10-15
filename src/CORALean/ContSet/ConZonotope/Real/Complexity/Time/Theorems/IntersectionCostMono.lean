module

public import CORALean.Global.Cost
public import CORALean.ContSet.ConZonotope.Real.Complexity.Time.Operations.IntersectionCost
public import CORALean.ContSet.ConZonotope.Real.Operations.Intersection
public import CORALean.ContSet.HPolytope.Real.Complexity.Time.Operations.ComapCost
public import CORALean.ContSet.HPolytope.Real.Operations.Comap
public import CORALean.ContSet.HPolytope.Real.Complexity.Time.Operations.IntersectionCost
public import CORALean.ContSet.HPolytope.Real.Operations.Intersection

@[expose] public section

/-!
# `ConZonotope.intersectionCost_mono`

Monotone in the second operand's generator count, so a bound on its size
gives a bound on the cost.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       10-October-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

/-- Monotone in the second operand's generator count, so a bound on its size
gives a bound on the cost. -/
theorem ConZonotope.intersectionCost_mono {h₂ h₂' : ℕ} (n h₁ r₁ re₁ r₂ re₂ : ℕ) (hh : h₂ ≤ h₂') :
    ConZonotope.intersectionCost n h₁ h₂ r₁ re₁ r₂ re₂ ≤
      ConZonotope.intersectionCost n h₁ h₂' r₁ re₁ r₂ re₂ := by
  cost_mono [ConZonotope.intersectionCost, HPolytope.comapCost, HPolytope.intersectionCost]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
