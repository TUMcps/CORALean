module

public import CORALean.Global.Cost
public import CORALean.ContSet.ConPolyZono.Real.Complexity.Time.Operations.IntersectionCost
public import CORALean.ContSet.ConPolyZono.Real.Operations.Intersection
public import CORALean.ContSet.ConPolyZono.Real.Complexity.Time.Operations.DependentCost
public import CORALean.ContSet.ConPolyZono.Real.Operations.Dependent
public import CORALean.ContSet.PolyZonotope.Real.Complexity.Time.Operations.DependentCost
public import CORALean.ContSet.PolyZonotope.Real.Operations.Dependent

@[expose] public section

/-!
# `ConPolyZono.intersectionCost_mono`

Monotone in the second operand's dependent-generator count, so a bound on
its size gives a bound on the cost.
-/

-- Authors:       Claude Opus 5.5, Claude Sonnet 5.5
-- Written:       23-September-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

/-- Monotone in the second operand's dependent-generator count, so a bound on
its size gives a bound on the cost. -/
theorem ConPolyZono.intersectionCost_mono {h₂ h₂' : ℕ} (n p₁ h₁ qI₁ m₁ q₁ p₂ qI₂ m₂ q₂ : ℕ)
    (hh : h₂ ≤ h₂') :
    ConPolyZono.intersectionCost n p₁ h₁ qI₁ m₁ q₁ p₂ h₂ qI₂ m₂ q₂ ≤
      ConPolyZono.intersectionCost n p₁ h₁ qI₁ m₁ q₁ p₂ h₂' qI₂ m₂ q₂ := by
  cost_mono [ConPolyZono.intersectionCost, ConPolyZono.dependentCost,
    PolyZonotope.dependentCost]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
