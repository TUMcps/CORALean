module

public import CORALean.Global.Cost
public import CORALean.ContSet.ZonoBundle.Real.Complexity.Time.Operations.PlusCost
public import CORALean.ContSet.ZonoBundle.Real.Operations.Plus
public import CORALean.ContSet.Zonotope.Real.Complexity.Time.Operations.PlusCost
public import CORALean.ContSet.Zonotope.Real.Operations.Plus

@[expose] public section

/-!
# `ZonoBundle.plusCost_mono`

Monotone in both member counts and both generator bounds, so bounds on the operands' sizes
give a bound on the cost.
-/

-- Authors:       Claude Opus 5, Claude Sonnet 5.5
-- Written:       07-September-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

/-- Monotone in both member counts and both generator bounds, so bounds on the operands' sizes
give a bound on the cost. -/
theorem ZonoBundle.plusCost_mono {k₁ k₁' k₂ k₂' h₁ h₁' h₂ h₂' : ℕ} (n : ℕ) (hk₁ : k₁ ≤ k₁')
    (hk₂ : k₂ ≤ k₂') (hh₁ : h₁ ≤ h₁') (hh₂ : h₂ ≤ h₂') :
    ZonoBundle.plusCost n k₁ k₂ h₁ h₂ ≤ ZonoBundle.plusCost n k₁' k₂' h₁' h₂' := by
  cost_mono [ZonoBundle.plusCost, Zonotope.plusCost]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
