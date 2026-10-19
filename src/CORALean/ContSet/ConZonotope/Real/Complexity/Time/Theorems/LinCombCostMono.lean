module

public import CORALean.ContSet.ConZonotope.Real.Operations.LinComb
public import CORALean.ContSet.HPolytope.Real.Complexity.Time.Theorems.Basic
public import CORALean.Global.Cost
public import CORALean.ContSet.ConZonotope.Real.Complexity.Time.Operations.LinCombCost

@[expose] public section

/-!
# `ConZonotope.linCombCost_mono`

Monotone in the operands' sizes, so a bound on them gives a bound on the cost.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       10-October-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

/-- Monotone in the operands' sizes, so a bound on them gives a bound on the cost. -/
theorem ConZonotope.linCombCost_mono {n h₁ h₁' m₁ m₁' me₁ me₁' h₂ h₂' m₂ m₂' me₂ me₂' : ℕ}
    (hh₁ : h₁ ≤ h₁') (hm₁ : m₁ ≤ m₁') (hme₁ : me₁ ≤ me₁')
    (hh₂ : h₂ ≤ h₂') (hm₂ : m₂ ≤ m₂') (hme₂ : me₂ ≤ me₂') : -- --- CONCL ---
    ConZonotope.linCombCost n h₁ m₁ me₁ h₂ m₂ me₂ ≤
      ConZonotope.linCombCost n h₁' m₁' me₁' h₂' m₂' me₂' := by -- --- PROOF ---
  cost_mono [ConZonotope.linCombCost, HPolytope.comapCost, HPolytope.halfScaledCost,
    HPolytope.intersectionCost]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
