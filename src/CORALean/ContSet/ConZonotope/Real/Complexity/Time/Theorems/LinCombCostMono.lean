module

public import CORALean.ContSet.ConZonotope.Real.Operations.LinComb
public import CORALean.ContSet.HPolytope.Real.Complexity.Time.Theorems.Basic
public import CORALean.Global.Cost
public import CORALean.ContSet.ConZonotope.Real.Complexity.Time.Operations.LinCombCost

@[expose] public section

/-!
# `ConZonotope.linCombCost_mono`

Monotone in the operands' sizes, so a bound on them gives a bound on the cost.

## Inputs
* `n` – dimension
* `h₁` – generators of the first set
* `h₁'` – larger generator count of the first set
* `m₁` – inequalities of the first set
* `m₁'` – larger inequality count of the first set
* `me₁` – equalities of the first set
* `me₁'` – larger equality count of the first set
* `h₂` – generators of the second set
* `h₂'` – larger generator count of the second set
* `m₂` – inequalities of the second set
* `m₂'` – larger inequality count of the second set
* `me₂` – equalities of the second set
* `me₂'` – larger equality count of the second set

## Hypotheses
* `hh₁` – `h₁ ≤ h₁'`
* `hm₁` – `m₁ ≤ m₁'`
* `hme₁` – `me₁ ≤ me₁'`
* `hh₂` – `h₂ ≤ h₂'`
* `hm₂` – `m₂ ≤ m₂'`
* `hme₂` – `me₂ ≤ me₂'`

## Conclusion
* the convex hull cost is monotone in all sizes
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
