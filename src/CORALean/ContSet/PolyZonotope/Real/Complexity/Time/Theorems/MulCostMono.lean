module

public import CORALean.ContSet.PolyZonotope.Real.Complexity.Time.Theorems.BilinCostMono
public import CORALean.ContSet.PolyZonotope.Real.Operations.Mul
public import CORALean.ContSet.PolyZonotope.Real.Complexity.Time.Operations.MulCost

@[expose] public section

/-!
# `PolyZonotope.mulCost_mono`

Monotone in both generator counts, so bounds on the operands' sizes give a
bound on the cost.

## Inputs
* `h₁` – first dependent generator count
* `h₁'` – larger first generator count
* `h₂` – second dependent generator count
* `h₂'` – larger second generator count
* `n` – dimension
* `p` – number of factors

## Hypotheses
* `h1` – first generator count grows
* `h2` – second generator count grows

## Conclusion
* the cost does not decrease
-/

-- Authors:       Claude Opus 5, Claude Sonnet 5.5
-- Written:       07-September-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

/-- Monotone in both generator counts, so bounds on the operands' sizes give a
bound on the cost. -/
theorem PolyZonotope.mulCost_mono {h₁ h₁' h₂ h₂' : ℕ} (n p : ℕ)
    (h1 : h₁ ≤ h₁') (h2 : h₂ ≤ h₂') :
    PolyZonotope.mulCost n p h₁ h₂ ≤ PolyZonotope.mulCost n p h₁' h₂' :=
  PolyZonotope.bilinCost_mono _ le_rfl le_rfl h1 h2

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
