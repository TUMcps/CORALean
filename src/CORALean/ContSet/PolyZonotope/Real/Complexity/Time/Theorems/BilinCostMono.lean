module

public import CORALean.ContSet.PolyZonotope.Real.Operations.Bilin
public import CORALean.Global.Cost
public import CORALean.ContSet.PolyZonotope.Real.Complexity.Time.Operations.BilinCost

@[expose] public section

/-!
# `PolyZonotope.bilinCost_mono`

Monotone in the factor count and in both generator counts, so bounds on the
operands' sizes give a bound on the cost.

## Inputs
* `nOut` – output dimension
* `nOut'` – larger output dimension
* `p` – number of factors
* `p'` – larger factor count
* `h₁` – first dependent generator count
* `h₁'` – larger first generator count
* `h₂` – second dependent generator count
* `h₂'` – larger second generator count
* `cf` – cost of one bilinear form evaluation

## Hypotheses
* `hn` – output dimension grows
* `hp` – factor count grows
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

/-- Monotone in the output dimension, the factor count and both generator counts, so bounds on
the operands' sizes give a bound on the cost. -/
theorem PolyZonotope.bilinCost_mono {nOut nOut' p p' h₁ h₁' h₂ h₂' : ℕ} (cf : Cost)
    (hn : nOut ≤ nOut') (hp : p ≤ p') (h1 : h₁ ≤ h₁') (h2 : h₂ ≤ h₂') :
    PolyZonotope.bilinCost cf nOut p h₁ h₂ ≤ PolyZonotope.bilinCost cf nOut' p' h₁' h₂' := by
  cost_mono [PolyZonotope.bilinCost]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
