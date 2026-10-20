module

public import CORALean.ContSet.PolyZonotope.Real.Operations.RelaxDrift
public import CORALean.ContSet.PolyZonotope.Real.Complexity.Time.Theorems.Basic
public import CORALean.ContSet.PolyZonotope.Real.Complexity.Time.Operations.RelaxDriftCost

@[expose] public section

/-!
# `PolyZonotope.relaxDriftCost_mono`

Monotone in the factor count.

## Inputs
* `p` – number of factors
* `p'` – larger factor count

## Hypotheses
* `h` – factor count grows

## Conclusion
* the cost does not decrease
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       10-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

/-- Monotone in the factor count. -/
theorem PolyZonotope.relaxDriftCost_mono {p p' : ℕ} (h : p ≤ p') :
    PolyZonotope.relaxDriftCost p ≤ PolyZonotope.relaxDriftCost p' := by
  have := PolyZonotope.eDriftCost_mono h
  simp only [PolyZonotope.relaxDriftCost, Cost.le_iff, Cost.ops_add, Cost.ops_smul] at this ⊢
  omega

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
