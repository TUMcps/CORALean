module

public import CORALean.ContSet.PolyZonotope.Real.Operations.RelaxWidthMulti
public import CORALean.ContSet.PolyZonotope.Real.Complexity.Time.Operations.EDiffCost
public import CORALean.ContSet.PolyZonotope.Real.Complexity.Time.Operations.RelaxWidthMultiCost

@[expose] public section

/-!
# `PolyZonotope.relaxWidthMultiCost_mono`

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
theorem PolyZonotope.relaxWidthMultiCost_mono {p p' : ℕ} (h : p ≤ p') :
    PolyZonotope.relaxWidthMultiCost p ≤ PolyZonotope.relaxWidthMultiCost p' := by
  simp only [PolyZonotope.relaxWidthMultiCost, Cost.le_iff, Cost.ops_add, Cost.ops_smul]
  have := Nat.mul_le_mul_right PolyZonotope.eDiffCost.ops h
  omega

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
