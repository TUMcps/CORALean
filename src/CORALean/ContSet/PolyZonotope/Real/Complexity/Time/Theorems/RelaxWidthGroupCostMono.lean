module

public import CORALean.ContSet.PolyZonotope.Real.Operations.RelaxWidthGroup
public import CORALean.ContSet.PolyZonotope.Real.Complexity.Time.Operations.EDiffCost
public import CORALean.ContSet.PolyZonotope.Real.Complexity.Time.Operations.RelaxWidthGroupCost

@[expose] public section

/-!
# `PolyZonotope.relaxWidthGroupCost_mono`

Monotone in the factor count.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       10-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

/-- Monotone in the factor count. -/
theorem PolyZonotope.relaxWidthGroupCost_mono {p p' : ℕ} (h : p ≤ p') :
    PolyZonotope.relaxWidthGroupCost p ≤ PolyZonotope.relaxWidthGroupCost p' := by
  simp only [PolyZonotope.relaxWidthGroupCost, Cost.le_iff, Cost.ops_add, Cost.ops_smul]
  have := Nat.mul_le_mul_right PolyZonotope.eDiffCost.ops h
  omega

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
