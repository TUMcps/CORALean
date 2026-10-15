module

public import CORALean.ContSet.PolyZonotope.Real.Operations.RelaxExpMid
public import CORALean.ContSet.PolyZonotope.Real.Complexity.Time.Theorems.RelaxDriftCostMono
public import CORALean.ContSet.PolyZonotope.Real.Complexity.Time.Operations.RelaxExpMidCost

@[expose] public section

/-!
# `PolyZonotope.relaxExpMidCost_mono`

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
theorem PolyZonotope.relaxExpMidCost_mono {p p' : ℕ} (n : ℕ) (h : p ≤ p') :
    PolyZonotope.relaxExpMidCost n p ≤ PolyZonotope.relaxExpMidCost n p' := by
  have := PolyZonotope.relaxDriftCost_mono h
  simp only [PolyZonotope.relaxExpMidCost, Cost.le_iff, Cost.ops_add, Cost.ops_smul] at this ⊢
  omega

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
