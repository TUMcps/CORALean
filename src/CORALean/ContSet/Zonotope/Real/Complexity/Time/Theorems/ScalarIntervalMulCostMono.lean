module

public import CORALean.ContSet.Zonotope.Real.Operations.ScalarIntervalMul
public import CORALean.ContSet.Zonotope.Real.Complexity.Time.Theorems.Basic
public import CORALean.ContSet.Zonotope.Real.Complexity.Time.Operations.PlusCost
public import CORALean.ContSet.Zonotope.Real.Complexity.Time.Operations.UnitIntervalMulCost
public import CORALean.ContSet.Zonotope.Real.Complexity.Time.Operations.ScalarIntervalMulCost

@[expose] public section

/-!
# `Zonotope.scalarIntervalMulCost_mono`

Monotone in the generator count.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       10-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

/-- Monotone in the generator count. -/
theorem Zonotope.scalarIntervalMulCost_mono {h h' : ℕ} (n : ℕ) (hh : h ≤ h') :
    Zonotope.scalarIntervalMulCost n h ≤ Zonotope.scalarIntervalMulCost n h' := by
  have := Zonotope.mtimesCost_mono n n hh
  simp only [Zonotope.scalarIntervalMulCost, Cost.le_iff, Cost.ops_add, Cost.ops_smul] at this ⊢
  omega

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
