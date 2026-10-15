module

public import CORALean.ContSet.ConPolyZono.Real.Complexity.Time.Operations.DependentCost
public import CORALean.ContSet.ConPolyZono.Real.Operations.QuadMap
public import CORALean.ContSet.PolyZonotope.Real.Complexity.Time.Theorems.Basic
public import CORALean.ContSet.ConPolyZono.Real.Complexity.Time.Operations.QuadMapCost

@[expose] public section

/-!
# `ConPolyZono.quadMapCost_mono`

Monotone in both generator counts, so bounds on the operand's sizes give a
bound on the cost.
-/

-- Authors:       Claude Opus 5.5
-- Written:       23-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

/-- Monotone in both generator counts, so bounds on the operand's sizes give a
bound on the cost. -/
theorem ConPolyZono.quadMapCost_mono {h h' qI q' : ℕ} (m n p : ℕ) (hh : h ≤ h') (hq : qI ≤ q') :
    ConPolyZono.quadMapCost m n p h qI ≤ ConPolyZono.quadMapCost m n p h' q' := by
  -- `dependent` is free, so the comparison is the quadratic map's at the counts it leaves
  have h := PolyZonotope.quadMapDepCost_mono m n (Nat.add_le_add_left hq p) (Nat.add_le_add hh hq)
  simpa [ConPolyZono.quadMapCost, ConPolyZono.dependentCost] using h

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
