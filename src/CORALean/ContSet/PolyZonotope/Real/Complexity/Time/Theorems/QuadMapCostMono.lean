module

public import CORALean.ContSet.PolyZonotope.Real.Complexity.Time.Operations.DependentCost
public import CORALean.ContSet.PolyZonotope.Real.Complexity.Time.Theorems.Basic
public import CORALean.ContSet.PolyZonotope.Real.Operations.QuadMap
public import CORALean.ContSet.PolyZonotope.Real.Complexity.Time.Operations.QuadMapCost

@[expose] public section

/-!
# `PolyZonotope.quadMapCost_mono`

Monotone in both generator counts, so bounds on the operand's sizes give a
bound on the cost.
-/

-- Authors:       Claude Opus 5
-- Written:       07-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

/-- Monotone in both generator counts, so bounds on the operand's sizes give a
bound on the cost. -/
theorem PolyZonotope.quadMapCost_mono {h h' q q' : ℕ} (m n p : ℕ) (hh : h ≤ h') (hq : q ≤ q') :
    PolyZonotope.quadMapCost m n p h q ≤ PolyZonotope.quadMapCost m n p h' q' := by
  -- `dependent` is free, so the comparison is the dependent map's at the counts it leaves
  have h := PolyZonotope.quadMapDepCost_mono m n (Nat.add_le_add_left hq p) (Nat.add_le_add hh hq)
  simpa [PolyZonotope.quadMapCost, PolyZonotope.dependentCost] using h

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
