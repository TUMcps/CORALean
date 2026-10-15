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

-- Authors:       Claude Opus 5, Claude Sonnet 5.5
-- Written:       07-September-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

/-- Monotone in both generator counts, so bounds on the operand's sizes give a
bound on the cost. -/
theorem PolyZonotope.quadMapCost_mono {h h' q q' : ℕ} (m n p : ℕ) (hh : h ≤ h') (hq : q ≤ q') :
    PolyZonotope.quadMapCost m n p h q ≤ PolyZonotope.quadMapCost m n p h' q' := by
  -- `dependent` writes the result; the comparison is the map's at the counts it leaves
  have a := PolyZonotope.quadMapDepCost_mono m n (Nat.add_le_add_left hq p) (Nat.add_le_add hh hq)
  simp only [PolyZonotope.quadMapCost, PolyZonotope.dependentCost, Cost.le_iff, Cost.ops_add] at a ⊢
  gcongr

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
