module

public import CORALean.ContSet.Zonotope.Real.Complexity.Time.Theorems.Basic
public import CORALean.ContSet.Zonotope.Real.Operations.ReduceGirard
public import CORALean.ContSet.Zonotope.Real.Complexity.Time.Operations.ReduceGirardCost

@[expose] public section

/-!
# `Zonotope.reduceGirardCost_mono`

Monotone in the generator count, so a bound on the operand's size gives a
bound on the cost.
-/

-- Authors:       Claude Opus 5
-- Written:       07-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

/-- Monotone in the generator count, so a bound on the operand's size gives a
bound on the cost. -/
theorem Zonotope.reduceGirardCost_mono {h h' : ℕ} (n : ℕ) (hle : h ≤ h') :
    Zonotope.reduceGirardCost n h ≤ Zonotope.reduceGirardCost n h' := by
  refine Cost.add_le_add (Cost.add_le_add ?_ ?_) (Zonotope.reduceByCost_mono n hle)
  · exact Nat.mul_le_mul_right _ hle
  · exact Cost.sort_mono hle

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
