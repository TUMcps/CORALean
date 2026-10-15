module

public import CORALean.ContSet.Zonotope.Real.Operations.ReduceCombastel
public import CORALean.ContSet.Zonotope.Real.Complexity.Time.Theorems.Basic
public import CORALean.ContSet.Zonotope.Real.Complexity.Time.Operations.ReduceCombastelCost

@[expose] public section

/-!
# `Zonotope.reduceCombastelCost_mono`

Monotone in the generator count.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       10-October-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

/-- Monotone in the generator count. -/
theorem Zonotope.reduceCombastelCost_mono {h h' : ℕ} (n : ℕ) (hle : h ≤ h') :
    Zonotope.reduceCombastelCost n h ≤ Zonotope.reduceCombastelCost n h' := by
  refine Cost.add_le_add (Cost.add_le_add ?_ ?_) (Zonotope.reduceByCost_mono n hle hle)
  · exact Nat.mul_le_mul_right _ hle
  · exact Cost.sort_mono hle

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
