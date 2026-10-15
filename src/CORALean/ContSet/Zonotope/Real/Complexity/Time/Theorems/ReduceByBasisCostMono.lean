module

public import CORALean.ContSet.Zonotope.Real.Operations.ReduceByBasis
public import CORALean.ContSet.Zonotope.Real.Complexity.Time.Operations.ReduceByCost
public import CORALean.ContSet.Zonotope.Real.Complexity.Time.Operations.ReduceByBasisCost

@[expose] public section

/-!
# `Zonotope.reduceByBasisCost_mono`

Monotone in the absorbed count.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       10-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

/-- Monotone in the absorbed count. -/
theorem Zonotope.reduceByBasisCost_mono {r r' : ℕ} (n : ℕ) (inv : Cost) (hr : r ≤ r') :
    Zonotope.reduceByBasisCost n r inv ≤ Zonotope.reduceByBasisCost n r' inv := by
  have := Nat.mul_le_mul_right (2 * (n * n)) hr
  have := Nat.mul_le_mul_left n hr
  simp only [Zonotope.reduceByBasisCost, Cost.le_iff, Cost.ops_add, Cost.ops_smul, Cost.matVec]
  omega

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
