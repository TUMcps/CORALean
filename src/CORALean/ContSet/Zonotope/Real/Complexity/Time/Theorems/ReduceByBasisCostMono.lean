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
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

/-- Monotone in the kept and the absorbed count. -/
theorem Zonotope.reduceByBasisCost_mono {q q' r r' : ℕ} (n : ℕ) (inv : Cost) (hq : q ≤ q')
    (hr : r ≤ r') :
    Zonotope.reduceByBasisCost n q r inv ≤
      Zonotope.reduceByBasisCost n q' r' inv := by -- --- PROOF ---
  have := Nat.mul_le_mul_right (2 * n * n) hr
  have := Nat.mul_le_mul_left n hr
  have := Nat.mul_le_mul_left n hq
  simp only [Zonotope.reduceByBasisCost, Cost.le_iff, Cost.ops_add, Cost.ops_smul, Cost.matVec]
  nlinarith

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
