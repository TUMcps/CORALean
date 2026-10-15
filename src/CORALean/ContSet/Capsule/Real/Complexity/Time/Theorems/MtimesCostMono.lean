module

public import CORALean.ContSet.Capsule.Real.Operations.Mtimes
public import CORALean.Global.Cost
public import CORALean.ContSet.Capsule.Real.Complexity.Time.Operations.MtimesCost

@[expose] public section

/-!
# `Capsule.mtimesCost_mono`

Monotone in both dimensions.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       10-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

/-- Monotone in both dimensions. -/
theorem Capsule.mtimesCost_mono {m m' n n' : ℕ} (hm : m ≤ m') (hn : n ≤ n') :
    Capsule.mtimesCost m n ≤ Capsule.mtimesCost m' n' := by
  have := Nat.mul_le_mul hm hn
  simp only [Capsule.mtimesCost, Cost.le_iff, Cost.ops_add, Cost.ops_smul, Cost.matVec]
  omega

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
