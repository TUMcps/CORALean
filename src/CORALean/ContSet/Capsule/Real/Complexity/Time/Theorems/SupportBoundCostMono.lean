module

public import CORALean.ContSet.Capsule.Real.Operations.SupportBound
public import CORALean.Global.Cost
public import CORALean.ContSet.Capsule.Real.Complexity.Time.Operations.SupportBoundCost

@[expose] public section

/-!
# `Capsule.supportBoundCost_mono`

Monotone in the dimension.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       10-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

/-- Monotone in the dimension. -/
theorem Capsule.supportBoundCost_mono {n n' : ℕ} (cf : Cost) (h : n ≤ n') :
    Capsule.supportBoundCost cf n ≤ Capsule.supportBoundCost cf n' := by
  have := Nat.mul_le_mul_right cf.ops (Nat.add_le_add_right h 2)
  simp only [Capsule.supportBoundCost, Cost.le_iff, Cost.ops_add, Cost.ops_smul]
  omega

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
