module

public import CORALean.ContSet.Zonotope.Real.Operations.MtimesIntervalMat
public import CORALean.Global.Cost
public import CORALean.ContSet.Zonotope.Real.Complexity.Time.Operations.MtimesIntervalMatCost

@[expose] public section

/-!
# `Zonotope.mtimesIntervalMatCost_mono`

Monotone in the generator count, so a bound on the operand's size gives a
bound on the cost.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       10-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

/-- Monotone in the generator count, so a bound on the operand's size gives a
bound on the cost. -/
theorem Zonotope.mtimesIntervalMatCost_mono {h h' : ℕ} (m n : ℕ) (hh : h ≤ h') :
    Zonotope.mtimesIntervalMatCost m n h ≤
      Zonotope.mtimesIntervalMatCost m n h' := by -- --- PROOF ---
  show 6 * (m * n) + n * (2 * h + 1) + (h + 1) * (2 * (m * n)) ≤
    6 * (m * n) + n * (2 * h' + 1) + (h' + 1) * (2 * (m * n))
  exact Nat.add_le_add
    (Nat.add_le_add_left (Nat.mul_le_mul_left n (Nat.succ_le_succ (Nat.mul_le_mul_left 2 hh))) _)
    (Nat.mul_le_mul_right _ (Nat.succ_le_succ hh))

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
