import CORALean.ContDynamics.LinearSys.MatExp.Operations.InputIntervalTaylorTail
import CORALean.ContSet.Interval.Real.Theorems.MatPowOuter
import CORALean.ContSet.Interval.Real.Theorems.MemPoint
import CORALean.ContSet.Interval.Real.Theorems.PlusOuter
import CORALean.ContSet.Interval.Real.Theorems.SmulOuter
import Mathlib.Algebra.BigOperators.Intervals

/-!
# `inputIntervalTaylorTail` encloses the input orders three and up of every member

`taylorTail_mem_expIntervalTaylorTail`'s induction at the input's coefficient `r/(i+1)!`:
`sum_Ico_succ_top` peels the top order off and `plus_outer`/`smul_outer`/`matPow_outer`
cover it.
-/

-- Authors:       Tobias Ladner
-- Written:       12-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- Orders `3 … κ` of any member's input series lie in the interval tail. -/
theorem MatExp.inputTail_mem_inputIntervalTaylorTail (B : Interval (Mat ℝ n n)) (r : ℝ)
    {N : Mat ℝ n n} (hN : N ∈ B.construct) (κ : ℕ) :
    (∑ i ∈ Finset.Ico 3 (κ + 1), (r / (Nat.factorial (i + 1) : ℝ)) • N ^ i)
      ∈ (MatExp.inputIntervalTaylorTail B r κ).construct := by -- --- PROOF ---
  induction κ with
  | zero =>
    rw [Finset.Ico_eq_empty (by omega), Finset.sum_empty]
    exact Interval.mem_point 0
  | succ k ih =>
    -- below order three the range is empty; from three on the top order peels off
    match k, ih with
    | 0, _ =>
      rw [Finset.Ico_eq_empty (by omega), Finset.sum_empty]
      exact Interval.mem_point 0
    | 1, _ =>
      rw [Finset.Ico_eq_empty (by omega), Finset.sum_empty]
      exact Interval.mem_point 0
    | m + 2, ih =>
      rw [Finset.sum_Ico_succ_top (by omega),
        add_comm (∑ i ∈ Finset.Ico 3 (m + 2 + 1), (r / (Nat.factorial (i + 1) : ℝ)) • N ^ i)
          ((r / (Nat.factorial (m + 2 + 1 + 1) : ℝ)) • N ^ (m + 2 + 1))]
      exact Interval.plus_outer _ _ (Set.add_mem_add
        (Interval.smul_outer _ _ (Interval.matPow_outer B hN _)) ih)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
