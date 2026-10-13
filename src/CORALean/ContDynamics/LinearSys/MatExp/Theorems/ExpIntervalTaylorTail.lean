import CORALean.ContDynamics.LinearSys.MatExp.Operations.ExpIntervalTaylorTail
import CORALean.ContSet.Interval.Real.Theorems.MatPowOuter
import CORALean.ContSet.Interval.Real.Theorems.MemPoint
import CORALean.ContSet.Interval.Real.Theorems.PlusOuter
import CORALean.ContSet.Interval.Real.Theorems.SmulOuter
import Mathlib.Algebra.BigOperators.Intervals

/-!
# `expIntervalTaylorTail` encloses orders three and up of every member

The same induction as `expTaylor_mem_expIntervalTaylor`, over `Finset.Ico 3`
instead of `Finset.range`: `sum_Ico_succ_top` peels the top order off the left
and `plus_outer`/`smul_outer`/`matPow_outer` cover it, the recursion matching
term for term.

Three base cases rather than one, because the definition has three: below order
three the range is empty and the tail is `point 0`.
-/

-- Authors:       Claude Opus 5
-- Written:       12-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- Orders `3 … κ` of any member's Taylor sum lie in the interval tail. -/
theorem MatExp.taylorTail_mem_expIntervalTaylorTail (B : Interval (Mat ℝ n n))
    {N : Mat ℝ n n} (hN : N ∈ B.construct) (κ : ℕ) :
    (∑ i ∈ Finset.Ico 3 (κ + 1), ((Nat.factorial i : ℝ)⁻¹) • N ^ i)
      ∈ (MatExp.expIntervalTaylorTail B κ).construct := by -- --- PROOF ---
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
        add_comm (∑ i ∈ Finset.Ico 3 (m + 2 + 1), ((Nat.factorial i : ℝ)⁻¹) • N ^ i)
          (((Nat.factorial (m + 2 + 1) : ℝ))⁻¹ • N ^ (m + 2 + 1))]
      exact Interval.plus_outer _ _ (Set.add_mem_add
        (Interval.smul_outer _ _ (Interval.matPow_outer B hN _)) ih)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
