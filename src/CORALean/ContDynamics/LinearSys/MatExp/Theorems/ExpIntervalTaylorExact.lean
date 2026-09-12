import CORALean.ContDynamics.LinearSys.MatExp.Theorems.ExpIntervalTaylorTail
import CORALean.ContDynamics.LinearSys.MatExp.Theorems.ExpIntervalWOuter
import CORALean.ContDynamics.LinearSys.MatExp.Theorems.ExpTaylorTwo
import CORALean.ContSet.Interval.Real.Theorems.MemPoint
import CORALean.ContSet.Interval.Real.Theorems.PlusOuter
import CORALean.ContSet.Interval.Real.Theorems.SmulOuter

/-!
# `expIntervalTaylorExact` encloses the truncation of every member

[1, Thm. 3.2] up to the remainder. The truncation splits at order three —
`sum_Ico_consecutive` — into `expTaylor (t • M) 2`, which `expTaylor_two` turns
into `I + W(t)`, and the orders past it. The first piece is enclosed exactly by
`expIntervalW`, the second by ordinary interval arithmetic.

`2 ≤ κ` is what makes the split legitimate; below it the definition's tail is
empty and this would be claiming more orders than the truncation has.

## References

* [1] M. Althoff. "Reachability Analysis and its Application to the Safety
      Assessment of Autonomous Cars". PhD thesis, TU München, 2010.
-/

-- Authors:       Tobias Ladner
-- Written:       12-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- Every member's Taylor truncation lies in the sharper interval truncation. -/
theorem MatExp.expTaylor_mem_expIntervalTaylorExact (A : Interval (Mat ℝ n n)) (t : ℝ)
    {M : Mat ℝ n n} (hM : M ∈ A.construct) {κ : ℕ} (hκ : 2 ≤ κ) :
    MatExp.expTaylor (t • M) κ
      ∈ (MatExp.expIntervalTaylorExact A t κ).construct := by -- --- PROOF ---
  -- the truncation splits at order three, which is where the exact part stops
  have hsplit : MatExp.expTaylor (t • M) κ
      = MatExp.expTaylor (t • M) 2
        + ∑ i ∈ Finset.Ico 3 (κ + 1), ((Nat.factorial i : ℝ)⁻¹) • (t • M) ^ i := by
    rw [MatExp.expTaylor, MatExp.expTaylor, Finset.range_eq_Ico, Finset.range_eq_Ico]
    exact (Finset.sum_Ico_consecutive _ (by omega) (by omega)).symm
  rw [hsplit, MatExp.expTaylor_two, MatExp.expIntervalTaylorExact]
  exact Interval.plus_outer _ _ (Set.add_mem_add
    (Interval.plus_outer _ _ (Set.add_mem_add (Interval.mem_point 1)
      (MatExp.expW_mem_expIntervalW A t hM)))
    (MatExp.taylorTail_mem_expIntervalTaylorTail _ (Interval.smul_outer t A hM) κ))

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
