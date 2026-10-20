module

public import Mathlib.Analysis.SpecialFunctions.Exponential

@[expose] public section

/-!
# The exponential series from its second order on, as a sum

`e^x - 1 - x = ∑ᵢ x^{i+2}/(i+2)!` for every real `x`, the whole tail rather than
`sum_expTail2_le`'s partial sums: a series compared with it termwise is then bounded
by the closed form directly, with no limit to take afterwards.

## Inputs
* `x` – real variable

## Hypotheses
* none

## Conclusion
* the exponential minus one minus the variable is the sum of the series from order two
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

/-- `e^x` with its constant and linear orders taken off, as the sum of the rest. -/
theorem hasSum_exp_tail2 (x : ℝ) :
    HasSum (fun i : ℕ => x ^ (i + 2) / ((i + 2).factorial : ℝ)) (Real.exp x - 1 - x) := by
  have h : HasSum (fun i : ℕ => x ^ i / (i.factorial : ℝ)) (Real.exp x) := by
    rw [Real.exp_eq_exp_ℝ]; exact NormedSpace.expSeries_div_hasSum_exp x
  rw [sub_sub]
  simpa [Finset.sum_range_succ] using (hasSum_nat_add_iff' 2).mpr h

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
