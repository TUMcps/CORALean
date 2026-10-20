module

public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.CorrCoeffBound

@[expose] public section

/-!
# The interpolation coefficient never leaves the unit interval

`corrCoeff i` is `a^i - a` at the stationary point `a = corrCritical i`, which sits in `(0, 1]`
for every `i ≥ 2`. So the coefficient is at most `0` (`corrCoeff_le_sub` at `s = 0`) and at least
`-a ≥ -1`. It buys an entrywise bound on `correctionMatrix` that mentions only `r` and `‖A‖`:
each order contributes at most `(r‖A‖)^i / i!`, so the finite part is under
`e^{r‖A‖} - 1 - r‖A‖` and the correction vanishes with the step. The sign is not symmetric, but
a bound on the absolute value is what an interval's two endpoints both need.

## Inputs
* none

## Hypotheses
* `hi` – order at least two

## Conclusion
* the correction coefficient is at most one in magnitude
-/

-- Authors:       Claude Opus 5
-- Written:       08-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {i : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- The coefficient of the interpolation error, in `[-1, 0]` and so bounded by
`1` either way. -/
theorem MatExp.abs_corrCoeff_le_one (hi : 2 ≤ i) :
    |MatExp.corrCoeff i| ≤ 1 := by -- --- PROOF ---
  have hi2 : (2:ℝ) ≤ (i : ℝ) := by exact_mod_cast hi
  have hipos : (0:ℝ) < (i : ℝ) := by linarith
  have hi1 : (1:ℝ) ≤ (i : ℝ) := by linarith
  have hapos : 0 < MatExp.corrCritical i := Real.rpow_pos_of_pos hipos _
  -- the stationary point is at most one, its exponent being nonpositive
  have hale : MatExp.corrCritical i ≤ 1 := by
    rw [MatExp.corrCritical]
    refine Real.rpow_le_one_of_one_le_of_nonpos hi1 ?_
    exact div_nonpos_of_nonpos_of_nonneg (by norm_num) (by linarith)
  have hupper : MatExp.corrCoeff i ≤ 0 := by
    have h := MatExp.corrCoeff_le_sub hi (le_refl (0:ℝ))
    rwa [zero_pow (by omega : i ≠ 0), sub_zero] at h
  have hlower : -1 ≤ MatExp.corrCoeff i := by
    rw [MatExp.corrCoeff]
    have hpow : 0 ≤ MatExp.corrCritical i ^ i := pow_nonneg hapos.le i
    linarith
  rw [abs_le]
  exact ⟨hlower, hupper.trans zero_le_one⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
