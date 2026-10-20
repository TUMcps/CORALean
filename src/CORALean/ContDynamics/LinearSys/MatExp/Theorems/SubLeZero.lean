module

public import CORALean.ContSet.Interval.Real.Interval

@[expose] public section

/-!
# `s^i - s ≤ 0` on `[0,1]`

The half of the correction term's range that needs no stationary-point
argument: `s ^ i ≤ s ^ 1` already gives it directly, which is also why this
direction needs `s ≤ 1` where `corrCoeff_le_sub`'s lower bound does not.

## Inputs
* `s` – evaluation point

## Hypotheses
* `hi` – order at least one
* `hs0` – point nonnegative
* `hs1` – point at most one

## Conclusion
* the interpolation polynomial is nonpositive on the unit interval
-/

-- Authors:       Claude Opus 5
-- Written:       18-August-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {i : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem MatExp.sub_le_zero (hi : 1 ≤ i) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    s ^ i - s ≤ 0 := by
  have : s ^ i ≤ s ^ 1 := pow_le_pow_of_le_one hs0 hs1 hi
  simpa using this

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
