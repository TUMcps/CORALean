import CORALean.ContSet.Interval.Real.Interval
/-!
# `s^i - s ≤ 0` on `[0,1]`

The half of the correction term's range that needs no stationary-point
argument: `s ^ i ≤ s ^ 1` already gives it directly, which is also why this
direction needs `s ≤ 1` where `corrCoeff_le_sub`'s lower bound does not.
-/

-- Authors:       Tobias Ladner
-- Written:       18-August-2026
-- Last update:   ---
-- Last revision: ---


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
