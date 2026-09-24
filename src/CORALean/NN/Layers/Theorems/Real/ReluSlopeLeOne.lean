import CORALean.Global.Float.Instances.Real.Instances
import CORALean.NN.Layers.Operations.ReluSlope

/-!
# The default ReLU slope is at most one at ℝ

ℝ-only, for the reason `reluSlope_nonneg` is: the secant `u / (u - l)` is at most `1` only once
the exact order has put `l` below zero and `u` above it.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   23-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

/-- The same branches upward, which together put the slope in `[0,1]`. -/
theorem reluSlope_le_one (l u : ℝ) : reluSlope l u ≤ 1 := by -- --- PROOF ---
  show (if decide (u ≤ 0) = true then (0 : ℝ)
    else if decide (0 ≤ l) = true then 1 else u / (u + -l)) ≤ 1
  split
  · exact zero_le_one
  · rename_i hu
    split
    · exact le_rfl
    · rename_i hl
      replace hu : 0 < u := not_le.mp (by simpa using hu)
      replace hl : l < 0 := not_le.mp (by simpa using hl)
      rw [div_le_one (by linarith)]
      linarith

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
