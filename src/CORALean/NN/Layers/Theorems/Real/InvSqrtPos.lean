import CORALean.NN.Layers.Definitions.InvSqrt
import Mathlib.Tactic.Positivity

/-!
# The clamped inverse square root is positive

`max x 1` never reaches zero, so neither does its square root.
-/

-- Authors:       Claude Opus 5.5
-- Written:       06-September-2026
-- Last update:   23-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

theorem invSqrt_pos (x : ℝ) : 0 < invSqrt x := by
  unfold invSqrt
  have : (0 : ℝ) < max x 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  positivity

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
