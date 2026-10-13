import CORALean.NN.Layers.Definitions.InvSqrt

/-!
# The clamped inverse square root above the clamp

The agreement with the unclamped function above the clamp point — the whole reason `invSqrt`
exists rather than `(Real.sqrt ·)⁻¹` directly.
-/

-- Authors:       Claude Opus 5.5
-- Written:       06-September-2026
-- Last update:   23-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

theorem invSqrt_eq_of_one_le {x : ℝ} (hx : 1 ≤ x) : invSqrt x = (Real.sqrt x)⁻¹ := by
  unfold invSqrt
  rw [max_eq_left hx]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
