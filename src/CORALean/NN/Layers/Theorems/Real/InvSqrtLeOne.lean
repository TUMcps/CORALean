import CORALean.NN.Layers.Definitions.InvSqrt

/-!
# The clamped inverse square root is at most one

The clamp puts the square root at `1` or above.
-/

-- Authors:       Tobias Ladner
-- Written:       06-September-2026
-- Last update:   23-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

theorem invSqrt_le_one (x : ℝ) : invSqrt x ≤ 1 := by -- --- PROOF ---
  unfold invSqrt
  rw [inv_le_one_iff₀]
  right
  rw [Real.le_sqrt' (by norm_num)]
  simp

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
