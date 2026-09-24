import CORALean.NN.Layers.Theorems.Real.SigmoidNeg
import CORALean.NN.Layers.Theorems.Real.SigmoidPos

/-!
# The logistic function is below one

`sigmoid_pos` read at the mirrored argument.
-/

-- Authors:       Tobias Ladner
-- Written:       03-September-2026
-- Last update:   23-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

theorem sigmoid_lt_one (t : ℝ) : sigmoid t < 1 := by
  have h := sigmoid_pos (-t)
  rw [sigmoid_neg] at h
  linarith

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
