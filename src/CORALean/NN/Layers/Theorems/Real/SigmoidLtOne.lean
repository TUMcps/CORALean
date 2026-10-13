module

public import CORALean.NN.Layers.Theorems.Real.SigmoidNeg
public import CORALean.NN.Layers.Theorems.Real.SigmoidPos

@[expose] public section

/-!
# The logistic function is below one

`sigmoid_pos` read at the mirrored argument.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-September-2026
-- Last update:   23-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

theorem sigmoid_lt_one (t : ℝ) : sigmoid t < 1 := by
  have h := sigmoid_pos (-t)
  rw [sigmoid_neg] at h
  linarith

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
