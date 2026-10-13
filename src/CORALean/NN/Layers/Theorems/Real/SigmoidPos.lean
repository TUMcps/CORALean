module

public import CORALean.NN.Layers.Definitions.Sigmoid
public import Mathlib.Tactic.Positivity

@[expose] public section

/-!
# The logistic function is positive

A reciprocal of `1 + e⁻ᵗ`, which is positive.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-September-2026
-- Last update:   23-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

theorem sigmoid_pos (t : ℝ) : 0 < sigmoid t := by
  rw [sigmoid]
  positivity

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
