module

public import CORALean.NN.Definitions.ActivationKind
public import CORALean.NN.Layers.Definitions.Relu
public import CORALean.NN.Layers.Definitions.Sigmoid
public import Mathlib.Analysis.Complex.Trigonometric

@[expose] public section

/-!
# The function an activation applies
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The scalar function: `max t 0`, the logistic function, or `tanh`. -/
noncomputable def ActivationKind.fn : ActivationKind → ℝ → ℝ
  | .relu => Real.relu
  | .sigmoid => Real.sigmoid
  | .tanh => Real.tanh

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
