module

public import Mathlib.Data.Real.Basic

@[expose] public section

/-!
# ReLU, and how far it rises above a line

CORA's `nnReLULayer` applies `max(t, 0)`. `reluGapOfSlope` is how far `relu` rises above the
line of slope `λ` through the origin over `[l, u]`: a function of the slope rather than of any
particular choice of it, so a layer that chooses its slope in finite precision measures its own
error against it. Both are what the layer means, over ℝ, and neither is run.

## Inputs
* `t` – real number to transform

## Output
* larger of the argument and zero
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-September-2026
-- Last update:   23-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

noncomputable def relu (t : ℝ) : ℝ := max t 0

/-- How far `relu` rises above the line of slope `lam` through the origin, over `[l, u]`. -/
noncomputable def reluGapOfSlope (lam l u : ℝ) : ℝ := max ((1 - lam) * u) (-(lam * l))

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
