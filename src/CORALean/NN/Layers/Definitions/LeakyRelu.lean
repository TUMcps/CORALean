import Mathlib.Data.Real.Basic

/-!
# Leaky ReLU

CORA's `nnLeakyReLULayer` applies `max(α t, t)`. For a slope `α ≤ 1` below zero it is
convex, which is what its relaxation reads. A specification over ℝ, never run.
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `max (α t) t`: the identity above zero, slope `α` below it. -/
noncomputable def leakyRelu (α t : ℝ) : ℝ := max (α * t) t

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
