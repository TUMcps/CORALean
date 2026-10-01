import CORALean.Global.Mathlib

/-!
# Leaky ReLU

CORA's `nnLeakyReLULayer` applies `max(α t, t)`. For a slope `α ≤ 1` below zero it is
convex, which is what its relaxation reads. A specification over ℝ, never run.
-/

-- Authors:       Tobias Ladner
-- Written:       01-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `max (α t) t`: the identity above zero, slope `α` below it. -/
noncomputable def leakyRelu (α t : ℝ) : ℝ := max (α * t) t

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
