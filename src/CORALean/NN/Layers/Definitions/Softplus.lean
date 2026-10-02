import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Softplus

CORA's `nnSoftPlusLayer` applies `log(1 + exp(β t)) / β` for a sharpness `β`, which is
`1` by default. A specification over ℝ, never run.
-/

-- Authors:       Tobias Ladner
-- Written:       01-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `log (1 + exp (β t)) / β`, a smooth `max t 0` that sharpens as `β` grows. -/
noncomputable def softplus (β t : ℝ) : ℝ := Real.log (1 + Real.exp (β * t)) / β

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
