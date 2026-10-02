import CORALean.NN.Layers.Definitions.InvSqrt
import Mathlib.Analysis.Normed.Order.Lattice

/-!
# The clamped inverse square root is continuous

Everywhere, the clamp included: `max x 1` never reaches zero, so the square root it feeds
never does either.
-/

-- Authors:       Tobias Ladner
-- Written:       06-September-2026
-- Last update:   23-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

theorem continuous_invSqrt : Continuous invSqrt := by
  have h : Continuous fun x : ℝ => Real.sqrt (max x 1) :=
    Real.continuous_sqrt.comp (continuous_id.max continuous_const)
  refine h.inv₀ fun x => ne_of_gt (Real.sqrt_pos.mpr ?_)
  exact lt_of_lt_of_le one_pos (le_max_right _ _)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
