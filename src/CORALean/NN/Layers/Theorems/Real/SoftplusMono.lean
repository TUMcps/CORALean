import CORALean.NN.Layers.Definitions.Softplus
import Mathlib.Tactic.Positivity

/-!
# Softplus is monotone

For a positive sharpness: `exp`, `1 + ·`, `log` and division by `β` are all monotone there.
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

theorem softplus_mono {β : ℝ} (hβ : 0 < β) : Monotone (softplus β) := by -- --- PROOF ---
  intro a b hab
  have hpos : ∀ t, 0 < 1 + Real.exp (β * t) := fun t => by positivity
  unfold softplus
  refine div_le_div_of_nonneg_right (Real.log_le_log (hpos a) ?_) hβ.le
  have : Real.exp (β * a) ≤ Real.exp (β * b) := Real.exp_le_exp.mpr (by nlinarith)
  linarith

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
