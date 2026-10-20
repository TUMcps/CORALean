module

public import CORALean.NN.Layers.Definitions.Sigmoid
public import Mathlib.Tactic.Positivity

@[expose] public section

/-!
# The logistic function is monotone

The denominator `1 + e⁻ᵗ` falls as `t` rises, so its reciprocal rises.

## Inputs
* none

## Hypotheses
* none

## Conclusion
* the sigmoid is monotone
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-September-2026
-- Last update:   23-September-2026
-- Reviewed:      15-October-2026 (Tobias Ladner)


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

theorem sigmoid_mono : Monotone sigmoid := by -- --- PROOF ---
  intro a b hab
  have hpb : (0:ℝ) < 1 + Real.exp (-b) := by positivity
  have hexp : Real.exp (-b) ≤ Real.exp (-a) := Real.exp_le_exp.mpr (by linarith)
  show (1 + Real.exp (-a))⁻¹ ≤ (1 + Real.exp (-b))⁻¹
  rw [inv_eq_one_div, inv_eq_one_div]
  exact one_div_le_one_div_of_le hpb (by linarith)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
