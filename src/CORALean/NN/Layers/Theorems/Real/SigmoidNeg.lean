module

public import CORALean.NN.Layers.Definitions.Sigmoid
public import Mathlib.Tactic.Positivity

@[expose] public section

/-!
# Mirroring the argument complements the logistic function

`σ (-t) = 1 - σ t`, which is what makes the derivative a product of two sigmoids.

## Inputs
* `t` – real number

## Hypotheses
* none

## Conclusion
* the sigmoid of the negated number is one minus the sigmoid
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-September-2026
-- Last update:   23-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

theorem sigmoid_neg (t : ℝ) : sigmoid (-t) = 1 - sigmoid t := by -- --- PROOF ---
  have hden : (1:ℝ) + Real.exp t ≠ 0 := by positivity
  have hden' : (1:ℝ) + Real.exp (-t) ≠ 0 := by positivity
  rw [sigmoid, sigmoid, neg_neg, Real.exp_neg]
  field_simp
  ring

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
