module

public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

@[expose] public section

/-!
# CROWN's backward step through an affine map

A row `μ` on `z = W x + b` is the row `Wᵀ μ` on `x` plus the constant `μ · b`: the step of
CORA.cpp's backward bound through a layer's map (after `crown_activation_step`), exactly.

## Inputs
* `μ` – the row on the map's outputs
* `W` – the map's weights
* `b` – the map's bias
* `x` – the map's input

## Hypotheses
* none

## Conclusion
* the row on the map's outputs is the transposed row on its input plus the row times the bias
-/

-- Authors:       Claude Opus 5.5
-- Written:       23-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {m n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem crown_affine_step (μ : Fin m → ℝ) (W : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (x : Fin n → ℝ) :
    ∑ i, μ i * (∑ j, W i j * x j + b i)
      = ∑ j, (∑ i, μ i * W i j) * x j + ∑ i, μ i * b i := by
  simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  congr 1
  exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => by ring

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
