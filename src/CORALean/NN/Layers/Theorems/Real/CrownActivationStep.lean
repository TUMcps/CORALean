module

public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

@[expose] public section

/-!
# CROWN's backward step through an activation

CROWN's step: a row `Λ` on the outputs `h = σ(z)` of a layer, with linear bounds
`s_l z + c_l ≤ σ(z) ≤ s_u z + c_u` at every neuron, is at least the row
`μ = Λ⁺ s_l + Λ⁻ s_u` on the inputs `z` plus `Λ⁺ c_l + Λ⁻ c_u`: a positive weight takes the
lower bound, a negative one the upper. With `crown_affine_step` through the layer's map and
`crown_box_le` at the input box, it is CORA.cpp's backward bound (`backward_bound_sound` is the
induction over the layers).

## Inputs
* `Λ` – the row on the outputs
* `sl` – the lower slopes
* `cl` – the lower offsets
* `su` – the upper slopes
* `cu` – the upper offsets
* `z` – the inputs of the activation
* `h` – the outputs of the activation

## Hypotheses
* `hlo` – the lower bounds hold at the point
* `hhi` – the upper bounds hold at the point

## Conclusion
* the row on the inputs plus the constant is at most the row on the outputs
-/

-- Authors:       Claude Opus 5.5
-- Written:       23-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem crown_activation_step (Λ sl cl su cu z h : Fin m → ℝ)
    (hlo : ∀ i, sl i * z i + cl i ≤ h i) (hhi : ∀ i, h i ≤ su i * z i + cu i) : -- --- CONCL ---
    ∑ i, (max (Λ i) 0 * sl i + min (Λ i) 0 * su i) * z i
        + ∑ i, (max (Λ i) 0 * cl i + min (Λ i) 0 * cu i) ≤ ∑ i, Λ i * h i := by -- --- PROOF ---
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun i _ => ?_
  -- `Λ = Λ⁺ + Λ⁻`, each part on the bound of its sign
  have hsplit : Λ i * h i = max (Λ i) 0 * h i + min (Λ i) 0 * h i := by
    rw [← add_mul, max_add_min, add_zero]
  have hp : 0 ≤ max (Λ i) 0 := le_max_right _ _
  have hn : min (Λ i) 0 ≤ 0 := min_le_right _ _
  have h1 := mul_le_mul_of_nonneg_left (hlo i) hp
  have h2 := mul_le_mul_of_nonpos_left (hhi i) hn
  rw [hsplit]
  nlinarith

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
