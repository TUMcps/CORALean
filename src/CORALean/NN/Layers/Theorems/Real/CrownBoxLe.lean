module

public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

@[expose] public section

/-!
# CROWN's bound of a row on a box

The last step of CORA.cpp's backward bound: on the box `|x - x₀| ≤ r`, a row `Λ` is at least
`Λ · x₀ - |Λ| · r`, term by term.

## Inputs
* `Λ` – the row on the input
* `x₀` – the box's center
* `r` – the box's radius
* `x` – a point of the box

## Hypotheses
* `hx` – the point lies in the box

## Conclusion
* the row at the center minus its magnitude times the radius is at most the row at the point
-/

-- Authors:       Claude Opus 5.5
-- Written:       23-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem crown_box_le (Λ x₀ r x : Fin n → ℝ) (hx : ∀ j, |x j - x₀ j| ≤ r j) : -- --- CONCL ---
    ∑ j, Λ j * x₀ j - ∑ j, |Λ j| * r j ≤ ∑ j, Λ j * x j := by -- --- PROOF ---
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_le_sum fun j _ => ?_
  have h1 : |Λ j * (x j - x₀ j)| ≤ |Λ j| * r j := by
    rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hx j) (abs_nonneg _)
  have h2 := neg_abs_le (Λ j * (x j - x₀ j))
  nlinarith

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
