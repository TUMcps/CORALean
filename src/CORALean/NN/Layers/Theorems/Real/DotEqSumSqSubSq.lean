module

public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

@[expose] public section

/-!
# A dot product is a sum of differences of squares

CORA.cpp lowers a product `∑ₜ aₜ bₜ` of two vectors (a MatMul entry) to scaled gathers of the half
sums and half differences into one square layer and a 1 x 1 convolution of `+1, -1`:
`mul_eq_sq_sub_sq` term by term. The identity is exact.

## Inputs
* `n` – length
* `a` – first vector
* `b` – second vector

## Hypotheses
* none

## Conclusion
* the dot product is the sum of the squared half sums minus the squared half differences
-/

-- Authors:       Claude Opus 5.5
-- Written:       23-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

theorem dot_eq_sum_sq_sub_sq {n : ℕ} (a b : Fin n → ℝ) :
    ∑ t, a t * b t = ∑ t, (((a t + b t) / 2) ^ 2 - ((a t - b t) / 2) ^ 2) := by
  exact Finset.sum_congr rfl fun t _ => by ring


end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
