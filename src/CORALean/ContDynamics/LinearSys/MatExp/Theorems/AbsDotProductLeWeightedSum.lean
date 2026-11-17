module

public import CORALean.Global.Tensor
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Real.Basic
public import Mathlib.LinearAlgebra.Matrix.DotProduct

@[expose] public section

/-!
# A dot product against a weighted bound

If every `|yᵢ|` is at most `β sᵢ`, then `|e ⬝ y| ≤ (Σᵢ |eᵢ| sᵢ) β`: the weighted `l¹` norm of `e`
is dual to the scaled sup norm of `y`. It turns a bound on the error of a propagated direction into
a bound on the error of a support value.

## Inputs
* `e` – vector of the errors
* `y` – vector it is applied to
* `s` – weights
* `β` – bound

## Hypotheses
* `hy` – every `|yᵢ|` is at most `β sᵢ`

## Conclusion
* the dot product is at most the weighted sum of `|e|` times `β` in magnitude
-/

-- Authors:       Claude Opus 5.5
-- Written:       17-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem MatExp.abs_dotProduct_le_weightedSum (e y s : Vec ℝ n) {β : ℝ}
    (hy : ∀ i, |y i| ≤ β * s i) :
    |e ⬝ᵥ y| ≤ (∑ i, |e i| * s i) * β := by
  rw [Finset.sum_mul]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum fun i _ => ?_)
  rw [abs_mul, mul_assoc, mul_comm (s i) β]
  exact mul_le_mul_of_nonneg_left (hy i) (abs_nonneg _)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
