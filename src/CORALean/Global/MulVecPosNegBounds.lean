module

public import CORALean.Global.Tensor
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Real.Basic
public import Mathlib.Tactic.Linarith

@[expose] public section

/-!
# A matrix image of a box, by the positive and negative parts

[1, Lemma 2]: for `x̲ ≤ x ≤ x̅` and any matrix `A`, `A⁺x̲ - A⁻x̅ ≤ A x ≤ A⁺x̅ - A⁻x̲`, with
`A⁺ = max{0, A}` and `A⁻ = A⁺ - A`, elementwise; the inequality the interval observers of [1]
propagate their bounds with. Each term `A_{ij} x_j = A⁺_{ij} x_j - A⁻_{ij} x_j`, both parts
nonnegative.

## Inputs
* `A` – matrix
* `x` – vector
* `xl` – lower bound of the vector
* `xu` – upper bound of the vector
* `i` – row index

## Hypotheses
* `h` – every entry of the vector lies within its bounds

## Conclusion
* the row's image lies between the bounds from the positive and negative parts

## References

* [1] [W. Tang, Z. Wang, Y. Wang, T. Raïssi and Y. Shen. "Interval estimation methods for
      discrete-time linear time-invariant systems". IEEE Transactions on Automatic Control,
      2019.](../../../references/2019/tang-tac-interval-estimation.md)
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix

variable {m n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem mulVec_posNeg_bounds (A : Mat ℝ m n) (x xl xu : Vec ℝ n)
    (h : ∀ j, xl j ≤ x j ∧ x j ≤ xu j) (i : Fin m) : -- --- CONCL ---
    (A.map (max 0) *ᵥ xl - (A.map (max 0) - A) *ᵥ xu) i ≤ (A *ᵥ x) i ∧
      (A *ᵥ x) i ≤ (A.map (max 0) *ᵥ xu - (A.map (max 0) - A) *ᵥ xl) i := by -- --- PROOF ---
  simp only [Pi.sub_apply, mulVec, dotProduct, map_apply, Matrix.sub_apply,
    ← Finset.sum_sub_distrib]
  -- each term, through `A⁺ ≥ 0` and `A⁻ = A⁺ - A ≥ 0`
  have hp : ∀ j, 0 ≤ max 0 (A i j) := fun j => le_max_left _ _
  have hn : ∀ j, 0 ≤ max 0 (A i j) - A i j := fun j => sub_nonneg.mpr (le_max_right _ _)
  constructor
  · refine Finset.sum_le_sum fun j _ => ?_
    nlinarith [mul_nonneg (hp j) (sub_nonneg.mpr (h j).1),
      mul_nonneg (hn j) (sub_nonneg.mpr (h j).2)]
  · refine Finset.sum_le_sum fun j _ => ?_
    nlinarith [mul_nonneg (hp j) (sub_nonneg.mpr (h j).2),
      mul_nonneg (hn j) (sub_nonneg.mpr (h j).1)]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
