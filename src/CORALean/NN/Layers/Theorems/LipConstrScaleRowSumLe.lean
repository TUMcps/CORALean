module

public import CORALean.NN.Layers.Operations.LipConstrScale
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Positivity

@[expose] public section

/-!
# The rows of `N W` have absolute sum at most `λ`

For `0 < λ`: a row whose absolute sum `s` exceeds `λ` is divided by `s / λ`, giving `λ`, and any
other row is untouched. So the layer is `λ`-Lipschitz in the supremum norm.

## Inputs
* `W` – weight matrix
* `lam` – Lipschitz bound
* `i` – row index

## Hypotheses
* `hl` – Lipschitz bound is positive

## Conclusion
* the absolute row sum of the rescaled weights is at most the bound
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      14-October-2026 (Tobias Ladner)


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {n m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- The rows of `N W` have absolute sum at most `λ`. -/
theorem Layer.lipConstrScale_rowSum_le (W : Mat ℝ m n) {lam : ℝ} (hl : 0 < lam)
    (i : Fin m) : -- --- CONCL ---
    ∑ j, |(Matrix.diagonal (Layer.lipConstrScale W lam) * W) i j| ≤ lam := by -- --- PROOF ---
  set s := ∑ j, |W i j| with hs
  have hs0 : 0 ≤ s := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hN : 0 < max 1 (lam⁻¹ * s) := lt_of_lt_of_le one_pos (le_max_left _ _)
  have hrow : ∑ j, |(Matrix.diagonal (Layer.lipConstrScale W lam) * W) i j|
      = (1 / max 1 (lam⁻¹ * s)) * s := by
    simp only [Matrix.diagonal_mul, Layer.lipConstrScale, abs_mul, ← Finset.mul_sum]
    rw [abs_of_pos (by positivity)]
  rw [hrow, div_mul_eq_mul_div, one_mul, div_le_iff₀ hN]
  rcases le_total 1 (lam⁻¹ * s) with h | h
  · rw [max_eq_right h, mul_inv_cancel_left₀ hl.ne']
  · rw [max_eq_left h, mul_one]
    calc s = lam * (lam⁻¹ * s) := by field_simp
      _ ≤ lam * 1 := mul_le_mul_of_nonneg_left h hl.le
      _ = lam := mul_one _

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
