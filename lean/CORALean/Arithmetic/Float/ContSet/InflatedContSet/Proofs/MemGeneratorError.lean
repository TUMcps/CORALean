import CORALean.Arithmetic.Float.ContSet.InflatedContSet.API

/-!
# What an inexact matrix costs

Every coefficient can conspire, so the row sums with no cancellation: the
triangle inequality, then `|β j| ≤ 1` discarding each coefficient, then `sumUp`
above the total.
-/

-- Authors:       Tobias Ladner
-- Written:       16-August-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Arithmetic.Float.InflatedContSet.Proofs

open FloatOps SoundFloatArithmetic

variable {F : Type} [FloatOps F] [SoundFloatArithmetic F] {n h : ℕ}

theorem mem_generatorError {d : Mat F n h} {Δ : Mat ℝ n h} {β : Vec ℝ h}
    (hd : ∀ i j, |Δ i j| ≤ toReal (d i j)) (hβ : ∀ j, |β j| ≤ 1) :
    (fun i => ∑ j, Δ i j * β j) ∈ (generatorError d).construct := by
  intro i
  have key : |∑ j, Δ i j * β j| ≤ toReal (sumUp fun j => d i j) := by
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    refine le_trans (Finset.sum_le_sum fun j _ => ?_) (sum_le_sumUp _)
    rw [abs_mul]
    exact le_trans (mul_le_of_le_one_right (abs_nonneg _) (hβ j)) (hd i j)
  refine ⟨?_, le_of_abs_le key⟩
  show toReal (neg (sumUp fun j => d i j)) ≤ ∑ j, Δ i j * β j
  rw [toReal_neg]
  exact neg_le_of_abs_le key

end CORALean.Arithmetic.Float.InflatedContSet.Proofs
