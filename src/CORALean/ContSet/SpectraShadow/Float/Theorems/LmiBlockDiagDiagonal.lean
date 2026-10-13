import CORALean.ContSet.SpectraShadow.Float.Theorems.ToRealMatBlockDiag

/-!
# An inequality beside a diagonal block, at a point

Every operation that adds linear constraints to a shadow stores them as a diagonal block beside
the old inequality, each matrix `blockDiag (X l) (diagonal (d l))`. At the variables `v` the
whole inequality is then the old part at `v` beside the diagonal of the constraint values at `v`,
so it holds exactly when the old part holds and every constraint value is nonnegative.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Matrix

variable {k b m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem SpectraShadow.lmi_blockDiag_diagonal (X₀ : Mat ℝ k k) (X : Fin m → Mat ℝ k k)
    (d₀ : Vec ℝ b) (d : Fin m → Vec ℝ b) (v : Fin m → ℝ) :
    blockDiag 0 X₀ (diagonal d₀) + ∑ l, v l • blockDiag 0 (X l) (diagonal (d l))
      = blockDiag 0 (X₀ + ∑ l, v l • X l) (diagonal (d₀ + ∑ l, v l • d l)) := by -- --- PROOF ---
  simp only [← blockDiag_smul, ← blockDiag_sum, ← blockDiag_add]
  congr 1
  ext r r'
  simp only [Matrix.add_apply, Matrix.sum_apply, Matrix.smul_apply, Matrix.diagonal_apply,
    Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  by_cases h : r = r'
  · simp [h]
  · simp [h]

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
