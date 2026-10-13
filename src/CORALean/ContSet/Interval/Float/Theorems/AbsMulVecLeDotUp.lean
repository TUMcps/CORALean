import CORALean.ContSet.Interval.Float.Interval
import Mathlib.Data.Matrix.Basic

/-!
# A matrix under entrywise bounds applied to a bounded vector

If `|M i k| ≤ R i k` and `|x k| ≤ ξ k`, then `|(M x) i| ≤ dotUp (R i) ξ`: each product is below
its rounded-up bound, and the sum is below the rounded-up sum.
-/

-- Authors:       Claude Opus 5.5
-- Written:       10-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Matrix FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {m n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem abs_mulVec_le_dotUp {M : Mat ℝ m n} {R : Mat 𝕋 m n} {x : Vec ℝ n} {ξ : Vec 𝕋 n}
    (hM : ∀ i k, |M i k| ≤ toReal (R i k)) (hx : ∀ k, |x k| ≤ toReal (ξ k)) (i : Fin m) :
    |((M *ᵥ x) i)| ≤ toReal (dotUp (R i) ξ) := by -- --- PROOF ---
  show |∑ k, M i k * x k| ≤ toReal (sumUp fun k => mulUp (R i k) (ξ k))
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) (le_trans ?_ (sum_le_sumUp _))
  refine Finset.sum_le_sum fun k _ => ?_
  rw [abs_mul]
  exact le_trans (mul_le_mul (hM i k) (hx k) (abs_nonneg _) ((abs_nonneg _).trans (hM i k)))
    (mul_le_mulUp _ _)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
