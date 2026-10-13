module

public import CORALean.ContSet.Interval.Float.Operations.Sum1

@[expose] public section

/-!
# `Interval.sum₁` holds every member's sums

The image of the members of the stored box under the sums lies in the stored result.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {m n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Interval.sum₁_outer_image (I : Interval (Mat 𝕋 m n)) :
    (fun A : Mat ℝ m n => fun j => ∑ i, A i j) '' I.construct ⊆
      I.sum₁.construct := by
  rintro _ ⟨A, hA, rfl⟩ j
  exact ⟨le_trans (sumDown_le_sum _) (Finset.sum_le_sum fun i _ => (hA (i, j)).1),
    le_trans (Finset.sum_le_sum fun i _ => (hA (i, j)).2) (sum_le_sumUp _)⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
