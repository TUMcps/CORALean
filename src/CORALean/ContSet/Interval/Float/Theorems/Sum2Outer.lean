import CORALean.ContSet.Interval.Float.Operations.Sum2
import CORALean.ContSet.Interval.Real.Operations.Sum2

/-!
# `Interval.sum₂` holds the exact layer's box

The lower bounds sum rounding down and the upper bounds rounding up. No nonemptiness is
needed: the rounding only widens.
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

theorem Interval.sum₂_outer (I : Interval (Mat 𝕋 m n)) :
    I.nominal.sum₂.construct ⊆ I.sum₂.construct := by
  intro y hy i
  exact ⟨le_trans (sumDown_le_sum _) (hy i).1, le_trans (hy i).2 (sum_le_sumUp _)⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
