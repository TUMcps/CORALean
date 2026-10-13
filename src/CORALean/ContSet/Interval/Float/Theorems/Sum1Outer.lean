module

public import CORALean.ContSet.Interval.Float.Operations.Sum1
public import CORALean.ContSet.Interval.Real.Operations.Sum1

@[expose] public section

/-!
# `Interval.sum₁` holds the exact layer's box

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

theorem Interval.sum₁_outer (I : Interval (Mat 𝕋 m n)) :
    I.nominal.sum₁.construct ⊆ I.sum₁.construct := by
  intro y hy j
  exact ⟨le_trans (sumDown_le_sum _) (hy j).1, le_trans (hy j).2 (sum_le_sumUp _)⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
