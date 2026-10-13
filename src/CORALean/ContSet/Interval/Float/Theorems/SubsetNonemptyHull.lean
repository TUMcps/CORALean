import CORALean.ContSet.Interval.Float.Operations.NonemptyHull

/-!
# The nonempty hull contains the box

Only the upper bound moves, and only up, so every point of the box stays inside.
-/

-- Authors:       Claude Opus 5.5
-- Written:       24-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Interval.construct_subset_nonemptyHull (I : Interval (Vec 𝕋 n)) :
    I.construct ⊆ I.nonemptyHull.construct := fun x hx i => by
  obtain ⟨hlo, hhi⟩ := hx i
  refine ⟨hlo, ?_⟩
  show x i ≤ toReal (maximum (I.inf i) (I.sup i))
  rw [toReal_maximum]
  exact le_trans hhi (le_max_right _ _)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
