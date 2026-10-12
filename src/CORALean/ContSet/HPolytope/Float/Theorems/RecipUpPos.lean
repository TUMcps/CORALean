import CORALean.ContSet.HPolytope.Float.Operations.RecipUp

/-!
# `recipUp` is positive

Taken only at a certified positive number, and rounded up, so above a positive one; otherwise it
is `1`.
-/

-- Authors:       Tobias Ladner
-- Written:       12-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem HPolytope.recipUp_pos (a : 𝕋) : 0 < toReal (HPolytope.recipUp a) := by -- --- PROOF ---
  by_cases h : ltStrict zero a = true
  · simp only [HPolytope.recipUp, h, if_true]
    have hpos := toReal_lt_of_ltStrict h
    rw [toReal_zero] at hpos
    refine lt_of_lt_of_le ?_ (div_le_divUp _ _ hpos)
    rw [toReal_one]
    exact one_div_pos.mpr hpos
  · simp only [HPolytope.recipUp, h, if_false, Bool.false_eq_true]
    rw [toReal_one]
    exact one_pos

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
