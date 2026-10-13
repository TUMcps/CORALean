module

public import CORALean.Global.Float.SoundFloatArithmetic

@[expose] public section

/-!
# A zeroed term reads as zero

`if` commutes with `toReal`, and the stored `zero` reads as `0`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-September-2026
-- Last update:   23-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float Float.FloatOps Float.SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem toReal_ite_zero (v : Fin n → 𝕋) (i j : Fin n) :
    toReal (if j = i then zero else v j) = if j = i then (0 : ℝ) else toReal (v j) := by
  by_cases h : j = i
  · rw [if_pos h, if_pos h, toReal_zero]
  · rw [if_neg h, if_neg h]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
