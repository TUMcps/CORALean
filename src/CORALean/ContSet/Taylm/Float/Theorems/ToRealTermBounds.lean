module

public import CORALean.ContSet.Taylm.Float.Operations.TermBounds
public import CORALean.ContSet.Taylm.Real.Operations.TermBounds

@[expose] public section

/-!
# The float term range reads as the exact one

Every operation in `termBounds` is exact, so this is an equality.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Taylm.toReal_termBounds (a : 𝕋 × (Fin n → ℕ)) :
    (toReal (Taylm.termBounds a).1, toReal (Taylm.termBounds a).2)
      = Real.Taylm.termBounds (toReal a.1, a.2) := by
  unfold Taylm.termBounds Real.Taylm.termBounds
  split_ifs <;> simp [toReal_minimum, toReal_maximum, toReal_zero, toReal_neg, toReal_absolute]

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
