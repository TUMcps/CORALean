module

public import CORALean.ContSet.Zoo.Float.Operations.Uplus

@[expose] public section

/-!
# `Zoo.uplus` encloses

The zoo itself.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zoo.uplus_outer {Z : Zoo 𝕋 n} {f : Vec ℝ n → ℝ} (h : Z.Encloses f) :
    Z.uplus.Encloses f := h

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
