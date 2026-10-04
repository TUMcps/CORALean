import CORALean.ContSet.Zoo.Float.Operations.Uplus

/-!
# `Zoo.uplus` encloses

The zoo itself.
-/

-- Authors:       Tobias Ladner
-- Written:       04-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zoo.uplus_outer {Z : Zoo 𝕋 n} {f : Vec ℝ n → ℝ} (h : Z.Encloses f) :
    Z.uplus.Encloses f := h

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
