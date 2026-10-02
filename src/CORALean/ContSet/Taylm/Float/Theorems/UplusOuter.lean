import CORALean.ContSet.Taylm.Float.Operations.Uplus

/-!
# `Taylm.uplus` encloses the function, over a floating-point scalar
-/

-- Authors:       Tobias Ladner
-- Written:       02-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Taylm.uplus_outer {T : Taylm 𝕋 n} {f : Vec ℝ n → ℝ} (h : T.Encloses f) :
    T.uplus.Encloses f := h

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
