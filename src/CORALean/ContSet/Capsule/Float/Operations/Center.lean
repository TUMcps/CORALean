import CORALean.ContSet.Capsule.Float.Capsule

/-!
# `Capsule.center` over a floating-point scalar

CORA returns the field `c`; so does this.
-/

-- Authors:       Tobias Ladner
-- Written:       02-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Capsule.center (C : Capsule 𝕋 n) : Vec 𝕋 n := C.c

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
