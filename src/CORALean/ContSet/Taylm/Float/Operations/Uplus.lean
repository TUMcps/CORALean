import CORALean.ContSet.Taylm.Float.Taylm

/-!
# `Taylm.uplus`

CORA's unary `+`: the model itself.
-/

-- Authors:       Tobias Ladner
-- Written:       02-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Taylm.uplus (T : Taylm 𝕋 n) : Taylm 𝕋 n := T

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
