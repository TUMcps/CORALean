import CORALean.ContSet.Taylm.Real.Taylm

/-!
# `Taylm.uplus`

CORA's unary `+`: the model itself.
-/

-- Authors:       Tobias Ladner
-- Written:       02-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Taylm.uplus (T : Taylm n) : Taylm n := T

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
