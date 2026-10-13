module

public import CORALean.ContSet.Taylm.Real.Taylm

@[expose] public section

/-!
# `Taylm.uplus`

CORA's unary `+`: the model itself.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Taylm.uplus (T : Taylm n) : Taylm n := T

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
