import CORALean.ContSet.Zoo.Real.Zoo

/-!
# `Zoo.uplus`

CORA's unary `+`: the zoo unchanged.
-/

-- Authors:       Tobias Ladner
-- Written:       03-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Zoo.uplus (Z : Zoo n) : Zoo n := Z

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
