module

public import CORALean.ContSet.Zoo.Real.Zoo

@[expose] public section

/-!
# `Zoo.uplus`

CORA's unary `+`: the zoo unchanged.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Zoo.uplus (Z : Zoo n) : Zoo n := Z

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
