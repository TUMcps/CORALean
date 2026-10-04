import CORALean.ContSet.Zoo.Float.Zoo

/-!
# `Zoo.uplus`, over a floating-point scalar

The zoo itself.
-/

-- Authors:       Tobias Ladner
-- Written:       04-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Zoo.uplus (Z : Zoo 𝕋 n) : Zoo 𝕋 n := Z

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
