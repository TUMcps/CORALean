import CORALean.ContSet.ConPolyZono.Float.ConPolyZono

/-!
# `ConPolyZono.centre` over a floating-point scalar

CORA's `center` of a constrained polynomial zonotope: the stored field `c`, nothing computed,
so nothing rounds. Whether it is a point of the set is `centre_mem_construct`.
-/

-- Authors:       Tobias Ladner
-- Written:       04-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def ConPolyZono.centre (cPZ : ConPolyZono 𝕋 n) : Vec 𝕋 n := cPZ.c

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
