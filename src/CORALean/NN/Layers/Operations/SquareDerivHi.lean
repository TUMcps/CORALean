import CORALean.Global.Float.FloatOps

/-!
# The greatest derivative of the square

`σ' x = 2x` over `[l, u]` is at most `2 u`, rounded up.
-/

-- Authors:       Tobias Ladner
-- Written:       01-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float Float.FloatOps

variable {𝕋 : Type} [FloatOps 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `2 u` from above, the derivative's greatest value on the box. -/
def squareDerivHi (_l u : 𝕋) : 𝕋 := addUp u u

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
