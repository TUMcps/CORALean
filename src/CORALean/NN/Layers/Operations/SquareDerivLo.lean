import CORALean.Global.Float.FloatOps

/-!
# The least derivative of the square

`σ' x = 2x` over `[l, u]` is at least `2 l`, rounded down.
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

/-- `2 l` from below, the derivative's least value on the box. -/
def squareDerivLo (l _u : 𝕋) : 𝕋 := addDown l l

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
