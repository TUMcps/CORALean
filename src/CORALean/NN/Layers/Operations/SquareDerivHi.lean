module

public import CORALean.Global.Float.FloatOps

@[expose] public section

/-!
# The greatest derivative of the square

`σ' x = 2x` over `[l, u]` is at most `2 u`, rounded up.
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float Float.FloatOps

variable {𝕋 : Type} [FloatOps 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `2 u` from above, the derivative's greatest value on the box. -/
def squareDerivHi (_l u : 𝕋) : 𝕋 := addUp u u

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
