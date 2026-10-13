module

public import CORALean.Global.Float.FloatOps

@[expose] public section

/-!
# The least derivative of the square

`σ' x = 2x` over `[l, u]` is at least `2 l`, rounded down.
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

/-- `2 l` from below, the derivative's least value on the box. -/
def squareDerivLo (l _u : 𝕋) : 𝕋 := addDown l l

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
