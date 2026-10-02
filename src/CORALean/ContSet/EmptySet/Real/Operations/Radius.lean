import CORALean.ContSet.EmptySet.Real.EmptySet
import Mathlib.Data.ENNReal.Basic

/-!
# `EmptySet.radius`

CORA's `@emptySet/radius`: `0`.
-/

-- Authors:       Tobias Ladner
-- Written:       02-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `emptySet/radius`: `0`. -/
def EmptySet.radius (_ : EmptySet n) : ENNReal := 0

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
