import CORALean.ContSet.Fullspace.Real.Fullspace
import Mathlib.Data.ENNReal.Basic

/-!
# `Fullspace.radius`

CORA's `@fullspace/radius`: `Inf`. At dimension `0` CORA answers `NaN`; that case is not claimed.
-/

-- Authors:       Tobias Ladner
-- Written:       02-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `fullspace/radius`: `Inf`. -/
def Fullspace.radius (_ : Fullspace n) : ENNReal := ⊤

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
