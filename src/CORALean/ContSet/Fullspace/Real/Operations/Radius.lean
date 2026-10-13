module

public import CORALean.ContSet.Fullspace.Real.Fullspace
public import Mathlib.Data.ENNReal.Basic

@[expose] public section

/-!
# `Fullspace.radius`

CORA's `@fullspace/radius`: `Inf`. At dimension `0` CORA answers `NaN`; that case is not claimed.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `fullspace/radius`: `Inf`. -/
def Fullspace.radius (_ : Fullspace n) : ENNReal := ⊤

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
