import CORALean.ContSet.Taylm.Real.Operations.Plus
import CORALean.ContSet.Taylm.Real.Operations.Uminus

/-!
# `Taylm.minus`

CORA's `minus`, as `plus` of the negation; CORA subtracts the remainders, which is the
same interval.
-/

-- Authors:       Tobias Ladner
-- Written:       02-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Taylm.minus (T₁ T₂ : Taylm n) : Taylm n := T₁.plus T₂.uminus

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
