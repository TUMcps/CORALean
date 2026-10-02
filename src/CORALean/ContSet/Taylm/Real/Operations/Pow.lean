import CORALean.ContSet.Taylm.Real.Operations.Times
import CORALean.ContSet.Taylm.Real.Operations.Const

/-!
# `Taylm.pow`

CORA's `power` and `mpower` at a natural exponent on one model: `times` repeated, each
product truncated at the model's order, starting from the constant one.
-/

-- Authors:       Tobias Ladner
-- Written:       02-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Taylm.pow (T : Taylm n) : ℕ → Taylm n
  | 0 => Taylm.const n 1 T.maxOrder
  | k + 1 => (T.pow k).times T

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
