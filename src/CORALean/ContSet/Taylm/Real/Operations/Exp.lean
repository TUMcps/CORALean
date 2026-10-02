import CORALean.ContSet.Taylm.Real.Operations.Taylor
import CORALean.ContSet.Taylm.Real.Operations.ConstCoef

/-!
# `Taylm.exp`

CORA's `exp`: the expansion at the constant part, every derivative `exp`, so the Lagrange
derivative is bounded by `exp` at the top of the range.
-/

-- Authors:       Tobias Ladner
-- Written:       02-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

noncomputable def Taylm.exp (T : Taylm n) : Taylm n :=
  T.taylor Real.exp T.constCoef (Real.exp (max T.constCoef T.bounds.2))

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
