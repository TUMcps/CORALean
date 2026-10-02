import CORALean.ContSet.Taylm.Real.Operations.Taylor
import CORALean.ContSet.Taylm.Real.Operations.ConstCoef
import Mathlib.Analysis.Complex.Trigonometric

/-!
# `Taylm.cos`

CORA's `cos`: the expansion at the constant part, every derivative of `cos` bounded by
`1`.
-/

-- Authors:       Tobias Ladner
-- Written:       02-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

noncomputable def Taylm.cos (T : Taylm n) : Taylm n :=
  T.taylor Real.cos T.constCoef 1

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
