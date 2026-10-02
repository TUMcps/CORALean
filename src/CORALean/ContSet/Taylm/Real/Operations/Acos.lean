import CORALean.ContSet.Taylm.Real.Operations.Taylor
import CORALean.ContSet.Taylm.Real.Operations.ConstCoef
import CORALean.ContSet.Taylm.Real.Operations.Mag
import CORALean.Global.ElementaryDerivBounds

/-!
# `Taylm.acos`

CORA's `acos`: `acos' = -asin'`, so the derivative bound is `asin`'s, and so is the
domain.
-/

-- Authors:       Tobias Ladner
-- Written:       02-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

noncomputable def Taylm.acos (T : Taylm n) : Taylm n :=
  T.taylor Real.arccos T.constCoef
    ((asinDom T.maxOrder).eval T.mag * ((√(1 - T.mag ^ 2))⁻¹) ^ (2 * T.maxOrder + 1))

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
