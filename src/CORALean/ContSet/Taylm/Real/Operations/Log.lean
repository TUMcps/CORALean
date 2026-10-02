import CORALean.ContSet.Taylm.Real.Operations.Taylor
import CORALean.ContSet.Taylm.Real.Operations.ConstCoef
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# `Taylm.log`

CORA's `log`: the expansion at the constant part, `|log⁽ᴺ⁺¹⁾ ξ| = N! / ξᴺ⁺¹`, largest at the
bottom of the range. Meaningful where that bottom is positive, which `LogOuter` assumes as
CORA's `CORA:outOfDomain` check does.
-/

-- Authors:       Tobias Ladner
-- Written:       02-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

noncomputable def Taylm.log (T : Taylm n) : Taylm n :=
  T.taylor Real.log T.constCoef
    ((T.maxOrder.factorial : ℝ) / min T.constCoef T.bounds.1 ^ (T.maxOrder + 1))

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
