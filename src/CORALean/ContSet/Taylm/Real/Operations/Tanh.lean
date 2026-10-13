import CORALean.ContSet.Taylm.Real.Operations.Taylor
import CORALean.ContSet.Taylm.Real.Operations.ConstCoef
import CORALean.Global.ElementaryDerivBounds

/-!
# `Taylm.tanh`

CORA's `tanh`: the expansion at the constant part. `tanh' = 1 - tanh²`, so `tanh⁽ᴺ⁺¹⁾` is
a polynomial in `tanh`, of absolute-coefficient bound `odePoly (1 + X²) (N+1)` at `|tanh| ≤ 1`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

noncomputable def Taylm.tanh (T : Taylm n) : Taylm n :=
  T.taylor Real.tanh T.constCoef ((odePoly (1 + Polynomial.X ^ 2) (T.maxOrder + 1)).eval 1)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
