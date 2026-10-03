import CORALean.ContSet.Taylm.Float.Operations.Hyperbolic

/-!
# `Taylm.sinh`

The Taylor model of `sinh`: `Taylm.hyperbolic` with the even coefficients `sinh`'s.
-/

-- Authors:       Tobias Ladner
-- Written:       02-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Taylm.sinh (p : ℕ) (T : Taylm 𝕋 n) : Taylm 𝕋 n := T.hyperbolic p true

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
