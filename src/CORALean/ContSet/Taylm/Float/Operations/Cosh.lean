import CORALean.ContSet.Taylm.Float.Operations.Hyperbolic

/-!
# `Taylm.cosh`

The Taylor model of `cosh`: `Taylm.hyperbolic` with the even coefficients `cosh`'s.
-/

-- Authors:       Tobias Ladner
-- Written:       02-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Taylm.cosh (p : ℕ) (T : Taylm 𝕋 n) : Taylm 𝕋 n := T.hyperbolic p false

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
