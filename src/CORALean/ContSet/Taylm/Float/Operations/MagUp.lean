import CORALean.ContSet.Taylm.Float.Operations.Bounds
import CORALean.ContSet.Taylm.Float.Operations.ConstCoef

/-!
# `Taylm.magUp`

The largest absolute value of the constant part and the two ends of the range: a bound of
`|ξ|` on the hull of the centre and the range, which is where a Lagrange remainder looks for
the derivative.
-/

-- Authors:       Tobias Ladner
-- Written:       03-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Taylm.magUp (T : Taylm 𝕋 n) : 𝕋 :=
  maximum (absolute T.constCoef) (maximum (absolute T.bounds.1) (absolute T.bounds.2))

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
