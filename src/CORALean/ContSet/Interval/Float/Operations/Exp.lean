import CORALean.Global.Float.Exp
import CORALean.ContSet.Interval.Float.Interval

/-!
# `Interval.exp`

Monotone, so `expDown` at the lower bound and `expUp` at the upper one. `p` is the precision of
the two enclosures (`Global/Float/Exp`).
-/

-- Authors:       Tobias Ladner
-- Written:       01-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Interval.exp (p : ℕ) (I : Interval (Vec 𝕋 n)) : Interval (Vec 𝕋 n) where
  inf := fun i => expDown p (I.inf i)
  sup := fun i => expUp p (I.sup i)


end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
