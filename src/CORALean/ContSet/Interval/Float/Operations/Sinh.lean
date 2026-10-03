import CORALean.Global.Float.Hyperbolic
import CORALean.ContSet.Interval.Float.Interval

/-!
# `Interval.sinh`

Increasing, so `sinhDown` at the lower bound and `sinhUp` at the upper one
(`Global/Float/Hyperbolic`). `p` is the precision of the exponentials.
-/

-- Authors:       Tobias Ladner
-- Written:       02-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Pointwise FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Interval.sinh (p : ℕ) (I : Interval (Vec 𝕋 n)) : Interval (Vec 𝕋 n) where
  inf := fun i => sinhDown p (I.inf i)
  sup := fun i => sinhUp p (I.sup i)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
