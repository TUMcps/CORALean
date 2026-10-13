import CORALean.ContSet.Interval.Float.Operations.CoshLo
import CORALean.ContSet.Interval.Float.Operations.CoshHi
import CORALean.ContSet.Interval.Float.Interval

/-!
# `Interval.cosh`

CORA's `@interval/cosh`, coordinate by coordinate, over `coshLo` and `coshHi`.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Pointwise FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Interval.cosh (p : ℕ) (I : Interval (Vec 𝕋 n)) : Interval (Vec 𝕋 n) where
  inf := fun i => Interval.coshLo p (I.inf i) (I.sup i)
  sup := fun i => Interval.coshHi p (I.inf i) (I.sup i)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
