import CORALean.Global.Float.Log
import CORALean.ContSet.Interval.Float.Interval

/-!
# `Interval.log`

Monotone, so `logDown` at the lower bound and `logUp` at the upper one. `p` is `expUp`'s precision
and `k` the number of bisection steps (`Global/Float/Log`).
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Pointwise FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Interval.log (p k : ℕ) (I : Interval (Vec 𝕋 n)) : Interval (Vec 𝕋 n) where
  inf := fun i => logDown p k (I.inf i)
  sup := fun i => logUp p k (I.sup i)


end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
