import CORALean.Global.Float.Hyperbolic
import CORALean.ContSet.Interval.Float.Interval

/-!
# `Interval.coshHi`

The upper bound of `cosh` over `[lb, ub]`, as the real `Interval.coshHi`: `cosh lb` if the range
lies left of `0`, `cosh ub` if right of it, and `cosh` of the larger magnitude otherwise, which
bounds `cosh` at every range.
-/

-- Authors:       Tobias Ladner
-- Written:       02-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Pointwise FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

def Interval.coshHi (p : ℕ) (lb ub : 𝕋) : 𝕋 :=
  if le ub zero = true then coshUp p lb else if le zero lb = true then coshUp p ub
  else coshUp p (maximum (neg lb) ub)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
