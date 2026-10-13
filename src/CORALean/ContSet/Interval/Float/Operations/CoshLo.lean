module

public import CORALean.Global.Float.Hyperbolic
public import CORALean.ContSet.Interval.Float.Interval

@[expose] public section

/-!
# `Interval.coshLo`

The lower bound of `cosh` over `[lb, ub]`, as the real `Interval.coshLo`: `cosh ub` if the range
lies left of `0`, `cosh lb` if right of it, and `1` if it contains `0`. `le` answers only `true`
reliably, which is enough: the third case is a bound at every range.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Pointwise FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

def Interval.coshLo (p : ℕ) (lb ub : 𝕋) : 𝕋 :=
  if le ub zero = true then coshDown p ub else if le zero lb = true then coshDown p lb else one

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
