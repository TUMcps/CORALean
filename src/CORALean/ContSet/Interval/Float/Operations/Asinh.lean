module

public import CORALean.Global.Float.InverseHyperbolic
public import CORALean.ContSet.Interval.Float.Interval

@[expose] public section

/-!
# `Interval.asinh`

Increasing, so `asinhDown` at the lower bound and `asinhUp` at the upper one
(`Global/Float/InverseHyperbolic`). `p` is `logDown`'s range exponent, `k` the number of
bisection and Newton steps.

## Inputs
* `p` – range exponent of `logDown`
* `k` – bisection and Newton steps
* `I` – interval box

## Output
* interval box enclosing the inverse hyperbolic sine of `I`
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

def Interval.asinh (p k : ℕ) (I : Interval (Vec 𝕋 n)) : Interval (Vec 𝕋 n) where
  inf := fun i => asinhDown p k (I.inf i)
  sup := fun i => asinhUp p k (I.sup i)


end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
