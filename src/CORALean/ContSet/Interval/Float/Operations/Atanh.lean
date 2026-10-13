module

public import CORALean.Global.Float.Atanh
public import CORALean.ContSet.Interval.Float.Interval

@[expose] public section

/-!
# `Interval.atanh`

Increasing, so `atanhDown` at the lower bound and `atanhUp` at the upper one
(`Global/Float/Atanh`). `p` is `logDown`'s range exponent, `k` the number of bisection steps.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Interval.atanh (p k : ℕ) (I : Interval (Vec 𝕋 n)) : Interval (Vec 𝕋 n) where
  inf := fun i => atanhDown p k (I.inf i)
  sup := fun i => atanhUp p k (I.sup i)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
