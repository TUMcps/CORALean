module

public import CORALean.Global.Float.InverseTrig
public import CORALean.ContSet.Interval.Float.Interval

@[expose] public section

/-!
# `Interval.asin`

Increasing (and constant outside `[-1, 1]`, as `Real.arcsin` is), so `asinDown` at the lower
bound and `asinUp` at the upper one (`Global/Float/InverseTrig`), sound for every box. `p` is the
number of halvings of the sine and cosine, `k` the number of bisection and Newton steps.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Pointwise FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Interval.asin (p k : ℕ) (I : Interval (Vec 𝕋 n)) : Interval (Vec 𝕋 n) where
  inf := fun i => asinDown p k (I.inf i)
  sup := fun i => asinUp p k (I.sup i)


end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
