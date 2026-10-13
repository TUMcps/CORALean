module

public import CORALean.Global.Float.Hyperbolic
public import CORALean.ContSet.Interval.Float.Interval

@[expose] public section

/-!
# `Interval.tanh`

Increasing, so `tanhDown` at the lower bound and `tanhUp` at the upper one
(`Global/Float/Hyperbolic`). `p` is the precision of the exponential.
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

def Interval.tanh (p : ℕ) (I : Interval (Vec 𝕋 n)) : Interval (Vec 𝕋 n) where
  inf := fun i => tanhDown p (I.inf i)
  sup := fun i => tanhUp p (I.sup i)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
