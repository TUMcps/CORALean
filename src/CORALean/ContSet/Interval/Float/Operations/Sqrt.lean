module

public import CORALean.Global.Float.Sqrt
public import CORALean.ContSet.Interval.Float.Interval

@[expose] public section

/-!
# `Interval.sqrt`

Monotone, so `sqrtDown` at the lower bound and `sqrtUp` at the upper one. `p` is the number of
Newton steps (`Global/Float/Sqrt`). CORA throws below `0`; the enclosure here is of `Real.sqrt`,
which is `0` there, and needs no domain.
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

def Interval.sqrt (p : ℕ) (I : Interval (Vec 𝕋 n)) : Interval (Vec 𝕋 n) where
  inf := fun i => sqrtDown p (I.inf i)
  sup := fun i => sqrtUp p (I.sup i)


end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
