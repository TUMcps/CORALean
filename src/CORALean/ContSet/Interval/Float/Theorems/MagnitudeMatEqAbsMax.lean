module

public import CORALean.ContSet.Interval.Float.Operations.MagnitudeMat
public import CORALean.ContSet.Interval.Real.Operations.AbsMax

@[expose] public section

/-!
# `Interval.magnitudeMat` is the exact layer's `absMax`

`maximum` and `absolute` round nothing, so the float matrix of larger absolute values reads back
as the real entrywise maximum of `|inf|` and `|sup|`, which is CORA's `abs(intMat)`.

## Inputs
* `I` – interval matrix

## Hypotheses
* none

## Conclusion
* the stored matrix, read as reals, is `absMax` of the nominal interval matrix
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       26-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {m n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Interval.magnitudeMat_eq_absMax (I : Interval (Mat 𝕋 m n)) :
    toRealMat I.magnitudeMat = I.nominal.absMax := by
  funext i j
  simp only [toRealMat, Interval.magnitudeMat, toReal_maximum, toReal_absolute]
  rfl

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
