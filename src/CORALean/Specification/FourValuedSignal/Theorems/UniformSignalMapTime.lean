module

public import CORALean.Specification.FourValuedSignal.Theorems.IndicatorMapTime

@[expose] public section

/-!
# The constant four-valued signal at a float time type, read as reals

Over a float scalar `𝕋` the constant signal is the indicator of the empty interval, exact as
every indicator is, so read through `toReal` it is the constant real signal.

## Inputs
* `val` – the constant value

## Hypotheses
* none

## Conclusion
* the constant float signal, read as reals, is the constant real signal
-/

-- Authors:       Claude Opus 5.5
-- Written:       23-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ExactLe 𝕋]


-- =======================================  MAIN THEOREM  ======================================= --

theorem FourValuedSignal.uniformSignal_mapTime (val : FourValued) :
    (FourValuedSignal.uniformSignal (𝕋 := 𝕋) val).mapTime toReal =
      FourValuedSignal.uniformSignal val := by
  rw [FourValuedSignal.uniformSignal, FourValuedSignal.indicator_mapTime]
  rfl

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
