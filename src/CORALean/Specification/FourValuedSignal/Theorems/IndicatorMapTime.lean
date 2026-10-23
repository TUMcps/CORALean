module

public import CORALean.Specification.FourValuedSignal.Operations.Basic
public import CORALean.Specification.PointSegmentSignal.Theorems.IndicatorMapTime

@[expose] public section

/-!
# The four-valued indicator at a float time type, read as reals

Over a float scalar `𝕋` all three parts of the four-valued indicator of a float `stlInterval` are
exact indicators (`PointSegmentSignal.indicator_mapTime`), so read through `toReal` it is the
indicator of the interval it denotes.

## Inputs
* `I` – time interval
* `val` – value on the interval
* `default` – value elsewhere

## Hypotheses
* none

## Conclusion
* the float indicator, read as reals, is the indicator of the denoted interval
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

theorem FourValuedSignal.indicator_mapTime (I : STLInterval 𝕋) (val default : FourValued) :
    (FourValuedSignal.indicator I val default).mapTime toReal =
      FourValuedSignal.indicator I.toRealInterval val default := by
  simp only [FourValuedSignal.indicator, KleeneSignal.indicator, FourValuedSignal.mapTime,
    KleeneSignal.mapTime, PointSegmentSignal.indicator_mapTime]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
