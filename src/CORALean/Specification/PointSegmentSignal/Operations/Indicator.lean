module

public import CORALean.Specification.PointSegmentSignal.Operations.IndicatorBounds
public import CORALean.Specification.STLInterval.Operations.Basic

@[expose] public section

/-!
# Indicator signals of an interval

`indicator(interval,val,default)` of `pointSegmentSignal.m` for a time scalar `𝕋` and an
`stlInterval`: the bounds of the interval (the empty interval, and any interval with a bound below
`0`, as the constructor leaves them) are read off by `lowerBound`, `upperBound` and the closedness
flags, and `indicatorBounds` builds the signal.

## Inputs
* `I` – time interval
* `val` – value on the interval
* `default` – value elsewhere

## Output
* the signal that is `val` on the interval and `default` elsewhere
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {𝕋 : Type} [Float.FloatOps 𝕋] [Float.SoundFloatArithmetic 𝕋] [TimeOrder 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `sig = pointSegmentSignal.indicator(interval,val,default)`. -/
def PointSegmentSignal.indicator (I : STLInterval 𝕋) (val default : Bool) : PointSegmentSignal 𝕋 :=
  PointSegmentSignal.indicatorBounds I.lowerBound I.upperBound I.lowerClosed I.upperClosed val
    default

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
