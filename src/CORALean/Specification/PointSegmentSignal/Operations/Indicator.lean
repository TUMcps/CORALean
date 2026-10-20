module

public import CORALean.Specification.PointSegmentSignal.Operations.IndicatorBounds
public import CORALean.Specification.STLInterval.Operations.Basic

@[expose] public section

/-!
# Indicator signals of an interval

`indicator(interval,val,default)` of `pointSegmentSignal.m` for a time type `ℝ` and an
`stlInterval`:
the bounds of the interval (the empty interval, and any interval with a bound below `0`, as the
constructor leaves them) are read off by `lowerBound`, `upperBound` and the closedness flags, and
`indicatorBounds` builds the signal.

Refinement pending: CORA computes this in doubles, and its refinement generic over `𝕋` (time
stamps over `𝕋`, rounded outward) is not yet written.

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


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `sig = pointSegmentSignal.indicator(interval,val,default)`. -/
noncomputable def PointSegmentSignal.indicator (I : STLInterval) (val default : Bool) :
    PointSegmentSignal ℝ :=
  PointSegmentSignal.indicatorBounds I.lowerBound I.upperBound I.lowerClosed I.upperClosed val
    default

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
