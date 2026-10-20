module

public import CORALean.Specification.PointSegmentSignal.PointSegmentSignal
public import Mathlib.Order.Basic

@[expose] public section

/-!
# The value of a signal at a time

`at` of `pointSegmentSignal.m` (via `priv_atIdx`): take the last time point `≤ time`; the point
value if it is `time`, else the value of the interval after it. The `find(...,'last')` is the
number of points `≤ time`, as the times are sorted; `time ≥ 0` is a precondition (CORA throws).

## Inputs
* `T` – time type
* `s` – signal
* `time` – time

## Output
* the value of the signal at the time
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `obj.at(time)`. -/
def PointSegmentSignal.at {T : Type} [LinearOrder T] (s : PointSegmentSignal T) (time : T) : Bool :=
  -- 1. i = find(obj.timePoints <= time,1,'last')
  let i := (s.timePoints.takeWhile (· ≤ time)).length - 1
  -- 2. the point value if timePoints(i) == time, else the following interval value
  if s.timePoints[i]? = some time then s.values.getD (2 * i) false
  else s.values.getD (2 * i + 1) false

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
