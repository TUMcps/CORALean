module

public import CORALean.Specification.PointSegmentSignal.Operations.AtIdx
public import CORALean.Specification.PointSegmentSignal.Operations.Basic

@[expose] public section

/-!
# Setting the value at one time

`aux_setPoint(obj,point,value)` of `pointSegmentSignal/set.m`: set the value at a single time. If it
already has `value`, nothing changes; at a time point the point value is set, and the point is
dropped when it then matches the intervals around it; elsewhere a new point is inserted.

## Inputs
* `T` – time type
* `s` – signal
* `point` – time to set
* `value` – value to set

## Output
* the signal with the value set at that time
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `sig = aux_setPoint(obj,point,value)`. -/
def PointSegmentSignal.setPoint {T : Type} [LinearOrder T] [Zero T] (s : PointSegmentSignal T)
    (point : T) (value : Bool) : PointSegmentSignal T :=
  -- 1. [cur,i] = priv_atIdx(obj,point)
  let cur := (s.atIdx point).1
  let i := (s.atIdx point).2
  if cur = value then s
  else if s.timePoints.getD (i - 1) 0 = point then
    -- 2. the point is a time point: remove it if it then matches both intervals, else set it
    if 1 < i ∧ s.precIntervalValue i = value ∧ s.succIntervalValue i = value then
      ⟨s.timePoints.eraseIdx (i - 1), (s.values.take (2 * i - 2)) ++ s.values.drop (2 * i)⟩
    else ⟨s.timePoints, s.values.set (2 * i - 2) value⟩
  else
    -- 3. insert a new point inside the interval
    ⟨s.timePoints.take i ++ point :: s.timePoints.drop i,
      s.values.take (2 * i) ++ value :: cur :: s.values.drop (2 * i)⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
