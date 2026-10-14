module

public import CORALean.Specification.PointSegmentSignal.Operations.Basic
public import Mathlib.Order.WithBot

@[expose] public section

/-!
# The value and index at a time

`[val,i] = priv_atIdx(obj,time)` of `pointSegmentSignal`: `i` counts (from `1`) the time points `≤
time` (`time` may be `inf`), `val` is the point value if the last of them is `time`, else the value
of the interval after it.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `[val,i] = priv_atIdx(obj,time)`. -/
def PointSegmentSignal.atIdx {T : Type} [LinearOrder T] [Zero T] (s : PointSegmentSignal T)
    (time : WithTop T) : Bool × ℕ :=
  -- i = find(obj.timePoints <= time,1,'last')
  let i := (s.timePoints.takeWhile (fun x : T => (x : WithTop T) ≤ time)).length
  -- the point value if timePoints(i) == time, else the following interval value
  (if ((s.timePoints.getD (i - 1) 0 : T) : WithTop T) = time then s.pointValue i
    else s.succIntervalValue i, i)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
