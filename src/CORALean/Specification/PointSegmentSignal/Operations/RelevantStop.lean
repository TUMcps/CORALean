module

public import CORALean.Specification.PointSegmentSignal.Operations.Basic
public import Mathlib.Order.WithBot

@[expose] public section

/-!
# The last value index in an interval

`stop` of `priv_relevantValueIdx(obj,interval)` in `pointSegmentSignal`, for the upper bound
`ub`: the index (from `1`) of the last stored value that the signal takes at a time of the
interval. A point equal to the upper end counts only when that end is closed; an infinite end is
never reached by a point.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `[start,stop] = priv_relevantValueIdx(obj,interval)`, the `stop`. -/
def PointSegmentSignal.relevantStop {T : Type} [LinearOrder T] [Zero T] (s : PointSegmentSignal T)
    (ub : WithTop T) (rc : Bool) : ℕ :=
  -- j = find(obj.timePoints <= ub,1,'last')
  let j := (s.timePoints.takeWhile (fun x : T => (x : WithTop T) ≤ ub)).length
  -- at the upper end only the point value, if that end is closed
  if ((s.timePoints.getD (j - 1) 0 : T) : WithTop T) = ub then
    (if rc = true then 2 * j - 1 else 2 * j - 2)
  else 2 * j

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
