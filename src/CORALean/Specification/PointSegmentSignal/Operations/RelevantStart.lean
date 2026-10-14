module

public import CORALean.Specification.PointSegmentSignal.Operations.Basic
public import Mathlib.Order.WithBot

@[expose] public section

/-!
# The first value index in an interval

`start` of `priv_relevantValueIdx(obj,interval)` in `pointSegmentSignal`, for the lower bound
`lb`: the index (from `1`) of the first stored value that the signal takes at a time of the
interval. A point equal to the lower end counts only when that end is closed.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `[start,stop] = priv_relevantValueIdx(obj,interval)`, the `start`. -/
def PointSegmentSignal.relevantStart {T : Type} [LinearOrder T] [Zero T] (s : PointSegmentSignal T)
    (lb : T) (lc : Bool) : ℕ :=
  -- i = find(obj.timePoints <= lb,1,'last')
  let i := (s.timePoints.takeWhile (· ≤ lb)).length
  -- at the lower end the point value, if that end is closed
  if s.timePoints.getD (i - 1) 0 = lb ∧ lc = true then 2 * i - 1 else 2 * i

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
