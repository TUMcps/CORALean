module

public import CORALean.Specification.PointSegmentSignal.Operations.FindIntervals
public import CORALean.Specification.PointSegmentSignal.Operations.IntervalUntil

@[expose] public section

/-!
# The until of two signals

`sig = until(lhs,interval,rhs)` of `pointSegmentSignal`: the until of the intervals where the
signals are `true`. At a time `t` it is `true` iff the right-hand side holds at some `t'` with `t' -
t` in the interval and the left-hand side holds strictly between `t` and `t'`.

Refinement pending: CORA computes this in doubles, and its refinement generic over `𝕋` (time
stamps over `𝕋`, rounded outward) is not yet written.

## Inputs
* `lhs` – left signal
* `interval` – time interval
* `rhs` – right signal

## Output
* the until signal
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `sig = until(lhs,interval,rhs)`. -/
noncomputable def PointSegmentSignal.until (lhs : PointSegmentSignal ℝ) (interval : STLInterval ℝ)
    (rhs : PointSegmentSignal ℝ) : PointSegmentSignal ℝ :=
  -- 1. find the positive intervals
  let lhsInt := lhs.findIntervals
  let rhsInt := rhs.findIntervals
  -- 2. set to true wherever we find a witness for until
  PointSegmentSignal.intervalUntil lhsInt interval rhsInt

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
