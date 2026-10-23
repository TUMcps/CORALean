module

public import CORALean.Global.IsEqvTop
public import CORALean.Specification.PointSegmentSignal.PointSegmentSignal
public import Mathlib.Order.Basic

@[expose] public section

/-!
# The stored value a time reads

`obj.at(time)` of `pointSegmentSignal` reads the point value at a time point and the following
interval value elsewhere. `cell` is the zero-based index of that value in `values`: `2k` at the
`k`-th time point and `2k + 1` between it and the next, the numbering `findIntervals` works in.

## Inputs
* `T` – time type
* `s` – signal
* `time` – time

## Output
* the index of the stored value read at the time
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The index in `values` of the value `at` reads at `time`. -/
def PointSegmentSignal.cell {T : Type} [TimeOrder T] (s : PointSegmentSignal T) (time : T) : ℕ :=
  -- 1. i = find(obj.timePoints <= time,1,'last'), zero-based
  let i := (s.timePoints.takeWhile (· ≤ time)).length - 1
  -- 2. the point value if timePoints(i) == time, else the following interval value
  if ∃ b ∈ s.timePoints[i]?, TimeOrder.Eqv b time then 2 * i else 2 * i + 1

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
