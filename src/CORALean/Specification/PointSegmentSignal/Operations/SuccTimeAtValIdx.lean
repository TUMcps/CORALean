module

public import CORALean.Specification.PointSegmentSignal.Operations.Basic

@[expose] public section

/-!
# The time after a stored value

`[time,atPoint] = succTimeAtValIdx(obj,i)` of `pointSegmentSignal.m`: for the `i`-th stored value
(one-based), the time at which it ends, `inf` after the last time point, and whether that value is a
point value, so that its end is included.

## Inputs
* `T` – time type
* `s` – signal
* `i` – index of a stored value

## Output
* the time point after the value and whether it is a point value
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `[time,atPoint] = succTimeAtValIdx(obj,i)`: the time point after the `i`-th stored value. -/
def PointSegmentSignal.succTimeAtValIdx {T : Type} [Zero T] (s : PointSegmentSignal T) (i : ℕ) :
    WithTop T × Bool :=
  -- 1. ti = floor(i / 2) + 1, and the time `inf` if there is no such time point
  let time : WithTop T :=
    if i / 2 + 1 > s.length then ⊤ else ((s.timePoints.getD (i / 2) 0 : T) : WithTop T)
  -- 2. atPoint = mod(i,2) == 1
  (time, decide (i % 2 = 1))

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
