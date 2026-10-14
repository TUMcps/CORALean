module

public import CORALean.Specification.PointSegmentSignal.Operations.Basic
public import Mathlib.Order.WithBot

@[expose] public section

/-!
# The time of the next unconsumed point

`aux_time` of `combine.m`: the time of the signal's `idx`-th point, or `inf` once the signal has
been consumed. `inf` is `⊤` of `WithTop T`.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `aux_time(signal,idx)`. -/
def PointSegmentSignal.timeOrInf {T : Type} [Zero T] (s : PointSegmentSignal T) (idx : ℕ) :
    WithTop T :=
  if idx ≤ s.length then ((s.timePoints.getD (idx - 1) 0 : T) : WithTop T) else ⊤

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
