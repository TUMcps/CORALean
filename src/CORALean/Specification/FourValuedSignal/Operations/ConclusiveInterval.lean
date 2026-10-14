module

public import CORALean.Specification.FourValuedSignal.FourValuedSignal
public import CORALean.Specification.PointSegmentSignal.Operations.At
public import CORALean.Specification.PointSegmentSignal.Operations.Basic
public import CORALean.Specification.PointSegmentSignal.Operations.CutAtFirstFallingEdge
public import CORALean.Specification.PointSegmentSignal.Operations.FindLast
public import CORALean.Specification.PointSegmentSignal.Operations.Set
public import CORALean.Specification.STLInterval.Operations.Basic

@[expose] public section

/-!
# The initial interval where a four-valued signal is conclusive

`int = conclusiveInterval(obj,ignore)` of `fourValuedSignal.m`: the interval from `0` up to the
first time the signal is inconclusive outside `ignore`; empty if it is inconclusive at `0`. It is
closed at the end if the signal is conclusive there, and open, or unbounded, otherwise.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `int = conclusiveInterval(obj,ignore)`. -/
noncomputable def FourValuedSignal.conclusiveInterval (obj : FourValuedSignal ℝ)
    (ignore : STLInterval) : STLInterval :=
  -- 1. isConclusive = ~(obj.isInconclusive.set(ignore,false))
  let isConclusive := (obj.isInconclusive.set ignore false).not
  -- 2. if ~isConclusive.at(0), there is no conclusive time
  if isConclusive.at 0 = false then STLInterval.empty
  else
    -- 3. [time,inclusive] = isConclusive.cutAtFirstFallingEdge().findLast(true)
    let time := isConclusive.cutAtFirstFallingEdge.findLast true
    STLInterval.stlIntervalBounds 0 time.1 true time.2

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
