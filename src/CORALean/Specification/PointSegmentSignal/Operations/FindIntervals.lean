module

public import CORALean.Specification.PointSegmentSignal.Operations.FindIntervalsBounds
public import CORALean.Specification.STLInterval.Operations.Basic
public import CORALean.Specification.STLInterval.Operations.StlIntervalBounds

@[expose] public section

/-!
# The intervals where a signal's values satisfy a condition, as intervals

`intervals = findIntervals(obj,cond)` of `pointSegmentSignal`: the maximal intervals of time at
which the signal has a value satisfying `cond` (by default, `true`), as the `stlInterval`s of the
bounds `findIntervalsBounds` computes.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `intervals = findIntervals(obj,cond)`. -/
noncomputable def PointSegmentSignal.findIntervals (s : PointSegmentSignal ℝ)
    (cond : Bool → Bool := id) : List STLInterval :=
  (s.findIntervalsBounds cond).map
    (fun b => STLInterval.stlIntervalBounds b.1 b.2.1 b.2.2.1 b.2.2.2)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
