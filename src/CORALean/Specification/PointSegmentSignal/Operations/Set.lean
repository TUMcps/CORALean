module

public import CORALean.Specification.PointSegmentSignal.Operations.SetBounds
public import CORALean.Specification.STLInterval.Operations.Basic

@[expose] public section

/-!
# Setting the value in an interval

`set(obj,interval,value)` of `pointSegmentSignal.m` for a time type `ℝ` and an `stlInterval`: the
interval's bounds and closedness flags are read off (`lowerBound`, `upperBound`) and `setBounds`
does the work.

Refinement pending: CORA computes this in doubles, and its refinement generic over `𝕋` (time
stamps over `𝕋`, rounded outward) is not yet written.

## Inputs
* `s` – signal
* `I` – time interval
* `value` – value to set

## Output
* the signal with the value set on the interval
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `sig = set(obj,interval,value)`. -/
noncomputable def PointSegmentSignal.set (s : PointSegmentSignal ℝ) (I : STLInterval)
    (value : Bool) : PointSegmentSignal ℝ :=
  s.setBounds I.lowerBound I.upperBound I.lowerClosed I.upperClosed value

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
