module

public import CORALean.Specification.KleeneSignal.KleeneSignal
public import CORALean.Specification.PointSegmentSignal.Operations.FindIntervals
public import CORALean.Specification.PointSegmentSignal.Operations.Set

@[expose] public section

/-!
# A three-valued signal as a Boolean one

`sig = toBoolSignal(obj,mapUnknownTo)` of `kleeneSignal.m`: the Boolean part with every interval
where the signal is unknown set to `mapUnknownTo`. Without an argument CORA throws if some value is
unknown; that call is `toBoolSignal?` (`none` for the error).

Refinement pending: CORA computes this in doubles, and its refinement generic over `𝕋` (time
stamps over `𝕋`, rounded outward) is not yet written.

## Inputs
* `s` – three-valued signal
* `mapUnknownTo` – Boolean for unknown times

## Output
* the Boolean signal
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `sig = toBoolSignal(obj,mapUnknownTo)`. -/
noncomputable def KleeneSignal.toBoolSignal (s : KleeneSignal ℝ) (mapUnknownTo : Bool) :
    PointSegmentSignal ℝ :=
  -- 1. intervals = obj.isUnknown.findIntervals()
  let intervals := s.isUnknown.findIntervals
  -- 2. sig = sig.set(intervals(i),mapUnknownTo) for each interval
  intervals.foldl (fun sig I => sig.set I mapUnknownTo) s.signal

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
