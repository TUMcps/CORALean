module

public import CORALean.Specification.FourValuedSignal.FourValuedSignal
public import CORALean.Specification.FourValuedSignal.Operations.Basic
public import CORALean.Specification.Kleene.Kleene
public import CORALean.Specification.KleeneSignal.Operations.Basic
public import CORALean.Specification.PointSegmentSignal.Operations.FindIntervals

@[expose] public section

/-!
# A four-valued signal as a three-valued one

`sig = toKleeneSignal(obj,mapInconclusiveTo)` of `fourValuedSignal.m`: the Kleene part with every
interval where the signal is inconclusive set to `mapInconclusiveTo`. Without an argument CORA
throws if some value is inconclusive; that call is `toKleeneSignal?` (`none` for the error).

Refinement pending: CORA computes this in doubles, and its refinement generic over `𝕋` (time
stamps over `𝕋`, rounded outward) is not yet written.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `sig = toKleeneSignal(obj,mapInconclusiveTo)`. -/
noncomputable def FourValuedSignal.toKleeneSignal (s : FourValuedSignal ℝ)
    (mapInconclusiveTo : Kleene) : KleeneSignal ℝ :=
  -- 1. intervals = obj.isInconclusive.findIntervals()
  let intervals := s.isInconclusive.findIntervals
  -- 2. sig = sig.set(intervals(i),mapInconclusiveTo) for each interval
  intervals.foldl (fun sig I => sig.set I mapInconclusiveTo) s.signal

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
