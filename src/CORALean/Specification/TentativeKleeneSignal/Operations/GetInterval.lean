module

public import CORALean.Specification.FourValuedSignal.Operations.Basic
public import CORALean.Specification.STLInterval.Operations.ToLeft
public import CORALean.Specification.TentativeKleeneSignal.Operations.Basic
public import CORALean.Specification.TentativeKleeneSignal.Operations.ToFourValued

@[expose] public section

/-!
# The conclusive part of a tentative signal on an interval

`sig = getInterval(obj,interval)` of `tentativeKleeneSignal.m`: everything outside the interval is
made invalid, the rest read as a four-valued signal; the empty interval gives the inconclusive
signal. `isemptyobject(interval)` is the case where `toLeft` has nothing to return.

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

/-- `sig = getInterval(obj,interval)`. -/
noncomputable def TentativeKleeneSignal.getInterval (s : TentativeKleeneSignal ℝ)
    (I : STLInterval) : FourValuedSignal ℝ :=
  match I.toLeft, I.toRight with
  | some left, some right =>
    -- 1. obj = obj.setInvalid(left); obj = obj.setInvalid(right)
    let obj := (s.setInvalid left).setInvalid right
    -- 2. sig = obj.toFourValued()
    obj.toFourValued
  -- `isemptyobject(interval)`: the inconclusive signal
  | _, _ => FourValuedSignal.uniformSignal FourValued.ii

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
