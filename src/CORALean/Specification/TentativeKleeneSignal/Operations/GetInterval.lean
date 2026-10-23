module

public import CORALean.Specification.FourValuedSignal.Operations.Basic
public import CORALean.Specification.STLInterval.Operations.ToLeft
public import CORALean.Specification.STLInterval.Operations.ToRight
public import CORALean.Specification.TentativeKleeneSignal.Operations.Basic
public import CORALean.Specification.TentativeKleeneSignal.Operations.ToFourValued

@[expose] public section

/-!
# The conclusive part of a tentative signal on an interval

`sig = getInterval(obj,interval)` of `tentativeKleeneSignal.m`: everything outside the interval is
made invalid, the rest read as a four-valued signal; the empty interval gives the inconclusive
signal. `isemptyobject(interval)` is the case where `toLeft` has nothing to return.

## Inputs
* `s` – tentative signal
* `I` – time interval

## Output
* the four-valued signal on the interval, inconclusive outside
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {𝕋 : Type} [Float.FloatOps 𝕋] [Float.SoundFloatArithmetic 𝕋] [Float.ExactLe 𝕋]
    [TimeOrder 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `sig = getInterval(obj,interval)`. -/
def TentativeKleeneSignal.getInterval (s : TentativeKleeneSignal 𝕋) (I : STLInterval 𝕋) :
    FourValuedSignal 𝕋 :=
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
