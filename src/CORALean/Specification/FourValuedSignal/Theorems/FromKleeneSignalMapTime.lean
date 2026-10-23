module

public import CORALean.Specification.FourValuedSignal.Operations.Basic
public import CORALean.Specification.PointSegmentSignal.Theorems.IndicatorMapTime

@[expose] public section

/-!
# A Kleene signal made four-valued at a float time type, read as reals

Over a float scalar `𝕋` the inconclusive part `fromKleeneSignal` adds is the indicator of the
empty interval, exact as every indicator is, so the result read through `toReal` is the real
Kleene signal made four-valued.

## Inputs
* `k` – Kleene signal

## Hypotheses
* none

## Conclusion
* the float four-valued signal, read as reals, is the one made from the real Kleene signal
-/

-- Authors:       Claude Opus 5.5
-- Written:       23-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ExactLe 𝕋]


-- =======================================  MAIN THEOREM  ======================================= --

theorem FourValuedSignal.fromKleeneSignal_mapTime (k : KleeneSignal 𝕋) :
    (FourValuedSignal.fromKleeneSignal k).mapTime toReal =
      FourValuedSignal.fromKleeneSignal (k.mapTime toReal) := by
  simp only [FourValuedSignal.fromKleeneSignal, FourValuedSignal.mapTime,
    PointSegmentSignal.indicator_mapTime]
  rfl

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
