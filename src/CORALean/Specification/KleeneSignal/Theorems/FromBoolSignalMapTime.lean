module

public import CORALean.Specification.KleeneSignal.Operations.Basic
public import CORALean.Specification.PointSegmentSignal.Theorems.IndicatorMapTime

@[expose] public section

/-!
# A Boolean signal made a Kleene signal at a float time type, read as reals

Over a float scalar `𝕋` the unknown part `fromBoolSignal` adds is the indicator of the empty
interval, exact as every indicator is, so the result read through `toReal` is the real Boolean
signal made a Kleene signal.

## Inputs
* `b` – Boolean signal

## Hypotheses
* none

## Conclusion
* the float Kleene signal, read as reals, is the one made from the real Boolean signal
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

theorem KleeneSignal.fromBoolSignal_mapTime (b : PointSegmentSignal 𝕋) :
    (KleeneSignal.fromBoolSignal b).mapTime toReal =
      KleeneSignal.fromBoolSignal (b.mapTime toReal) := by
  simp only [KleeneSignal.fromBoolSignal, KleeneSignal.mapTime,
    PointSegmentSignal.indicator_mapTime]
  rfl

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
