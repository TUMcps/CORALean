module

public import CORALean.Specification.FourValuedSignal.Operations.FindIntervals
public import CORALean.Specification.FourValuedSignal.Operations.ToKleeneSignal
public import CORALean.Specification.FourValuedSignal.Theorems.ToKleeneSignalMapTime
public import CORALean.Specification.KleeneSignal.Theorems.FindIntervalsMapTime
public import CORALean.Specification.KleeneSignal.Theorems.SetMapTime
public import CORALean.Specification.PointSegmentSignal.Theorems.FindIntervalsMapTime

@[expose] public section

/-!
# The intervals of a four-valued value at a float time type, read as reals

Over a float scalar `𝕋` the intervals are found on the inconclusive part or on a Kleene signal
made from the four-valued one, both exact, so the float intervals read as reals are those of the
signal read as reals.

## Inputs
* `s` – signal
* `match_` – value looked for

## Hypotheses
* none

## Conclusion
* the float intervals, read as reals, are those of the signal read as reals
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

theorem FourValuedSignal.findIntervals_mapTime (s : FourValuedSignal 𝕋) (match_ : FourValued) :
    (s.findIntervals match_).map STLInterval.toRealInterval =
      (s.mapTime toReal).findIntervals match_ := by
  cases match_ <;>
    (simp only [FourValuedSignal.findIntervals, PointSegmentSignal.findIntervals_mapTime,
      KleeneSignal.findIntervals_mapTime, FourValuedSignal.toKleeneSignal_mapTime]; try rfl)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
