module

public import CORALean.Specification.KleeneSignal.Operations.Basic
public import CORALean.Specification.KleeneSignal.Operations.FindIntervals
public import CORALean.Specification.KleeneSignal.Operations.ToBoolSignal
public import CORALean.Specification.KleeneSignal.Theorems.ToBoolSignalMapTime
public import CORALean.Specification.PointSegmentSignal.Theorems.FindIntervalsMapTime
public import CORALean.Specification.PointSegmentSignal.Theorems.SetMapTime

@[expose] public section

/-!
# The intervals of a Kleene value at a float time type, read as reals

Over a float scalar `𝕋` the intervals are found on the unknown part or on a Boolean signal made
from the Kleene one, both exact, so the float intervals read as reals are those of the signal read
as reals.

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

theorem KleeneSignal.findIntervals_mapTime (s : KleeneSignal 𝕋) (match_ : Kleene) :
    (s.findIntervals match_).map STLInterval.toRealInterval =
      (s.mapTime toReal).findIntervals match_ := by
  cases match_ <;>
    (simp only [KleeneSignal.findIntervals, PointSegmentSignal.findIntervals_mapTime,
      KleeneSignal.toBoolSignal_mapTime]; try rfl)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
