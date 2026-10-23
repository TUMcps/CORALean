module

public import CORALean.Specification.FourValuedSignal.Operations.Basic
public import CORALean.Specification.PointSegmentSignal.Theorems.AtMapTime

@[expose] public section

/-!
# The four-valued value at a time at a float time type, read as reals

Over a float scalar `𝕋` all three parts are read exactly (`PointSegmentSignal.at_mapTime`), so the
float signal read through `toReal` has, at the real a float time denotes, the float value there: a
float `tt` or `ff` is the verdict of the signal it denotes.

## Inputs
* `s` – signal
* `t` – time

## Hypotheses
* none

## Conclusion
* the signal read as reals has the float value at the real time
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

theorem FourValuedSignal.at_mapTime (s : FourValuedSignal 𝕋) (t : 𝕋) :
    (s.mapTime toReal).at (toReal t) = s.at t := by
  simp only [FourValuedSignal.at, KleeneSignal.at, FourValuedSignal.mapTime, KleeneSignal.mapTime,
    PointSegmentSignal.at_mapTime]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
