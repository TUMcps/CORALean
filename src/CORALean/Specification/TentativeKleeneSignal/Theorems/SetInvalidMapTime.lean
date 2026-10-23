module

public import CORALean.Specification.PointSegmentSignal.Theorems.SetMapTime
public import CORALean.Specification.TentativeKleeneSignal.Operations.Basic

@[expose] public section

/-!
# Ruling out an interval at a float time type, read as reals

Over a float scalar `𝕋` both parts are set to `false` as Boolean signals are, exactly
(`PointSegmentSignal.set_mapTime`), so the float result read through `toReal` is the signal read as
reals with the interval the float one denotes ruled out.

## Inputs
* `s` – signal
* `I` – time interval

## Hypotheses
* none

## Conclusion
* ruling out the interval commutes with reading the time points as reals
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

theorem TentativeKleeneSignal.setInvalid_mapTime (s : TentativeKleeneSignal 𝕋)
    (I : STLInterval 𝕋) :
    (s.setInvalid I).mapTime toReal = (s.mapTime toReal).setInvalid I.toRealInterval := by
  simp only [TentativeKleeneSignal.setInvalid, TentativeKleeneSignal.mapTime,
    PointSegmentSignal.set_mapTime]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
