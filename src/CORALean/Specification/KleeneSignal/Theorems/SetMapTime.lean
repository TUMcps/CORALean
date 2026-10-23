module

public import CORALean.Specification.KleeneSignal.Operations.Basic
public import CORALean.Specification.PointSegmentSignal.Theorems.SetMapTime

@[expose] public section

/-!
# Setting a Kleene value in an interval at a float time type, read as reals

Over a float scalar `𝕋` both parts are set as Boolean signals are, exactly
(`PointSegmentSignal.set_mapTime`), so the float result read through `toReal` is the signal read as
reals with the value set on the interval the float one denotes.

## Inputs
* `s` – signal
* `I` – time interval
* `value` – value to set

## Hypotheses
* none

## Conclusion
* setting the value commutes with reading the time points as reals
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

theorem KleeneSignal.set_mapTime (s : KleeneSignal 𝕋) (I : STLInterval 𝕋) (value : Kleene) :
    (s.set I value).mapTime toReal = (s.mapTime toReal).set I.toRealInterval value := by
  simp only [KleeneSignal.set, KleeneSignal.mapTime, PointSegmentSignal.set_mapTime]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
