module

public import CORALean.Specification.PointSegmentSignal.Theorems.SetMapTime
public import CORALean.Specification.TentativeKleeneSignal.Operations.Basic
public import CORALean.Specification.TentativeKleeneSignal.Operations.Observe

@[expose] public section

/-!
# Observing a value at a float time type, read as reals

Over a float scalar `𝕋` an observation sets the parts it allows on the interval exactly
(`PointSegmentSignal.set_mapTime`), so the float result read as reals is the observation of the
interval the float one denotes on the signal read as reals.

## Inputs
* `s` – signal
* `I` – time interval
* `value` – value observed

## Hypotheses
* none

## Conclusion
* observing commutes with reading the time points as reals
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

theorem TentativeKleeneSignal.observe_mapTime (s : TentativeKleeneSignal 𝕋) (I : STLInterval 𝕋)
    (value : Kleene) : (s.observe I value).mapTime toReal =
      (s.mapTime toReal).observe I.toRealInterval value := by
  cases value <;>
    simp only [TentativeKleeneSignal.observe, TentativeKleeneSignal.mapTime,
      PointSegmentSignal.set_mapTime]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
