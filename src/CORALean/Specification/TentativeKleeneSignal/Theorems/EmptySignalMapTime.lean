module

public import CORALean.Specification.PointSegmentSignal.Theorems.IndicatorMapTime
public import CORALean.Specification.STLInterval.Theorems.StlIntervalToRealInterval
public import CORALean.Specification.TentativeKleeneSignal.Operations.Basic

@[expose] public section

/-!
# The empty tentative signal at a float time type, read as reals

Over a float scalar `𝕋` both parts of `emptySignal` are indicators of `[0, ∞)`, built by the
constructor from the bound `0`, which denotes `0`; read through `toReal` the signal is the real
`emptySignal`.

## Inputs
* none

## Hypotheses
* none

## Conclusion
* the float empty signal, read as reals, is the real one
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

theorem TentativeKleeneSignal.emptySignal_mapTime :
    (TentativeKleeneSignal.emptySignal (𝕋 := 𝕋)).mapTime toReal =
      TentativeKleeneSignal.emptySignal := by
  simp only [TentativeKleeneSignal.emptySignal, TentativeKleeneSignal.mapTime,
    PointSegmentSignal.indicator_mapTime, STLInterval.stlInterval_toRealInterval,
    WithTop.map_top, toReal_zero_eq]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
