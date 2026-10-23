module

public import CORALean.Specification.FourValuedSignal.Theorems.IndicatorMapTime
public import CORALean.Specification.OnlineAnalyzerNode.Operations.Basic

@[expose] public section

/-!
# The initial signal of a node at a float time type, read as reals

Over a float scalar `𝕋` the constant signal a node starts with is the indicator of the empty
interval, exact as every indicator is, so read through `toReal` it is the real initial signal.

## Inputs
* `k` – node kind

## Hypotheses
* none

## Conclusion
* the float initial signal, read as reals, is the real one
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

theorem OnlineAnalyzerNode.initSignal_mapTime (k : OnlineAnalyzerNode.Kind) :
    (OnlineAnalyzerNode.initSignal (𝕋 := 𝕋) k).mapTime toReal =
      OnlineAnalyzerNode.initSignal k := by
  rw [OnlineAnalyzerNode.initSignal, FourValuedSignal.uniformSignal,
    FourValuedSignal.indicator_mapTime]
  rfl

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
