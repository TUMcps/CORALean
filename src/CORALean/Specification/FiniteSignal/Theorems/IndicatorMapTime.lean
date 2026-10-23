module

public import CORALean.Specification.FiniteSignal.Operations.Indicator
public import CORALean.Specification.FiniteSignal.Theorems.MkMapTime

@[expose] public section

/-!
# The indicator signal at a float time type, read as reals

Over a float scalar `𝕋` the five cases of `indicator` compare the duration and the bounds exactly
(`TimeOrder`), so the float indicator read through `toReal` is the indicator of the reals they
denote, and both throw together.

## Inputs
* `dur` – signal duration
* `lo` – interval lower bound
* `hi` – interval upper bound
* `val` – value on the interval

## Hypotheses
* none

## Conclusion
* the float indicator, read as reals, is the real indicator
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

theorem FiniteSignal.indicator?_mapTime (dur lo hi : 𝕋) (val : Bool) :
    (FiniteSignal.indicator? dur lo hi val).map (FiniteSignal.mapTime toReal) =
      FiniteSignal.indicator? (toReal dur) (toReal lo) (toReal hi) val := by
  unfold FiniteSignal.indicator?
  simp only [le_iff_toReal_le (𝕋 := 𝕋), toReal_zero_eq (𝕋 := 𝕋)]
  split_ifs <;> simp [FiniteSignal.mk?_mapTime]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
