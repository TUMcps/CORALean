module

public import CORALean.Global.Float.Instances.Real.Instances
public import CORALean.Global.Float.TimeOrder
public import CORALean.Specification.FourValuedSignal.Operations.Basic
public import CORALean.Specification.KleeneSignal.Theorems.EqMapTime
public import CORALean.Specification.PointSegmentSignal.Theorems.EqMapTime

@[expose] public section

/-!
# Equality of float four-valued signals, read as reals

Over a float scalar `𝕋` `eq` compares the time points of both parts by the reals they denote
(`TimeOrder.Eqv`), so the signals read as reals compare as the float ones, and a float `true` is
equality of the signals read as reals.

## Inputs
* `a` – first signal
* `b` – second signal

## Hypotheses
* none

## Conclusion
* the comparison of the signals read as reals is the float one
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       26-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ExactLe 𝕋]


-- =======================================  MAIN THEOREM  ======================================= --

theorem FourValuedSignal.eq_mapTime (a b : FourValuedSignal 𝕋) :
    (a.mapTime toReal).eq (b.mapTime toReal) = a.eq b := by
  -- both parts compare as the reals the time points denote
  unfold FourValuedSignal.eq FourValuedSignal.mapTime
  rw [KleeneSignal.eq_mapTime, PointSegmentSignal.eq_mapTime]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
