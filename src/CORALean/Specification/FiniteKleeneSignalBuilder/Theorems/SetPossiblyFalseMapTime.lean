module

public import CORALean.Global.Float.Instances.Real.Instances
public import CORALean.Global.Float.TimeOrder
public import CORALean.Specification.FiniteKleeneSignalBuilder.Operations.Basic
public import CORALean.Specification.FiniteKleeneSignalBuilder.Operations.SetPossiblyFalse
public import CORALean.Specification.FiniteSignal.Theorems.CombineMapTime
public import CORALean.Specification.FiniteSignal.Theorems.IndicatorMapTime

@[expose] public section

/-!
# Marking possibly false on a float builder, read as reals

Over a float scalar `𝕋` `setPossiblyFalse?` builds the indicator of the interval and combines it
with the signal by exact comparisons of time stamps (`TimeOrder`), so the float result read as
reals is `setPossiblyFalse?` of the builder read as reals on the reals the bounds denote, and both
throw together.

## Inputs
* `obj` – builder
* `lo` – interval lower bound
* `hi` – interval upper bound

## Hypotheses
* none

## Conclusion
* the float result, read as reals, is the real one
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

theorem FiniteKleeneSignalBuilder.setPossiblyFalse?_mapTime
    (obj : FiniteKleeneSignalBuilder 𝕋) (lo hi : 𝕋) : -- --- CONCL ---
    (obj.setPossiblyFalse? lo hi).map (FiniteKleeneSignalBuilder.mapTime toReal) =
      (obj.mapTime toReal).setPossiblyFalse? (toReal lo) (toReal hi) := by -- --- PROOF ---
  -- the duration, the indicator and the combination are those of the reals
  have hd : (obj.mapTime toReal).possiblyFalseSignal.duration =
      toReal obj.possiblyFalseSignal.duration :=
    FiniteSignal.duration_mapTime toReal toReal_zero_eq _
  unfold FiniteKleeneSignalBuilder.setPossiblyFalse?
  dsimp only
  have hind := FiniteSignal.indicator?_mapTime obj.possiblyFalseSignal.duration lo hi true
  rw [hd, ← hind]
  cases FiniteSignal.indicator? obj.possiblyFalseSignal.duration lo hi true with
  | none => rfl
  | some ind =>
    have hc := FiniteSignal.combine?_mapTime (· || ·) [obj.possiblyFalseSignal, ind]
    simp only [List.map_cons, List.map_nil] at hc
    simp only [Option.map_some, Option.bind_some]
    show _ = (FiniteSignal.combine? _
      [obj.possiblyFalseSignal.mapTime toReal, ind.mapTime toReal]).map _
    rw [← hc]
    cases FiniteSignal.combine? (· || ·) [obj.possiblyFalseSignal, ind] <;> rfl

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
