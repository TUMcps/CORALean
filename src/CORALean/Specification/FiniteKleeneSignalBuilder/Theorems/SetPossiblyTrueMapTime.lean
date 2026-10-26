module

public import CORALean.Global.Float.Instances.Real.Instances
public import CORALean.Global.Float.TimeOrder
public import CORALean.Specification.FiniteKleeneSignalBuilder.Operations.Basic
public import CORALean.Specification.FiniteKleeneSignalBuilder.Operations.SetPossiblyTrue
public import CORALean.Specification.FiniteSignal.Theorems.CombineMapTime
public import CORALean.Specification.FiniteSignal.Theorems.IndicatorMapTime

@[expose] public section

/-!
# Marking possibly true on a float builder, read as reals

Over a float scalar `𝕋` `setPossiblyTrue?` builds the indicator of the interval and combines it
with the signal by exact comparisons of time stamps (`TimeOrder`), so the float result read as
reals is `setPossiblyTrue?` of the builder read as reals on the reals the bounds denote, and both
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

theorem FiniteKleeneSignalBuilder.setPossiblyTrue?_mapTime
    (obj : FiniteKleeneSignalBuilder 𝕋) (lo hi : 𝕋) : -- --- CONCL ---
    (obj.setPossiblyTrue? lo hi).map (FiniteKleeneSignalBuilder.mapTime toReal) =
      (obj.mapTime toReal).setPossiblyTrue? (toReal lo) (toReal hi) := by -- --- PROOF ---
  -- the duration, the indicator and the combination are those of the reals
  have hd : (obj.mapTime toReal).possiblyTrueSignal.duration =
      toReal obj.possiblyTrueSignal.duration :=
    FiniteSignal.duration_mapTime toReal toReal_zero_eq _
  unfold FiniteKleeneSignalBuilder.setPossiblyTrue?
  dsimp only
  have hind := FiniteSignal.indicator?_mapTime obj.possiblyTrueSignal.duration lo hi true
  rw [hd, ← hind]
  cases FiniteSignal.indicator? obj.possiblyTrueSignal.duration lo hi true with
  | none => rfl
  | some ind =>
    have hc := FiniteSignal.combine?_mapTime (· || ·) [obj.possiblyTrueSignal, ind]
    simp only [List.map_cons, List.map_nil] at hc
    simp only [Option.map_some, Option.bind_some]
    show _ = (FiniteSignal.combine? _
      [obj.possiblyTrueSignal.mapTime toReal, ind.mapTime toReal]).map _
    rw [← hc]
    cases FiniteSignal.combine? (· || ·) [obj.possiblyTrueSignal, ind] <;> rfl

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
