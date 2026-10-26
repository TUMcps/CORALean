module

public import CORALean.Global.Float.Instances.Real.Instances
public import CORALean.Global.Float.TimeOrder
public import CORALean.Specification.PointSegmentSignal.Operations.RelevantStart
public import CORALean.Specification.PointSegmentSignal.Theorems.TimePointsGetDMapTime

@[expose] public section

/-!
# The first relevant value at a float time type, read as reals

Over a float scalar `𝕋` `relevantStart` counts the time points up to the lower bound by exact
comparisons (`TimeOrder`), so the signal read as reals, with the bound read as a real, finds the
same index.

## Inputs
* `s` – signal
* `lb` – lower bound
* `lc` – whether the lower end is closed

## Hypotheses
* none

## Conclusion
* the index on the signal and bound read as reals is the float one
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

theorem PointSegmentSignal.relevantStart_mapTime (s : PointSegmentSignal 𝕋) (lb : 𝕋)
    (lc : Bool) : -- --- CONCL ---
    (s.mapTime toReal).relevantStart (toReal lb) lc = s.relevantStart lb lc := by -- --- PROOF ---
  -- as many points are at most the bound, the last one compared exactly
  have hn : ((s.mapTime toReal).timePoints.takeWhile (· ≤ toReal lb)).length =
      (s.timePoints.takeWhile (· ≤ lb)).length := by
    simp only [PointSegmentSignal.mapTime]
    rw [List.takeWhile_map, List.length_map]
    exact congrArg List.length (congrArg (List.takeWhile · s.timePoints)
      (funext fun x => decide_eq_decide.mpr Iff.rfl))
  have hv : ∀ a b : 𝕋, TimeOrder.Eqv (toReal a) (toReal b) ↔ TimeOrder.Eqv a b :=
    fun _ _ => Iff.rfl
  unfold PointSegmentSignal.relevantStart
  simp only [hn, PointSegmentSignal.timePoints_getD_mapTime, hv]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
