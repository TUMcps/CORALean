module

public import CORALean.Global.Float.Instances.Real.Instances
public import CORALean.Global.Float.TimeOrder
public import CORALean.Global.IsEqvTop
public import CORALean.Specification.PointSegmentSignal.Operations.RelevantStop
public import CORALean.Specification.PointSegmentSignal.Theorems.TimePointsGetDMapTime

@[expose] public section

/-!
# The last relevant value at a float time type, read as reals

Over a float scalar `𝕋` `relevantStop` counts the time points up to the upper bound by exact
comparisons (`TimeOrder`), so the signal read as reals, with the bound read as a real, finds the
same index.

## Inputs
* `s` – signal
* `ub` – upper bound, or `inf`
* `rc` – whether the upper end is closed

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

theorem PointSegmentSignal.relevantStop_mapTime (s : PointSegmentSignal 𝕋) (ub : WithTop 𝕋)
    (rc : Bool) : -- --- CONCL ---
    (s.mapTime toReal).relevantStop (ub.map toReal) rc = s.relevantStop ub rc := by -- --- PROOF ---
  -- a point is below the bound exactly when the real it denotes is
  have hle : ∀ x : 𝕋, ((toReal x : ℝ) : WithTop ℝ) ≤ ub.map toReal ↔ (x : WithTop 𝕋) ≤ ub :=
    fun x => by
      cases ub with
      | top => exact iff_of_true le_top le_top
      | coe a =>
        show ((toReal x : ℝ) : WithTop ℝ) ≤ ((toReal a : ℝ) : WithTop ℝ) ↔ _
        rw [WithTop.coe_le_coe, WithTop.coe_le_coe]; exact Iff.rfl
  have hn : ((s.mapTime toReal).timePoints.takeWhile
      (fun x : ℝ => (x : WithTop ℝ) ≤ ub.map toReal)).length =
      (s.timePoints.takeWhile (fun x : 𝕋 => (x : WithTop 𝕋) ≤ ub)).length := by
    simp only [PointSegmentSignal.mapTime]
    rw [List.takeWhile_map, List.length_map]
    exact congrArg List.length (congrArg (List.takeWhile · s.timePoints)
      (funext fun x => decide_eq_decide.mpr (hle x)))
  have he : ∀ y : 𝕋, TimeOrder.IsEqvTop ((toReal y : ℝ) : WithTop ℝ) (ub.map toReal) ↔
      TimeOrder.IsEqvTop (y : WithTop 𝕋) ub := fun y => by
    cases ub <;> exact Iff.rfl
  -- so the same count and the same test at its end
  unfold PointSegmentSignal.relevantStop
  simp only [hn, PointSegmentSignal.timePoints_getD_mapTime, he]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
