module

public import CORALean.Global.Float.Instances.Real.Instances
public import CORALean.Global.Float.TimeOrder
public import CORALean.Global.IsEqvTop
public import CORALean.Specification.PointSegmentSignal.Operations.Basic
public import CORALean.Specification.PointSegmentSignal.Operations.Indicator
public import CORALean.Specification.PointSegmentSignal.Operations.IndicatorBounds
public import CORALean.Specification.STLInterval.Operations.ToRealInterval

@[expose] public section

/-!
# The indicator of an interval at a float time type, read as reals

Over a float scalar `𝕋` the indicator of a float `stlInterval`, read through `toReal`, is the
indicator of the interval it denotes (`toRealInterval`): the float signal is exact.

## Inputs
* `I` – time interval
* `val` – value on the interval
* `default` – value elsewhere

## Hypotheses
* none

## Conclusion
* the float indicator, read as reals, is the indicator of the denoted interval
-/

-- Authors:       Claude Opus 5.5
-- Written:       23-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ExactLe 𝕋]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The indicator of float bounds, read as reals, is the indicator of the bounds they denote. -/
theorem PointSegmentSignal.aux_indicatorBounds_mapTime (lb : 𝕋) (ub : WithTop 𝕋)
    (lc rc val default : Bool) : -- --- CONCL ---
    (PointSegmentSignal.indicatorBounds lb ub lc rc val default).mapTime toReal =
      PointSegmentSignal.indicatorBounds (toReal lb) (ub.map toReal) lc rc val
        default := by -- --- PROOF ---
  -- every condition on the real bounds is the one on the float bounds
  have hlt : ub.map toReal < ((toReal lb : ℝ) : WithTop ℝ) ↔ ub < (lb : WithTop 𝕋) := by
    cases ub with
    | top => exact iff_of_false (WithTop.not_top_lt _) (WithTop.not_top_lt _)
    | coe a =>
      show ((toReal a : ℝ) : WithTop ℝ) < _ ↔ _
      rw [WithTop.coe_lt_coe, WithTop.coe_lt_coe]; exact Iff.rfl
  have heq : TimeOrder.IsEqvTop (ub.map toReal) ((toReal lb : ℝ) : WithTop ℝ) ↔
      TimeOrder.IsEqvTop ub (lb : WithTop 𝕋) := by
    cases ub <;> exact Iff.rfl
  have heq' : TimeOrder.IsEqvTop ((toReal lb : ℝ) : WithTop ℝ) (ub.map toReal) ↔
      TimeOrder.IsEqvTop (lb : WithTop 𝕋) ub := by
    cases ub <;> exact Iff.rfl
  have htop : ub.map toReal = ⊤ ↔ ub = ⊤ := by cases ub <;> simp
  have hd : (ub.map toReal).untopD 0 = toReal (ub.untopD 0) := by
    cases ub <;> simp [toReal_zero_eq]
  have h0 : (0 : ℝ) < toReal lb ↔ (0 : 𝕋) < lb := by rw [← toReal_zero_eq (𝕋 := 𝕋)]; exact Iff.rfl
  -- both sides unfolded: the same conditions, the time points mapped one by one
  unfold PointSegmentSignal.indicatorBounds STLInterval.emptyBounds
  simp only [hlt, heq, heq', ne_eq, htop, hd, h0]
  rw [apply_ite (PointSegmentSignal.mapTime toReal)]
  congr 1
  · simp [PointSegmentSignal.mapTime, toReal_zero_eq]
  · simp only [PointSegmentSignal.mapTime, apply_ite (List.map toReal), List.map_append,
      List.map_cons, List.map_nil, toReal_zero_eq]


-- =======================================  MAIN THEOREM  ======================================= --

theorem PointSegmentSignal.indicator_mapTime
    (I : STLInterval 𝕋) (val default : Bool) : -- --- CONCL ---
    (PointSegmentSignal.indicator I val default).mapTime toReal =
      PointSegmentSignal.indicator I.toRealInterval val default := by -- --- PROOF ---
  -- the indicator of the bounds read as reals; the bounds of the interval read as reals
  rw [PointSegmentSignal.indicator, PointSegmentSignal.aux_indicatorBounds_mapTime]
  cases I with
  | empty =>
    simp [STLInterval.toRealInterval, PointSegmentSignal.indicator, STLInterval.lowerBound,
      STLInterval.upperBound, STLInterval.lowerClosed, STLInterval.upperClosed, toReal_zero]
  | nonempty l u lc rc _ _ _ =>
    cases u <;> rfl

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
