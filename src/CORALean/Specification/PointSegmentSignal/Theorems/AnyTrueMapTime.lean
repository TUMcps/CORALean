module

public import CORALean.Global.Float.Instances.Real.Instances
public import CORALean.Global.Float.TimeOrder
public import CORALean.Specification.PointSegmentSignal.Operations.AnyTrue
public import CORALean.Specification.PointSegmentSignal.Operations.Basic

@[expose] public section

/-!
# Whether a value holds somewhere at a float time type, read as reals

Over a float scalar `𝕋` `anyTrue` finds the values within the bounds by exact comparisons of the
time points with them (`TimeOrder`), so the signal read as reals, between the bounds read as reals,
gives the float answer.

## Inputs
* `s` – signal
* `lb` – lower bound
* `ub` – upper bound, or `inf`
* `lc` – whether the lower end is closed
* `rc` – whether the upper end is closed
* `cond` – condition on values

## Hypotheses
* none

## Conclusion
* the answer on the signal and bounds read as reals is the float one
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

omit [ExactLe 𝕋] in
/-- The `k`-th time point, `0` past the end, read as a real. -/
private theorem PointSegmentSignal.aux_getD_mapTime' (s : PointSegmentSignal 𝕋) (k : ℕ) :
    (s.mapTime toReal).timePoints.getD k 0 = toReal (s.timePoints.getD k 0) := by
  rw [← toReal_zero_eq (𝕋 := 𝕋), List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD]
  simp only [PointSegmentSignal.mapTime, List.getElem?_map]
  cases s.timePoints[k]? <;> rfl

/-- The first relevant value is found alike on the float and the real time points. -/
private theorem PointSegmentSignal.aux_relevantStart_mapTime (s : PointSegmentSignal 𝕋) (lb : 𝕋)
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
  simp only [hn, PointSegmentSignal.aux_getD_mapTime', hv]

/-- The last relevant value is found alike on the float and the real time points. -/
private theorem PointSegmentSignal.aux_relevantStop_mapTime (s : PointSegmentSignal 𝕋)
    (ub : WithTop 𝕋) (rc : Bool) : -- --- CONCL ---
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
  simp only [hn, PointSegmentSignal.aux_getD_mapTime', he]


-- =======================================  MAIN THEOREM  ======================================= --

theorem PointSegmentSignal.anyTrue_mapTime (s : PointSegmentSignal 𝕋) (lb : 𝕋)
    (ub : WithTop 𝕋) (lc rc : Bool) (cond : Bool → Bool) :
    (s.mapTime toReal).anyTrue (toReal lb) (ub.map toReal) lc rc cond =
      s.anyTrue lb ub lc rc cond := by
  -- the same values between the same indices
  unfold PointSegmentSignal.anyTrue
  rw [PointSegmentSignal.aux_relevantStart_mapTime, PointSegmentSignal.aux_relevantStop_mapTime]
  rfl

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
