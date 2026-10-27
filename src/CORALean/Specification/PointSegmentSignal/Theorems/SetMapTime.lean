module

public import CORALean.Global.Float.Instances.Real.Instances
public import CORALean.Global.Float.TimeOrder
public import CORALean.Specification.PointSegmentSignal.Operations.AtIdx
public import CORALean.Specification.PointSegmentSignal.Operations.Basic
public import CORALean.Specification.PointSegmentSignal.Operations.Set
public import CORALean.Specification.PointSegmentSignal.Operations.SetPoint
public import CORALean.Specification.STLInterval.Operations.ToRealInterval
public import Mathlib.Data.List.InsertIdx

@[expose] public section

/-!
# Setting the value in an interval at a float time type, read as reals

Over a float scalar `𝕋` every step of `set` finds and compares the time points exactly
(`TimeOrder`), so the float result read through `toReal` is the signal read as reals with the value
set on the interval the float one denotes (`toRealInterval`).

## Inputs
* `s` – signal
* `I` – time interval
* `value` – value to set

## Hypotheses
* none

## Conclusion
* setting the value commutes with reading the time points as reals
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

/-- The value and index `atIdx` finds are alike on the float and the real time points. -/
private theorem PointSegmentSignal.aux_atIdx_mapTime
    (s : PointSegmentSignal 𝕋) (time : WithTop 𝕋) : -- --- CONCL ---
    (s.mapTime toReal).atIdx (time.map toReal) = s.atIdx time := by -- --- PROOF ---
  -- a point is below the time exactly when the real it denotes is
  have hle : ∀ x : 𝕋, ((toReal x : ℝ) : WithTop ℝ) ≤ time.map toReal ↔
      (x : WithTop 𝕋) ≤ time := fun x => by
    cases time with
    | top => exact iff_of_true le_top le_top
    | coe a =>
      show ((toReal x : ℝ) : WithTop ℝ) ≤ ((toReal a : ℝ) : WithTop ℝ) ↔ _
      rw [WithTop.coe_le_coe, WithTop.coe_le_coe]; exact Iff.rfl
  -- so as many points are below it
  have hn : ((s.timePoints.map toReal).takeWhile
      (fun x : ℝ => (x : WithTop ℝ) ≤ time.map toReal)).length =
      (s.timePoints.takeWhile (fun x : 𝕋 => (x : WithTop 𝕋) ≤ time)).length := by
    rw [List.takeWhile_map, List.length_map]
    exact congrArg List.length (congrArg (List.takeWhile · s.timePoints)
      (funext fun x => decide_eq_decide.mpr (hle x)))
  -- the last of them is read as the real it denotes
  have hg : ∀ k, (s.timePoints.map toReal).getD k 0 = toReal (s.timePoints.getD k 0) := fun k => by
    rw [← toReal_zero_eq (𝕋 := 𝕋), List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
      List.getElem?_map]
    cases s.timePoints[k]? <;> rfl
  have he : ∀ y : 𝕋, TimeOrder.IsEqvTop ((toReal y : ℝ) : WithTop ℝ) (time.map toReal) ↔
      TimeOrder.IsEqvTop (y : WithTop 𝕋) time := fun y => by
    cases time <;> exact Iff.rfl
  unfold PointSegmentSignal.atIdx
  simp only [PointSegmentSignal.mapTime] at hn hg ⊢
  rw [hn, hg]
  simp only [he]
  rfl


/-- Setting the value at a point commutes with reading the time points as reals. -/
private theorem PointSegmentSignal.aux_setPoint_mapTime (s : PointSegmentSignal 𝕋) (point : 𝕋)
    (value : Bool) : -- --- CONCL ---
    (s.setPoint point value).mapTime toReal =
      (s.mapTime toReal).setPoint (toReal point) value := by -- --- PROOF ---
  -- the value and index found, and the point compared, are the float ones
  have ha := PointSegmentSignal.aux_atIdx_mapTime s (point : WithTop 𝕋)
  have hg : ∀ k, (s.timePoints.map toReal).getD k 0 = toReal (s.timePoints.getD k 0) := fun k => by
    rw [← toReal_zero_eq (𝕋 := 𝕋), List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
      List.getElem?_map]
    cases s.timePoints[k]? <;> rfl
  simp only [WithTop.map_coe] at ha
  -- unfolded, with the values next to the point the float ones
  unfold PointSegmentSignal.setPoint
  rw [ha]
  have hp : ∀ i, (s.mapTime toReal).precIntervalValue i = s.precIntervalValue i := fun _ => rfl
  have hs : ∀ i, (s.mapTime toReal).succIntervalValue i = s.succIntervalValue i := fun _ => rfl
  simp only [hp, hs]
  have hgi := hg ((s.atIdx point).2 - 1)
  simp only [PointSegmentSignal.mapTime] at hgi ⊢
  rw [hgi]
  -- the same case on both sides, the time points mapped one by one
  by_cases h1 : (s.atIdx point).1 = value
  · rw [if_pos h1, if_pos h1]
  · rw [if_neg h1, if_neg h1]
    by_cases h2 : TimeOrder.Eqv (s.timePoints.getD ((s.atIdx point).2 - 1) 0) point
    · rw [if_pos h2, if_pos (show TimeOrder.Eqv (toReal _) (toReal point) from h2)]
      split_ifs <;> simp [List.eraseIdx_map]
    · rw [if_neg h2, if_neg (show ¬ TimeOrder.Eqv (toReal _) (toReal point) from h2)]
      simp [List.map_take, List.map_drop]


omit [ExactLe 𝕋] in
/-- The `k`-th time point, `0` past the end, read as a real. -/
private theorem PointSegmentSignal.aux_getD_mapTime (s : PointSegmentSignal 𝕋) (k : ℕ) :
    (s.mapTime toReal).timePoints.getD k 0 = toReal (s.timePoints.getD k 0) := by
  rw [← toReal_zero_eq (𝕋 := 𝕋), List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD]
  simp only [PointSegmentSignal.mapTime, List.getElem?_map]
  cases s.timePoints[k]? <;> rfl

/-- Whether a new point is needed is decided alike on the float and the real time points. -/
private theorem PointSegmentSignal.aux_isNewPointOk_mapTime (s : PointSegmentSignal 𝕋) (i : ℕ)
    (p : 𝕋) (vals : List Bool) : -- --- CONCL ---
    (s.mapTime toReal).step_isNewPointOk i (toReal p) vals =
      s.step_isNewPointOk i p vals := by -- --- PROOF ---
  -- the values next to the point are the float ones, the point and `0` compared exactly
  have hp : (s.mapTime toReal).precIntervalValue i = s.precIntervalValue i := rfl
  have hs : (s.mapTime toReal).succIntervalValue i = s.succIntervalValue i := rfl
  have h0 : TimeOrder.Eqv (toReal p) (0 : ℝ) ↔ TimeOrder.Eqv p (0 : 𝕋) := by
    rw [← toReal_zero_eq (𝕋 := 𝕋)]; exact Iff.rfl
  unfold PointSegmentSignal.step_isNewPointOk
  rw [hp, hs, PointSegmentSignal.aux_getD_mapTime]
  by_cases h : TimeOrder.Eqv (s.timePoints.getD (i - 1) 0) p
  · rw [if_pos h, if_pos (show TimeOrder.Eqv (toReal _) (toReal p) from h)]
    exact decide_eq_decide.mpr (or_congr h0 Iff.rfl)
  · rw [if_neg h, if_neg (show ¬ TimeOrder.Eqv (toReal _) (toReal p) from h)]

/-- `set` on bounds commutes with reading the time points and the bounds as reals. -/
private theorem PointSegmentSignal.aux_setBounds_mapTime (s : PointSegmentSignal 𝕋) (lb : 𝕋)
    (ub : WithTop 𝕋) (lc rc value : Bool) : -- --- CONCL ---
    (s.step_setBounds lb ub lc rc value).mapTime toReal =
      (s.mapTime toReal).step_setBounds (toReal lb) (ub.map toReal) lc rc
        value := by -- --- PROOF ---
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
  -- the points found at both ends are the float ones
  have hal := PointSegmentSignal.aux_atIdx_mapTime s (lb : WithTop 𝕋)
  have hau := PointSegmentSignal.aux_atIdx_mapTime s ub
  have hs : ∀ j, (s.mapTime toReal).succIntervalValue j = s.succIntervalValue j := fun _ => rfl
  have hv : ∀ a b : 𝕋, TimeOrder.Eqv (toReal a) (toReal b) ↔ TimeOrder.Eqv a b :=
    fun _ _ => Iff.rfl
  simp only [WithTop.map_coe] at hal
  -- both sides unfolded: the same conditions, the time points mapped one by one
  unfold PointSegmentSignal.step_setBounds STLInterval.emptyBounds
  simp only [hlt, heq, heq', ne_eq, htop, hd, hal, hau, hs,
    PointSegmentSignal.aux_isNewPointOk_mapTime, PointSegmentSignal.aux_getD_mapTime, hv]
  rw [apply_ite (PointSegmentSignal.mapTime toReal)]
  congr 1
  rw [apply_ite (PointSegmentSignal.mapTime toReal), PointSegmentSignal.aux_setPoint_mapTime]
  congr 1
  simp only [PointSegmentSignal.mapTime, List.map_append, List.map_take, List.map_drop,
    apply_ite (List.map toReal), List.map_cons, List.map_nil]


-- =======================================  MAIN THEOREM  ======================================= --

theorem PointSegmentSignal.set_mapTime (s : PointSegmentSignal 𝕋) (I : STLInterval 𝕋)
    (value : Bool) : -- --- CONCL ---
    (s.set I value).mapTime toReal =
      (s.mapTime toReal).set I.toRealInterval value := by -- --- PROOF ---
  -- `set` is `set` on the bounds
  unfold PointSegmentSignal.set
  rw [PointSegmentSignal.aux_setBounds_mapTime]
  -- the bounds and flags of the interval read as reals are those read off the float one
  cases I with
  | empty =>
    simp [STLInterval.toRealInterval, STLInterval.lowerBound, STLInterval.upperBound,
      STLInterval.lowerClosed, STLInterval.upperClosed, toReal_zero]
  | nonempty l u lc rc _ _ _ => cases u <;> rfl

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
