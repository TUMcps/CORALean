module

public import CORALean.Global.Float.Instances.Real.Instances
public import CORALean.Global.Float.TimeOrder
public import CORALean.Specification.PointSegmentSignal.Operations.FindLast
public import CORALean.Specification.PointSegmentSignal.Operations.SuccTimeAtValIdx
public import CORALean.Specification.PointSegmentSignal.Theorems.TimePointsGetDMapTime

@[expose] public section

/-!
# The end of the last stretch of a float signal with a value, read as reals

`findLast` looks the last stored value up and reads the time point after it, so on the signal read
as reals it gives the real the float time point denotes, with the same flag.

## Inputs
* `s` – signal
* `value` – value to find

## Hypotheses
* none

## Conclusion
* the end on the signal read as reals is the float one, read as a real, with the same flag
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       26-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ExactLe 𝕋]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

omit [ExactLe 𝕋] in
/-- The time after a stored value is the one at the same index, read as a real. -/
private theorem aux_succTimeAtValIdx_mapTime (s : PointSegmentSignal 𝕋) (i : ℕ) : -- --- CONCL ---
    (s.mapTime toReal).succTimeAtValIdx i =
      ((s.succTimeAtValIdx i).1.map toReal, (s.succTimeAtValIdx i).2) := by -- --- PROOF ---
  -- the time point is the one at the same index, read as a real
  unfold PointSegmentSignal.succTimeAtValIdx
  have hl : (s.mapTime toReal).length = s.length := by
    simp [PointSegmentSignal.mapTime, PointSegmentSignal.length]
  rw [hl, PointSegmentSignal.timePoints_getD_mapTime]
  by_cases h : i / 2 + 1 > s.length <;> simp [h]


-- =======================================  MAIN THEOREM  ======================================= --

theorem PointSegmentSignal.findLast_mapTime (s : PointSegmentSignal 𝕋)
    (value : Bool) : -- --- CONCL ---
    (s.mapTime toReal).findLast value =
      ((s.findLast value).1.map toReal, (s.findLast value).2) := by -- --- PROOF ---
  -- the last index is found in the values, which are the same
  unfold PointSegmentSignal.findLast
  have hv : (s.mapTime toReal).values = s.values := rfl
  rw [hv]
  cases (List.matlabFind (· == value) s.values).getLast? with
  | none => simp [toReal_zero_eq]
  | some i => exact aux_succTimeAtValIdx_mapTime s i

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
