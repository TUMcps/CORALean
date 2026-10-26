module

public import CORALean.Global.Float.Instances.Real.Instances
public import CORALean.Global.Float.TimeOrder
public import CORALean.Specification.PointSegmentSignal.Operations.Basic

@[expose] public section

/-!
# A time point of a float signal, read as a real

The `k`-th time point of a signal with every time point read through `toReal` is the real the
float one denotes, `0` past the end.

## Inputs
* `s` – signal
* `k` – index

## Hypotheses
* none

## Conclusion
* the time point of the signal read as reals is the real the float one denotes
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

omit [ExactLe 𝕋] in
theorem PointSegmentSignal.timePoints_getD_mapTime (s : PointSegmentSignal 𝕋) (k : ℕ) :
    (s.mapTime toReal).timePoints.getD k 0 = toReal (s.timePoints.getD k 0) := by
  rw [← toReal_zero_eq (𝕋 := 𝕋), List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD]
  simp only [PointSegmentSignal.mapTime, List.getElem?_map]
  cases s.timePoints[k]? <;> rfl

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
