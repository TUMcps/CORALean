module

public import CORALean.Specification.FourValuedSignal.Operations.Basic
public import CORALean.Specification.FourValuedSignal.Operations.ConclusiveInterval
public import CORALean.Specification.PointSegmentSignal.Theorems.AtMapTime
public import CORALean.Specification.PointSegmentSignal.Theorems.SetMapTime
public import CORALean.Specification.STLInterval.Theorems.StlIntervalBoundsToRealInterval

@[expose] public section

/-!
# The conclusive interval at a float time type, read as reals

Over a float scalar `𝕋` every step of `conclusiveInterval` (setting, negating, reading at `0`,
cutting at the first falling edge and finding the last time) is exact on the time points, so the
float interval read as reals is the conclusive interval of the signal read as reals.

## Inputs
* `obj` – signal
* `ignore` – interval ignored

## Hypotheses
* none

## Conclusion
* the float interval, read as reals, is the conclusive interval of the signal read as reals
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

/-- Cutting at the first falling edge commutes with reading the time points as reals. -/
theorem PointSegmentSignal.aux_cutAtFirstFallingEdge_mapTime (s : PointSegmentSignal 𝕋) :
    s.cutAtFirstFallingEdge.mapTime toReal = (s.mapTime toReal).cutAtFirstFallingEdge := by
  -- the edge is found on the values, which reading as reals keeps
  unfold PointSegmentSignal.cutAtFirstFallingEdge
  simp only [PointSegmentSignal.mapTime]
  split <;> (try split_ifs) <;> simp [List.map_take]

/-- The last time of a value in the signal read as reals is the float one read as a real. -/
theorem PointSegmentSignal.aux_findLast_mapTime (s : PointSegmentSignal 𝕋)
    (value : Bool) : -- --- CONCL ---
    (s.mapTime toReal).findLast value =
      ((s.findLast value).1.map toReal, (s.findLast value).2) := by -- --- PROOF ---
  -- the value is found on the values, its end read off the time points by index
  have hg : ∀ k, (s.mapTime toReal).timePoints.getD k 0 = toReal (s.timePoints.getD k 0) :=
    fun k => by
      rw [← toReal_zero_eq (𝕋 := 𝕋), List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD]
      simp only [PointSegmentSignal.mapTime, List.getElem?_map]
      cases s.timePoints[k]? <;> rfl
  have hl : (s.mapTime toReal).length = s.length := by
    simp [PointSegmentSignal.length, PointSegmentSignal.mapTime]
  unfold PointSegmentSignal.findLast
  simp only [PointSegmentSignal.mapTime] at hg hl ⊢
  split
  · simp [toReal_zero_eq]
  · simp only [PointSegmentSignal.succTimeAtValIdx, hg, hl]
    split_ifs <;> rfl


-- =======================================  MAIN THEOREM  ======================================= --

theorem FourValuedSignal.conclusiveInterval_toRealInterval (obj : FourValuedSignal 𝕋)
    (ignore : STLInterval 𝕋) : -- --- CONCL ---
    (obj.conclusiveInterval ignore).toRealInterval =
      (obj.mapTime toReal).conclusiveInterval ignore.toRealInterval := by -- --- PROOF ---
  -- the conclusive part read as reals is the one of the signal read as reals
  have hc : (obj.isInconclusive.set ignore false).not.mapTime toReal =
      ((obj.mapTime toReal).isInconclusive.set ignore.toRealInterval false).not := by
    rw [FourValuedSignal.mapTime, ← PointSegmentSignal.set_mapTime]; rfl
  have h0 := PointSegmentSignal.at_mapTime (obj.isInconclusive.set ignore false).not 0
  rw [hc, toReal_zero_eq] at h0
  unfold FourValuedSignal.conclusiveInterval
  dsimp only
  rw [h0]
  split_ifs
  · rfl
  · rw [STLInterval.stlIntervalBounds_toRealInterval, ← hc,
      ← PointSegmentSignal.aux_cutAtFirstFallingEdge_mapTime,
      PointSegmentSignal.aux_findLast_mapTime, toReal_zero_eq]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
