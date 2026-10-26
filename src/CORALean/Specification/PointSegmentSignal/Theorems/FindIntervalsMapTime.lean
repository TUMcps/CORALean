module

public import CORALean.Global.Float.TimeOrder
public import CORALean.Specification.PointSegmentSignal.Operations.FindIntervals
public import CORALean.Specification.STLInterval.Theorems.StlIntervalBoundsToRealInterval

@[expose] public section

/-!
# The intervals where a condition holds at a float time type, read as reals

Over a float scalar `𝕋` `findIntervals` reads its bounds off the time points by index and
builds each interval on the reals they denote, so the float intervals read as reals are those of
the signal read as reals.

## Inputs
* `s` – signal
* `cond` – condition on values

## Hypotheses
* none

## Conclusion
* the float intervals, read as reals, are those of the signal read as reals
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

/-- The bounds `findIntervalsBounds` reads off the signal read as reals are the float ones read as
reals. -/
private theorem PointSegmentSignal.aux_findIntervalsBounds_mapTime (s : PointSegmentSignal 𝕋)
    (cond : Bool → Bool) : -- --- CONCL ---
    (s.mapTime toReal).findIntervalsBounds cond = (s.findIntervalsBounds cond).map
      (fun b => (toReal b.1, b.2.1.map toReal, b.2.2.1, b.2.2.2)) := by -- --- PROOF ---
  -- the time point before and after a stored value are the float ones read as reals
  have hg : ∀ k, (s.mapTime toReal).timePoints.getD k 0 = toReal (s.timePoints.getD k 0) :=
    fun k => by
      rw [← toReal_zero_eq (𝕋 := 𝕋), List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD]
      simp only [PointSegmentSignal.mapTime, List.getElem?_map]
      cases s.timePoints[k]? <;> rfl
  have hp : ∀ i, (s.mapTime toReal).precTimeAtValIdx i =
      (toReal (s.precTimeAtValIdx i).1, (s.precTimeAtValIdx i).2) := fun i => by
    simp only [PointSegmentSignal.precTimeAtValIdx, hg]
  have hs : ∀ i, (s.mapTime toReal).succTimeAtValIdx i =
      ((s.succTimeAtValIdx i).1.map toReal, (s.succTimeAtValIdx i).2) := fun i => by
    have hl : (s.mapTime toReal).length = s.length := by
      simp [PointSegmentSignal.length, PointSegmentSignal.mapTime]
    simp only [PointSegmentSignal.succTimeAtValIdx, hg, hl]
    split_ifs <;> rfl
  have hv : (s.mapTime toReal).values = s.values := rfl
  -- the same edges, so the same intervals with mapped bounds
  unfold PointSegmentSignal.findIntervalsBounds
  simp only [hv, hp, hs]
  split_ifs <;>
    (try rcases List.matlabFind (· == (-1 : ℤ)) (List.matlabDiff (s.values.map cond)) with
      _ | ⟨f, fs⟩) <;>
    (simp [Function.comp_def, Option.toList_map, toReal_zero_eq]; try (split_ifs <;> simp))


-- =======================================  MAIN THEOREM  ======================================= --

theorem PointSegmentSignal.findIntervals_mapTime (s : PointSegmentSignal 𝕋)
    (cond : Bool → Bool) : -- --- CONCL ---
    (s.findIntervals cond).map STLInterval.toRealInterval =
      (s.mapTime toReal).findIntervals cond := by -- --- PROOF ---
  -- each interval is built from bounds read as reals
  unfold PointSegmentSignal.findIntervals
  rw [PointSegmentSignal.aux_findIntervalsBounds_mapTime, List.map_map, List.map_map]
  congr 1
  funext b
  simp only [Function.comp, STLInterval.stlIntervalBounds_toRealInterval]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
