module

public import CORALean.Specification.PointSegmentSignal.Definitions.IsValid
public import CORALean.Specification.PointSegmentSignal.Operations.At
public import CORALean.Specification.PointSegmentSignal.Operations.Basic
public import CORALean.Specification.PointSegmentSignal.Theorems.Basic
public import Mathlib.Data.List.TakeWhile

@[expose] public section

/-!
# Negation negates the value at every time

`(~obj).at(t)` is `~obj.at(t)`, for every time and every valid signal.

## Inputs
* `T` – time type
* `s` – signal
* `t` – time

## Hypotheses
* `hs` – the signal is valid

## Conclusion
* the negated signal has the negated value at the time
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =======================================  MAIN THEOREM  ======================================= --

theorem PointSegmentSignal.not_at {T : Type} [LinearOrder T] [Zero T]
    (s : PointSegmentSignal T) (hs : s.IsValid) (t : T) :
    s.not.at t = !(s.at t) := by -- --- PROOF ---
  obtain ⟨h1, h2, -⟩ := hs
  simp only [PointSegmentSignal.at, PointSegmentSignal.not]
  -- the index of the last point `≤ t` lies inside the arrays
  have hL : (s.timePoints.takeWhile (· ≤ t)).length ≤ s.timePoints.length :=
    (List.takeWhile_sublist _).length_le
  have hpos : 0 < s.timePoints.length := List.length_pos_iff.mpr h1
  split_ifs
  · rw [List.getD_map_not _ _ (by omega)]
  · rw [List.getD_map_not _ _ (by omega)]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
