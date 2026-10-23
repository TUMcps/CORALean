module

public import CORALean.Specification.PointSegmentSignal.Operations.AtIdx
public import CORALean.Specification.PointSegmentSignal.PointSegmentSignal
public import Mathlib.Data.List.GetD

@[expose] public section

/-!
# `PointSegmentSignal/Theorems`: small declarations

One section per declaration, at most five code lines each; alphabetical, after the
sections each one uses (CONTRIBUTING, "Small declarations").
-/


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --


namespace CORALean


-- ===================================  `List.getD_map_not`  ==================================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- Reading a negated Boolean list at an index inside it negates the entry. -/
theorem List.getD_map_not (l : List Bool) (i : ℕ) (h : i < l.length) :
    (l.map (!·)).getD i false = !(l.getD i false) := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]


-- ================================  `List.pairwise_matlabFind`  ================================ --
-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `find` returns increasing indices. -/
theorem List.pairwise_matlabFind {α : Type} (p : α → Bool) (l : List α) :
    (List.matlabFind p l).Pairwise (· < ·) :=
  (List.pairwise_lt_range').sublist (List.filter_sublist)


-- ==============================  `PointSegmentSignal.atIdx_snd`  ============================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- The index `atIdx` returns counts the time points `≤ u`. -/
theorem PointSegmentSignal.atIdx_snd {T : Type} [LinearOrder T] [Zero T] (s : PointSegmentSignal T)
    (u : T) : (s.atIdx (u : WithTop T)).2 = (s.timePoints.takeWhile (· ≤ u)).length := by
  simp [TimeOrder.isEqvTop_iff_eq, PointSegmentSignal.atIdx]


end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
