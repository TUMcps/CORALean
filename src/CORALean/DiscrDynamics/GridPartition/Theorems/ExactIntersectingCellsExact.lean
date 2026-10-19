module

public import CORALean.DiscrDynamics.GridPartition.Operations.ExactIntersectingCells
public import CORALean.DiscrDynamics.GridPartition.Theorems.FilterIntersectingCells
public import CORALean.DiscrDynamics.GridPartition.Theorems.MemIntersectingCellsOfCellVolumePos

@[expose] public section

/-!
# `exactIntersectingCells` finds the cells sharing volume and their shares

CORA's claim for `exactIntersectingCells`: `iS` are the cells that intersect the set `P`, and
`iProp` the proportion of `P`'s volume in each, the outside first. For a set of positive volume `V`
this is exact: `iS` is `0` and the cells where `vol(P ∩ cell)` is positive, in order; `iProp` is the
outside share `1 - Σ`, then `vol(P ∩ cell c) / V` for each cell `c`. Cells meeting `P` only in a
null set, a face, are not listed, and the hull `intersectingCells` starts from loses none.
Not proved: that the outside share is the part of `P` beyond the state space.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet

variable {n : ℕ} {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] [Real.IntervalOuter S]


-- =======================================  MAIN THEOREM  ======================================= --

/-- For a set of positive volume, `exactIntersectingCells` is the positive-volume cells and the
volume share in each, with `1 - Σ` for the outside. -/
theorem GridPartition.exactIntersectingCells_exact (P : GridPartition n) (X : S n) (hn : n ≠ 0)
    (hpos : 0 < GridPartition.volumeOf (construct X)) : -- --- CONCL ---
    let shares := (List.range' 1 P.nrOfCells).map
      fun c => P.cellVolume (construct X) c / GridPartition.volumeOf (construct X)
    (P.exactIntersectingCells X).iS = 0 :: (List.range' 1 P.nrOfCells).filter
        (fun c => 0 < P.cellVolume (construct X) c) ∧
      (P.exactIntersectingCells X).iProp = (1 - shares.sum) :: shares := by -- --- PROOF ---
  intro shares
  -- the positive-volume cells are all among the candidates of the hull
  have hiS : ((P.intersectingCellsOf X).filter (fun c => 0 < c ∧ c ≤ P.nrOfCells)).filter
        (fun c => 0 < P.cellVolume (construct X) c) =
      (List.range' 1 P.nrOfCells).filter (fun c => 0 < P.cellVolume (construct X) c) := by
    unfold GridPartition.intersectingCellsOf
    rw [GridPartition.filter_intersectingCells P _ hn, List.filter_filter]
    apply List.filter_congr
    intro c hc
    rw [List.mem_range'_1] at hc
    -- a cell with volume is a candidate; one without is not kept either way
    by_cases hv : 0 < P.cellVolume (construct X) c
    · have hmem := P.mem_intersectingCells_of_cellVolume_pos _ hn
        (Real.IntervalOuter.interval_outer X) (by omega) (by omega) hv
      have hmem2 : c ∈ (P.intersectingCells (Real.IntervalOuter.interval X)).filter
          (fun c => 0 < c ∧ c ≤ P.nrOfCells) := by
        rw [List.mem_filter]; exact ⟨hmem, by simp; omega⟩
      rw [GridPartition.filter_intersectingCells P _ hn, List.mem_filter] at hmem2
      simp [hv, hmem2.2]
    · simp [hv]
  -- the share of a cell outside the list is `0 / V`, hence `0` as well
  have hmap : ((List.range' 1 P.nrOfCells).map fun c =>
        if c ∈ (List.range' 1 P.nrOfCells).filter (fun c => 0 < P.cellVolume (construct X) c)
        then P.cellVolume (construct X) c / GridPartition.volumeOf (construct X) else 0) =
      (List.range' 1 P.nrOfCells).map
        fun c => P.cellVolume (construct X) c / GridPartition.volumeOf (construct X) := by
    apply List.map_congr_left
    intro c _
    by_cases hv : 0 < P.cellVolume (construct X) c
    · simp [*]
    · -- a volume that is not positive is zero, so its share is
      have h0 : P.cellVolume (construct X) c = 0 :=
        le_antisymm (not_lt.mp hv) ENNReal.toReal_nonneg
      simp [h0]
  unfold GridPartition.exactIntersectingCells
  rw [if_pos hpos]
  dsimp only
  rw [hiS, hmap]
  exact ⟨rfl, rfl⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
