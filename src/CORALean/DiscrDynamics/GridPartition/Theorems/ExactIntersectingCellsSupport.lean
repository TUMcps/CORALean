module

public import CORALean.DiscrDynamics.GridPartition.Theorems.ExactIntersectingCellsExact
public import CORALean.DiscrDynamics.GridPartition.Theorems.MemIntersectingCellsOfCellVolumePos

@[expose] public section

/-!
# A cell with a share is among the intersecting cells

A cell `s ≥ 1` with a nonzero entry in `iProp` is returned by `intersectingCellsOf`: whatever
share `exactIntersectingCells` assigns a cell, the cell meets the hull of the set.

## Inputs
* `P` – grid partition
* `X` – set
* `s` – cell number

## Hypotheses
* `hn` – dimension nonzero
* `h1` – cell number at least one
* `h2` – cell number within the cell count
* `h` – the cell has a nonzero share

## Conclusion
* the cell is among the intersecting cells
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

/-- A nonzero `iProp` entry at cell `s ≥ 1` puts `s` in `intersectingCellsOf P X`. -/
theorem GridPartition.exactIntersectingCells_support (P : GridPartition n) (X : S n)
    (hn : n ≠ 0) {s : ℕ} (h1 : 1 ≤ s) (h2 : s ≤ P.nrOfCells)
    (h : (P.exactIntersectingCells X).iProp.getD s 0 ≠ 0) : s ∈ P.intersectingCellsOf X
      := by -- --- PROOF ---
  by_cases hpos : 0 < GridPartition.volumeOf (construct X)
  · have hex := (GridPartition.exactIntersectingCells_exact P X hn hpos).2
    rw [hex] at h
    obtain ⟨t, rfl⟩ : ∃ t, s = t + 1 := ⟨s - 1, by omega⟩
    rw [List.getD_cons_succ] at h
    have ht : t < P.nrOfCells := by omega
    simp only [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range', ht,
      Option.map_some, Option.getD_some, one_mul] at h
    -- the entry is a volume share, so the volume is nonzero
    have hv : P.cellVolume (construct X) (1 + t) ≠ 0 := by
      intro h0; apply h; rw [h0, zero_div]
    have hvpos : 0 < P.cellVolume (construct X) (1 + t) :=
      lt_of_le_of_ne ENNReal.toReal_nonneg (Ne.symm hv)
    have := GridPartition.mem_intersectingCells_of_cellVolume_pos P _ hn
      (Real.IntervalOuter.interval_outer X) (c := 1 + t) (by omega) (by omega) hvpos
    simpa [Nat.add_comm, GridPartition.intersectingCellsOf] using this
  · exfalso; apply h
    -- zero volume: `iProp` is the single entry `1`, which has nothing at a cell
    unfold GridPartition.exactIntersectingCells
    rw [if_neg hpos]
    obtain ⟨t, rfl⟩ : ∃ t, s = t + 1 := ⟨s - 1, by omega⟩
    simp

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
