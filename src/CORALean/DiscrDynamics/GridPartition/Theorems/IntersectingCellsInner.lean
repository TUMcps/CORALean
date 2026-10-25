module

public import CORALean.DiscrDynamics.GridPartition.Theorems.FilterIntersectingCells
public import CORALean.DiscrDynamics.GridPartition.Theorems.MemIntersectingCellsLe
public import CORALean.DiscrDynamics.GridPartition.Theorems.Basic

@[expose] public section

/-!
# `intersectingCells` is tight up to its tolerance

CORA's `intersectingCells` is an over-approximation; this says by how much: a returned cell holds a
point within `tol` of the box `I`, so it is the tolerance of `1e-12` alone that over-approximates.

## Inputs
* `P` – grid partition
* `I` – box
* `c` – cell number

## Hypotheses
* `hP` – partition well formed
* `hI` – box nonempty
* `hn` – dimension nonzero
* `hc` – cell is returned
* `h0` – cell is not the outside

## Conclusion
* the cell holds a point within the tolerance of the box
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- A cell returned by `intersectingCells` holds a point within `tol` of the nonempty box `I`. -/
theorem GridPartition.intersectingCells_inner (P : GridPartition n) (hP : P.IsWellFormed)
    (I : Real.Interval (Vec ℝ n)) (hI : ∀ j, I.inf j ≤ I.sup j) (hn : n ≠ 0) {c : ℕ}
    (hc : c ∈ P.intersectingCells I) (h0 : c ≠ 0) : -- --- CONCL ---
    ∃ x ∈ (P.cellInterval c).construct,
      ∀ j, I.inf j - GridPartition.tol ≤ x j ∧ x j ≤ I.sup j + GridPartition.tol
        := by -- --- PROOF ---
  have hchk : c ∈ (P.intersectingCells I).filter (fun c => 0 < c ∧ c ≤ P.nrOfCells) := by
    refine List.mem_filter.mpr ⟨hc, ?_⟩
    have := GridPartition.mem_intersectingCells_le P I hc
    simp only [decide_eq_true_eq]; omega
  rw [GridPartition.filter_intersectingCells P I hn, List.mem_filter, List.mem_range'_1] at hchk
  obtain ⟨⟨h1, h2⟩, hA⟩ := hchk
  simp only [decide_eq_true_eq] at hA
  have h2' : c ≤ P.nrOfCells := by omega
  -- the point of the cell nearest to the lower end of the inflated box
  refine ⟨fun j : Fin n => max ((P.cellInterval c).inf j) (I.inf j - GridPartition.tol), ?_, ?_⟩
  · rw [GridPartition.mem_interval_iff]
    intro j
    have hm := hA j
    unfold GridPartition.aux_meetingSubscripts at hm
    simp only [List.mem_filter, decide_eq_true_eq] at hm
    have hne := GridPartition.cellInterval_nonempty P hP h1 h2' j
    exact ⟨le_max_left _ _, max_le hne hm.2.1⟩
  · intro j
    have hm := hA j
    unfold GridPartition.aux_meetingSubscripts at hm
    simp only [List.mem_filter, decide_eq_true_eq] at hm
    have ht := GridPartition.tol_pos
    have := hI j
    exact ⟨le_max_right _ _, max_le hm.2.2 (by linarith)⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
