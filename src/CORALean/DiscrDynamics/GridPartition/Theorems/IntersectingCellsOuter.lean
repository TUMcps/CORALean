module

public import CORALean.DiscrDynamics.GridPartition.Operations.IntersectingCells
public import CORALean.DiscrDynamics.GridPartition.Theorems.Basic

@[expose] public section

/-!
# `intersectingCells` returns every cell that meets the box

CORA's claim for `intersectingCells`: it over-approximates, every cell meeting the set is
returned. A cell `c` in `1 … N` containing a point of the box `I` is in the list, whatever the
dividers; for `n = 0` CORA returns `0` and the statement is for a state space with a dimension.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- Every cell that contains a point of `I` is among `intersectingCells P I`. -/
theorem GridPartition.intersectingCells_outer (P : GridPartition n) (I : Real.Interval (Vec ℝ n))
    (hn : n ≠ 0) {c : ℕ} (h1 : 1 ≤ c) (h2 : c ≤ P.nrOfCells) {x : Vec ℝ n}
    (hxI : x ∈ I.construct) (hxc : x ∈ (P.cellInterval c).construct) :
    c ∈ P.intersectingCells I := by -- --- PROOF ---
  rw [GridPartition.mem_interval_iff] at hxI hxc
  -- each subscript of `c` is a segment meeting `[inf - tol, sup + tol]`
  have hmem : ∀ j, GridPartition.i2s P.nrOfSegments c j ∈ P.aux_meetingSubscripts I j := by
    intro j
    have hs := GridPartition.i2s_mem P.nrOfSegments h2 h1 j
    have hI := hxI j
    have hc := hxc j
    simp only [GridPartition.cellInterval] at hc
    have ht := GridPartition.tol_pos
    unfold GridPartition.aux_meetingSubscripts
    rw [List.mem_filter, List.mem_range'_1]
    refine ⟨⟨hs.1, by omega⟩, ?_⟩
    simp only [decide_eq_true_eq]
    constructor <;> linarith [hc.1, hc.2, hI.1, hI.2]
  -- so none of the early exits of `intersectingCells` applies
  have hne : ¬ (n = 0 ∨ ∃ j, P.aux_meetingSubscripts I j = []) := by
    rintro (h | ⟨j, hj⟩)
    · exact hn h
    · have := hmem j
      rw [hj] at this
      exact List.not_mem_nil this
  have hc : c ∈ (List.range' 1 P.nrOfCells).filter fun c =>
      ∀ j, GridPartition.i2s P.nrOfSegments c j ∈ P.aux_meetingSubscripts I j := by
    rw [List.mem_filter, List.mem_range'_1]
    exact ⟨⟨h1, by omega⟩, by simpa using hmem⟩
  unfold GridPartition.intersectingCells
  rw [if_neg hne]
  dsimp only
  split_ifs
  · exact List.mem_append_left _ hc
  · exact hc

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
