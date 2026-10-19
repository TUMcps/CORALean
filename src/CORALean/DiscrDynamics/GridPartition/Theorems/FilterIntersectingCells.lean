module

public import CORALean.DiscrDynamics.GridPartition.Operations.IntersectingCells

@[expose] public section

/-!
# The real cells of `intersectingCells`

Dropping the outside `0` from `intersectingCells` leaves the cells whose subscripts all meet
the box, in cell order: what `cellPolytopes` keeps when `exactIntersectingCells` passes the list.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- The cells of `intersectingCells P I` in `1 … N` are those whose subscripts all meet `I`. -/
theorem GridPartition.filter_intersectingCells (P : GridPartition n)
    (I : Real.Interval (Vec ℝ n)) (hn : n ≠ 0) : -- --- CONCL ---
    (P.intersectingCells I).filter (fun c => 0 < c ∧ c ≤ P.nrOfCells) =
      (List.range' 1 P.nrOfCells).filter fun c =>
        ∀ j, GridPartition.i2s P.nrOfSegments c j ∈
          P.aux_meetingSubscripts I j := by -- --- PROOF ---
  unfold GridPartition.intersectingCells
  by_cases h : n = 0 ∨ ∃ j, P.aux_meetingSubscripts I j = []
  · -- no real cell: the list is just `0`, and no cell has a subscript in the empty segment set
    rw [if_pos h]
    obtain ⟨j, hj⟩ := h.resolve_left hn
    have h0 : ([0] : List ℕ).filter (fun c => 0 < c ∧ c ≤ P.nrOfCells) = [] := by simp
    rw [h0, eq_comm, List.filter_eq_nil_iff]
    intro c _ hc
    simp only [decide_eq_true_eq] at hc
    have := hc j
    rw [hj] at this
    exact List.not_mem_nil this
  · rw [if_neg h]
    dsimp only
    -- all of `MX` are real cells, so dropping the outside leaves them whole
    have hself : ((List.range' 1 P.nrOfCells).filter fun c =>
        ∀ j, GridPartition.i2s P.nrOfSegments c j ∈ P.aux_meetingSubscripts I j).filter
        (fun c => 0 < c ∧ c ≤ P.nrOfCells) = (List.range' 1 P.nrOfCells).filter fun c =>
        ∀ j, GridPartition.i2s P.nrOfSegments c j ∈ P.aux_meetingSubscripts I j := by
      rw [List.filter_eq_self]
      intro c hc
      rw [List.mem_filter, List.mem_range'_1] at hc
      simp only [decide_eq_true_eq]; omega
    split_ifs
    · rw [List.filter_append, hself]; simp
    · exact hself

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
