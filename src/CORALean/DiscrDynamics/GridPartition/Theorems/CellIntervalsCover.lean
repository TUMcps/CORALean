module

public import CORALean.DiscrDynamics.GridPartition.Theorems.MemCellIntervalsIff
public import CORALean.DiscrDynamics.GridPartition.Theorems.ExistsMemCell
public import CORALean.DiscrDynamics.GridPartition.Theorems.CellSubsetIntervals

@[expose] public section

/-!
# The cells tile the state space

The boxes `cellIntervals` lists cover exactly the box the partition covers: CORA's cells are a
partition of the state space (adjacent cells share their faces).
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- The union of the cell boxes is the state space of a well-formed partition. -/
theorem GridPartition.cellIntervals_cover (P : GridPartition n) (hP : P.WellFormed) :
    P.intervals.construct = {x | ∃ B ∈ P.cellIntervals, x ∈ B.construct} := by -- --- PROOF ---
  ext x
  constructor
  · intro hx
    obtain ⟨c, h1, h2, hc⟩ := GridPartition.exists_mem_cell P hP hx
    refine ⟨P.cellInterval c, ?_, hc⟩
    rw [GridPartition.mem_cellIntervals_iff]
    exact ⟨c, by rw [List.mem_range'_1]; omega, h1, h2, rfl⟩
  · rintro ⟨B, hB, hx⟩
    obtain ⟨c, _, h1, h2, rfl⟩ := (GridPartition.mem_cellIntervals_iff _ _ _).mp hB
    exact GridPartition.cell_subset_intervals P hP h1 h2 hx

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
