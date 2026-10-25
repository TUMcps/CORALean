module

public import CORALean.DiscrDynamics.GridPartition.Theorems.MemCellIntervalsIff
public import CORALean.DiscrDynamics.GridPartition.Theorems.ExistsMemCell
public import CORALean.DiscrDynamics.GridPartition.Theorems.I2sMem
public import CORALean.DiscrDynamics.GridPartition.Theorems.Basic

@[expose] public section

/-!
# The cells tile the state space

The boxes `cellIntervals` lists cover exactly the box the partition covers: CORA's cells are a
partition of the state space (adjacent cells share their faces).

## Inputs
* `P` – grid partition

## Hypotheses
* `hP` – partition well formed

## Conclusion
* the cell boxes cover exactly the state space
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- Every cell of a well-formed partition is inside its state space. -/
theorem GridPartition.aux_cell_subset_intervals (P : GridPartition n) (hP : P.IsWellFormed) {c : ℕ}
    (h1 : 1 ≤ c) (h2 : c ≤ P.nrOfCells) : -- --- CONCL ---
    (P.cellInterval c).construct ⊆ P.intervals.construct := by -- --- PROOF ---
  intro x hx
  rw [GridPartition.mem_interval_iff] at hx ⊢
  intro j
  have hs := GridPartition.i2s_mem P.nrOfSegments h2 h1 j
  have hc := hx j
  simp only [GridPartition.cellInterval] at hc
  simp only [GridPartition.intervals]
  have a := (hP j).2 0 (GridPartition.i2s P.nrOfSegments c j - 1) (by omega) (by omega)
  have b := (hP j).2 (GridPartition.i2s P.nrOfSegments c j) (P.nrOfSegments j) hs.2 le_rfl
  constructor <;> linarith [hc.1, hc.2]


-- =======================================  MAIN THEOREM  ======================================= --

/-- The union of the cell boxes is the state space of a well-formed partition. -/
theorem GridPartition.cellIntervals_cover (P : GridPartition n)
    (hP : P.IsWellFormed) : -- --- CONCL ---
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
    exact GridPartition.aux_cell_subset_intervals P hP h1 h2 hx

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
